import Mathlib.Computability.Language
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Computability.DFA
import Mathlib.Data.ZMod.Basic
import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Cslib.Computability.Languages.MyhillNerode

open Language DFA

inductive α₂ where
| a
| b
deriving Repr, DecidableEq, Fintype

open α₂

def empty_word : List α₂ := []

--redundant
def word_length (x : List α₂) : Nat :=
  match x with
  | [] => 0
  | x => x.length

@[simp]
def count_alphabet (d : α₂) (x : List α₂) : Nat:= x.count d

@[simp]
def ξ (x : List α₂) : Int := (count_alphabet .a x : Int) - (count_alphabet .b x : Int)

private lemma ξ_helper (u : List α₂) : ξ (u ++ []) = ξ u := by grind --reduntacticdant

theorem ξ_add (u v : List α₂) : ξ (u ++ v) = ξ (u) + ξ (v):= by
  unfold ξ count_alphabet --only restricts the lemmas that simp can use (tactic modifier)
  simp only [List.count_append] --just breakdown definitions and apply simp lol
  omega --does arithmetic and solves basic equations

def Lₙ (n : ℕ+) : Language α₂:= {x : List α₂ | (n : ℤ ) ∣ ξ x }

def IsRegularL_n (n : ℕ+) : Prop := Language.IsRegular (Lₙ n)

def dfa_Ln (n : ℕ+) : DFA α₂ (ZMod n) where
  step q α:= match α with
  | .a => q+1
  | .b => q-1
  start := 0
  accept := {0}

private lemma eval_from (q : ZMod (n : ℕ+)) (w : List α₂) :
  (dfa_Ln n).evalFrom q w = q + (ξ w : ZMod n):= by
    induction w generalizing q with
    | nil => simp
    | cons α w ih =>
        change (dfa_Ln n).evalFrom ((dfa_Ln n).step q α) w = _--used ai for this one as it was weird
        rw [ih]
        cases α <;> simp [dfa_Ln, ξ] <;> ring

private lemma dfa_eval (w : List α₂) : eval (dfa_Ln n) w = (ξ w : ZMod n):= by
  unfold eval
  rw [eval_from]
  simp [dfa_Ln]

lemma hmeow(n : ℕ+) : Lₙ n = (dfa_Ln n).accepts := by
  ext w
  unfold accepts
  sorry

  -- constructor <;> intro h


theorem Lₙ_is_regular (n : ℕ+) : (Lₙ n).IsRegular := by
  use ZMod n, inferInstance
  use dfa_Ln n
  exact (hmeow n).symm

def L : Language α₂ := {x | ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ ξ x }

theorem ξ_ne_one : w ∈ L → ξ w ≠ 1 ∧ ξ w ≠ - 1:= by
  intro h
  rcases h with ⟨p, prime, div⟩
  unfold Nat.Prime at prime
  constructor <;> intro contra <;> rw [contra] at div
  · have hp_div_1 : p ∣ 1 := by exact_mod_cast div --used ai for these steps, there was some
    have hp_eq_1 : p = 1 := Nat.dvd_one.mp hp_div_1 --coercion issue so had to convert Z into N
    rw [hp_eq_1] at prime -- first and then say that p has to be 1
    exact not_irreducible_one prime
  · have div_one : (p : ℤ) ∣ 1 := dvd_neg.mp div -- here we gotta prove that if a number divides -1
    have hp_div_1 : p ∣ 1 := by exact_mod_cast div_one -- it divides 1
    have hp_eq_1 : p = 1 := Nat.dvd_one.mp hp_div_1
    rw [hp_eq_1] at prime
    exact not_irreducible_one prime

def meow (i j : Nat) := i > j

-- we'll define powers of a by lists of a right

theorem L_isNotRegular (h:meow i j): ¬L.IsRegular:= by
  intro contra
  sorry
