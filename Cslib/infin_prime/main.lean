import Mathlib.Computability.Language
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Computability.DFA
import Mathlib.Data.ZMod.Basic
import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Data.Set.Basic

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

def count_alphabet (d : α₂) (x : List α₂) : Nat:= x.count d

def ξ (x : List α₂) : Int := (count_alphabet .a x : Int) - (count_alphabet .b x : Int)

theorem ξ_add (u v : List α₂) : ξ (u ++ v) = ξ (u) + ξ (v):=
  by sorry

def Lₙ (n : ℕ+) : Language α₂:= {x : List α₂ | (n : ℤ ) ∣ ξ x }

def IsRegularL_n (n : ℕ+) : Prop := Language.IsRegular (Lₙ n)

def dfa_Ln (n : ℕ+) : DFA α₂ (ZMod n) where
  step q α:= match α with
  | .a => q+1
  | .b => q-1
  start := 0
  accept := {0}

def L : Language α₂ := {x | ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ ξ x }
