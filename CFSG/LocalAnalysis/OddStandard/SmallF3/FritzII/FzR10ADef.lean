module

public import Certificates.Data.FzR10A
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G]

@[expose] def fzrAElt (a b : G) (n : ℕ) : G := a ^ (n % 8) * b ^ (n / 8 % 8)

@[expose] def FzR10AAct (a b c : G) (M : Mat) : Prop :=
  ∀ n, n < 64 → c * fzrAElt a b n * c⁻¹ = fzrAElt a b (M.ap n)

@[expose] def FzR10AMatLt (M : Mat) : Prop := M.a < 8 ∧ M.b < 8 ∧ M.c < 8 ∧ M.d < 8

structure FzR10ABasis (P : Subgroup G) (a b : G) : Prop where
  a_mem : a ∈ P
  b_mem : b ∈ P
  a8 : a ^ 8 = 1
  b8 : b ^ 8 = 1
  comm : a * b = b * a
  span : ∀ p ∈ P, ∃ n, n < 64 ∧ fzrAElt a b n = p
  inj : ∀ n m, n < 64 → m < 64 → fzrAElt a b n = fzrAElt a b m → n = m

end CFSG.OddStandard.SmallF3.FritzII
