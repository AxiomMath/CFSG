module

public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.DirectProd
public import CFSG.CharacterTheory.Semidihedral.Presentation
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.SD16Cert
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.Semidihedral
section Relations

variable {M : Type*} [Group M]

@[expose] def RelD (a b c d : M) : Prop :=
  d ^ 2 = 1 ∧ d * c * d⁻¹ = c⁻¹ ∧ d * a = a * d ∧ d * b = b * d

end Relations

section Certificate

variable (m : ℕ)

@[expose] def DCentralPow (c : SD16M × DihedralGroup (2 * m)) : Prop :=
  ∀ y : SD16M × DihedralGroup (2 * m), y * c ^ m = c ^ m * y

@[expose] def DSearch4 (a b c : SD16M × DihedralGroup (2 * m)) : Prop :=
  ∀ d : SD16M × DihedralGroup (2 * m), RelD a b c d → False

@[expose] def DSearch3 (t₀ a b : SD16M × DihedralGroup (2 * m)) : Prop :=
  ∀ c : SD16M × DihedralGroup (2 * m), RelB m a b c → DCentralPow m c → c ^ m ≠ t₀ →
    DSearch4 m a b c

@[expose] def DSearch2 (t₀ a : SD16M × DihedralGroup (2 * m)) : Prop :=
  ∀ b : SD16M × DihedralGroup (2 * m), RelA a b → DSearch3 m t₀ a b

@[expose] def DSearchOK (t₀ : SD16M × DihedralGroup (2 * m)) : Prop :=
  ∀ a : SD16M × DihedralGroup (2 * m), a ^ 8 = 1 → DSearch2 m t₀ a

end Certificate

end CFSG.GH74.E2
