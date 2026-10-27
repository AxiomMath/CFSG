module

public import CFSG.GH74.E2.Ext2
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.GH74.E2.FrattiniRank
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public meta import CFSG.Open.Catalog

public section

namespace CFSG.GH74.E2.OuterRank

open CFSG.Semidihedral
@[expose] abbrev SD : Type := Model 4 (by norm_num)

instance instFintypeSD : Fintype SD := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

local instance instDecEqSD : DecidableEq SD := inferInstance

@[expose] def R0 : SD := modelR 4 (by norm_num)

@[expose] def S0 : SD := modelS 4 (by norm_num)

@[expose] def nf (a : SD) : ℕ × ℕ :=
  ((Multiplicative.toAdd a.left).val, (Multiplicative.toAdd a.right).val)

@[expose] def ap (a b x : SD) : SD := a ^ (nf x).1 * b ^ (nf x).2

@[expose] def Rel5 (a b : SD) : Prop :=
  a ^ 8 = 1 ∧ a ^ 4 ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ b * a * b⁻¹ = a ^ 3

instance instDecidableRel5 (a b : SD) : Decidable (Rel5 a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

@[expose] def Hyp3 (a b w : SD) : Prop :=
  ap a b w = w ∧ ap a b a = w * R0 * w⁻¹ ∧ ap a b b = w * S0 * w⁻¹

instance instDecidableHyp3 (a b w : SD) : Decidable (Hyp3 a b w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CFSG.GH74.E2.OuterRank

