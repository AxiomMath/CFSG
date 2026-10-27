module

public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Visible

instance hmat_Qmat_normal : (Qmat.subgroupOf Hmat).Normal :=
  gmat_rhoQvis_normal

theorem hmat_Qmat_characteristic : (Qmat.subgroupOf Hmat).Characteristic := by
  change rhoQvis.Characteristic
  rw [← pCore_Gvis]
  infer_instance

theorem hmat_Qmat_isPGroup : IsPGroup 2 (Qmat.subgroupOf Hmat) :=
  IsPGroup.of_card natCard_rhoQvis

theorem hmat_quotient_isSimpleGroup : IsSimpleGroup (Hmat ⧸ Qmat.subgroupOf Hmat) :=
  VisQuot.isSimpleGroup_visQuot

theorem hmat_quotient_nonabelian : ∃ a b : Hmat ⧸ Qmat.subgroupOf Hmat, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : Hmat ⧸ Qmat.subgroupOf Hmat, a * b = b * a :=
    fun a b => not_not.1 fun hab => h ⟨a, b, hab⟩
  let _ : CommGroup (Hmat ⧸ Qmat.subgroupOf Hmat) :=
    { (inferInstance : Group (Hmat ⧸ Qmat.subgroupOf Hmat)) with mul_comm := hc }
  have : IsSimpleGroup (Hmat ⧸ Qmat.subgroupOf Hmat) := hmat_quotient_isSimpleGroup
  have hp := IsSimpleGroup.prime_card (α := Hmat ⧸ Qmat.subgroupOf Hmat)
  rw [show Nat.card (Hmat ⧸ Qmat.subgroupOf Hmat) = 4157776806543360000 from
    VisQuot.natCard_visQuot] at hp
  norm_num at hp

theorem hmat_center_quotient : Subgroup.center (Hmat ⧸ Qmat.subgroupOf Hmat) = ⊥ := by
  have : IsSimpleGroup (Hmat ⧸ Qmat.subgroupOf Hmat) := hmat_quotient_isSimpleGroup
  exact center_eq_bot_of_isSimpleGroup hmat_quotient_nonabelian

theorem native_M_visible_centralizer_schreier
    (hautH : ∀ β : MulAut Hmat, ∃ h : Hmat, β = MulAut.conj h) :
    Group.IsSolvable (Outer Hmat) ∧ (Qmat.subgroupOf Hmat).Characteristic ∧
      (∀ α : MulAut Hmat, ∃ g : Hmat, ∃ r ∈ quotKerAut (Qmat.subgroupOf Hmat),
        α = MulAut.conj g * r) ∧
      ∃ F : Subgroup (quotKerAut (Qmat.subgroupOf Hmat)), ∃ _ : F.Normal, IsPGroup 2 F ∧
        IsPGroup 3 (quotKerAut (Qmat.subgroupOf Hmat) ⧸ F) :=
  ⟨isSolvable_outer_of_inner hautH, hmat_Qmat_characteristic,
    quotKerAut_of_inner hmat_Qmat_isPGroup hmat_center_quotient hautH⟩

theorem native_M_rational_group_schreier
    (hautH : ∀ β : MulAut Hmat, ∃ h : Hmat, β = MulAut.conj h) :
    Group.IsSolvable (Outer Gmat) :=
  isSolvable_outer_of_inner (gmat_automorphisms_inner hautH)

end CFSG.ComponentClassification.BMCase
