module

public import CFSG.Sporadic.Fi22.Classes
public import Certificates.Certificate24671

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Th CFSG.Sporadic.Fi22

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isPGroup_slvl_zero :
    IsPGroup 2 (slvl 0) := IsPGroup.of_card (n := 17) (by rw [card_slvl_zero]; norm_num)

open scoped Pointwise in
theorem exists_conj_into_slvl
    (S : Sylow 2 J) : ∃ g : J, ∀ x ∈ (S : Subgroup J), g * x * g⁻¹ ∈ slvl 0 := by
  have hidx : ¬ 2 ∣ (slvl 0).index := by rw [slvl_index]; decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S (isPGroup_slvl_zero.toSylow hidx)
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (S : Subgroup J) :=
    Subgroup.smul_mem_pointwise_smul x _ _ hx
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem card_D_inter_sylow_le
    (S : Sylow 2 J) :
    Nat.card {x : J // x ∈ D ∧ x ∈ (S : Subgroup J)} ≤ 22 :=
  Certificates.certificate24671 S

theorem card_D_slvl_le :
    Nat.card {x : J // x ∈ D ∧ x ∈ slvl 0} ≤ 22 := by
  have hidx : ¬ 2 ∣ (slvl 0).index := by rw [slvl_index]; decide
  have h := card_D_inter_sylow_le (isPGroup_slvl_zero.toSylow hidx)
  rwa [IsPGroup.toSylow_coe] at h

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
