module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TightEnd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TClique

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
open scoped Pointwise

section Sylow

variable {F : Type*} [Group F] [Finite F]

theorem exists_conj_mem_sylow (T : Sylow 2 F) {y : F} (hy : IsPGroup 2 (Subgroup.zpowers y)) :
    ∃ g : F, g * y * g⁻¹ ∈ (T : Subgroup F) := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F Q T
  refine ⟨g, ?_⟩
  have h1 : y ∈ (Q : Subgroup F) := hQ (Subgroup.mem_zpowers y)
  have h2 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup F) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ h1
  rw [← Sylow.coe_subgroup_smul, hg] at h2
  simpa [MulAut.smul_def, MulAut.conj_apply] using h2

theorem exists_mem_sylow_orderOf_eight {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (T : Sylow 2 F) : ∃ y ∈ (T : Subgroup F), orderOf y = 8 := by
  obtain ⟨Qs⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨x, -, hx8⟩ := exists_orderOf_eight_of_witness hK.witness Qs
  have hxo : orderOf (x : F) = 8 := by
    rw [← Subgroup.orderOf_coe] at hx8
    exact hx8
  have h2 : IsPGroup 2 (Subgroup.zpowers (x : F)) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hxo]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow T h2
  exact ⟨g * (x : F) * g⁻¹, hg, by rw [orderOf_conj_eq, hxo]⟩

end Sylow

section Gold

variable {F : Type} [Group F] [Finite F]

theorem false_of_cliqueGrp_strongly_closed [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (hZ : CenterTrivial F)
    (IH : ClassicalCommuteBelow F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (T : Sylow 2 F) (hAT : cliqueGrp K ≤ (T : Subgroup F))
    (hsc : ∀ a ∈ cliqueGrp K, ∀ g : F,
      g * a * g⁻¹ ∈ (T : Subgroup F) → g * a * g⁻¹ ∈ cliqueGrp K) : False := by
  have hz : z ∈ cliqueGrp K := Subgroup.subset_closure (mem_cliqueInv_self hK)
  have hne : cliqueGrp K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hz
    have := hK.orderOf_eq_two
    rw [hz, orderOf_one] at this
    omega
  have hexp := GS F hnab T (cliqueGrp K) hne hAT
    (fun a ha b hb => cliqueGrp_comm hZ IH ⟨z, hK⟩ ha hb) hsc
  obtain ⟨y, hyT, hy8⟩ := exists_mem_sylow_orderOf_eight hK T
  have hdvd : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one (hexp y hyT)
  rw [hy8] at hdvd
  omega

end Gold

end CFSG.ClassicalInvolution.Hat2A7T
