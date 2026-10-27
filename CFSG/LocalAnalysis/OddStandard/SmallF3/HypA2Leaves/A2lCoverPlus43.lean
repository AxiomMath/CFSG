module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinPlus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpinCenter

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ComponentClassification
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem a2lCoverPlus43_holds
    (hC : HypA2.ChevOddInChev2) :
    a2lCoverOn fun S _ => LieModel S .POmegaPlus 4 3 1 := by
  intro K _ _ hq h2 hZ hm
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hF3 : Fintype.card F = 3 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF3]; decide)
  haveI := a2l_finite_spinPlus F 4
  obtain ⟨α, hαs, hle, hZα, -⟩ := a2l_cover (a2l_splits_spinPlus hk (by norm_num)) h2
    (center (spinGroup (quadPlus 4 F)))
    (e.trans (spinQuotientCenterEquivQuadPlus (by norm_num)).symm)
  obtain ⟨E, _, _, ψ, hE9, hψinj, hψneg⟩ := a2l_exists_spinPlus_sl2 hF3
  have hTU : HypA2.TypU K := a2l_typU_of_not_inChev2 hq h2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))))
    (a2l_not_inChev2_pOmegaPlus43 hC hm)
  have hψcen : ψ (a2lNegOne E) ∈ center (spinGroup (quadPlus 4 F)) :=
    a2l_mem_center_of_coe_eq_neg_one hψneg
  by_cases hα : α (ψ (a2lNegOne E)) = 1
  · have hker_le : (spinMatrix (quadPlus 4 F)).ker ≤ α.ker := by
      intro x hx
      rcases (mem_ker_spinMatrix_quadPlus_iff x).1 hx with h | h
      · rw [h]
        exact one_mem _
      · have hx' : x = ψ (a2lNegOne E) := Subtype.ext (h.trans hψneg.symm)
        rw [MonoidHom.mem_ker, hx']
        exact hα
    have hne : (spinMatrix (quadPlus 4 F)).ker ≠ ⊥ := by
      intro hbot
      have hk0 : ψ (a2lNegOne E) ∈ (spinMatrix (quadPlus 4 F)).ker :=
        (mem_ker_spinMatrix_quadPlus_iff _).2 (Or.inr hψneg)
      rw [hbot, Subgroup.mem_bot] at hk0
      exact a2lNegOne_ne_one E (a2l_ringChar_ne_two (by rw [hE9]; decide))
        (hψinj (hk0.trans (map_one ψ).symm))
    have hkα : Nat.card α.ker ≤ 2 := by
      have h1 := a2l_card_map_mul_card_ker α _ hle
      rw [← hZα] at h1
      have h2c := a2l_two_le_card_center h2 hZ
      have h4 := a2l_card_center_spinPlus_le_four F
      have hpos : 0 < Nat.card α.ker := Nat.card_pos
      by_contra hcon
      have h3 : 3 ≤ Nat.card α.ker := by omega
      have := Nat.mul_le_mul h2c h3
      omega
    obtain ⟨ω⟩ := a2l_nonempty_equiv_elementary F α hαs hker_le hkα hne
    obtain ⟨E', _, _, φ₀, hE'9, hφ₀, hz⟩ := a2l_exists_sl2_elementary_plus hF3
    exact a2l_centralDatum_of_equiv ω (by decide) (by norm_num) hE'9 φ₀ hφ₀ hz hTU
  · refine a2l_centralDatum_of_embedding (by decide) (by norm_num) hE9 (α.comp ψ)
      (a2l_injective_comp_of_ker_le_center ψ hψinj α hle hα) ?_ hTU
    rw [hZα]
    exact Subgroup.mem_map_of_mem α hψcen

end CFSG.OddStandard.SmallF3.HypA2Leaves
