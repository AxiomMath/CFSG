module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

theorem l239L33Overgroups : L239L33Overgroups := by
  intro G _ _ L t hmodel htL ht2 ht1 Y hYL hCY _ hY
  obtain ⟨e₀⟩ := CFSG.QuasithinUnique.Unc25K1.psl33_equiv hmodel
  let φ : ↥L ≃* L33Insp.S3 := e₀.trans CFSG.QuasithinUnique.Unc25K1.psl33EquivS3
  let t' : ↥L := ⟨t, htL⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa [sq] using ht2)
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  let Y₁ : Subgroup L33Insp.S3 := (Y.subgroupOf L).map φ.toMonoidHom
  have hY₁ : CharTwo Y₁ := by
    have ey : ↥Y ≃* ↥Y₁ := (Subgroup.subgroupOfEquivOfLe hYL).symm.trans
      (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective)
    exact charTwo_iff_internal.mpr
      (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2 ey
        (charTwo_iff_internal.mp hY))
  have ht₁2 : φ t' * φ t' = 1 := by rw [← map_mul, ht'2, map_one]
  have ht₁1 : φ t' ≠ 1 := fun h => ht'1 (φ.injective (by rw [h, map_one]))
  have hC₁ : Subgroup.centralizer ({φ t'} : Set L33Insp.S3) ≤ Y₁ := by
    intro c hc
    refine ⟨φ.symm c, ?_, by simp⟩
    have hcomm : φ.symm c * t' = t' * φ.symm c := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    apply hCY
    refine ⟨(φ.symm c).2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)
  have h := L33Insp.main_inv ht₁2 ht₁1 hC₁ hY₁
  apply le_antisymm
  · intro x hx
    refine ⟨hYL hx, ?_⟩
    have hx₁ : φ ⟨x, hYL hx⟩ ∈ Y₁ := ⟨⟨x, hYL hx⟩, hx, rfl⟩
    rw [h] at hx₁
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx₁
    have hcomm' : (⟨x, hYL hx⟩ : ↥L) * t' = t' * ⟨x, hYL hx⟩ := by
      apply φ.injective
      rw [map_mul, map_mul]
      exact hcomm
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm')
  · exact hCY

end CFSG.QuasithinUnique.Vol2Native.L239
