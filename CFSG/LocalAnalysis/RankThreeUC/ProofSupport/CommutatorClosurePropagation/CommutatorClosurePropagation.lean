module


public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CommutatorClosurePropagation

open CFSG.LocalAnalysis.RankThreeUC Subgroup

open scoped commutatorElement

theorem commutator_normalClosureUnder_le_of_le {G : Type} [Group G] (A C X W : Subgroup G)
    (hWA : W ≤ Subgroup.normalizer A) (hWC : W ≤ Subgroup.normalizer C)
    (hCA : C ≤ A) (hAX : ⁅A, X⁆ ≤ C) :
    ⁅A, SourceSetting.normalClosureUnder X W⁆ ≤ C := by
  have commutator_normalClosureUnder_le {G : Type} [Group G] (A C X W : Subgroup G)
      (hWA : W ≤ Subgroup.normalizer A) (hWC : W ≤ Subgroup.normalizer C)
      (hXC : X ≤ Subgroup.normalizer C) (hAX : ⁅A, X⁆ ≤ C) :
      ⁅A, SourceSetting.normalClosureUnder X W⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    have key : y ∈ Subgroup.normalizer C ∧ ∀ a ∈ A, ⁅a, y⁆ ∈ C := by
      refine Subgroup.iSup_induction (fun h : W => X.map (MulAut.conj (h : G)).toMonoidHom)
        (C := fun y => y ∈ Subgroup.normalizer C ∧ ∀ a ∈ A, ⁅a, y⁆ ∈ C) hy ?_ ?_ ?_
      · rintro ⟨w, hw⟩ y ⟨x, hx, rfl⟩
        have hwN := hWC hw
        refine ⟨?_, ?_⟩
        · exact mul_mem (mul_mem hwN (hXC hx)) (inv_mem hwN)
        · intro a ha
          have hwA : w⁻¹ * a * w ∈ A := by
            have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hWA hw)) a).1 ha
            simpa using this
          have h1 : ⁅w⁻¹ * a * w, x⁆ ∈ C := hAX (Subgroup.commutator_mem_commutator hwA hx)
          have h2 : w * ⁅w⁻¹ * a * w, x⁆ * w⁻¹ ∈ C :=
            (Subgroup.mem_normalizer_iff.1 hwN _).1 h1
          convert h2 using 1
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
      · exact ⟨one_mem _, fun a ha => by simp⟩
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨mul_mem hy1 hz1, fun a ha => ?_⟩
        have h3 : y * ⁅a, z⁆ * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hy1 _).1 (hz2 a ha)
        have : ⁅a, y * z⁆ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact mul_mem (hy2 a ha) h3
    exact key.2 a ha
  refine commutator_normalClosureUnder_le A C X W hWA hWC ?_ hAX
  have key : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    have h1 : ⁅c⁻¹, x⁆ ∈ C := hAX (Subgroup.commutator_mem_commutator (hCA (inv_mem hc)) hx)
    have : x * c * x⁻¹ = c * ⁅c⁻¹, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [this]; exact mul_mem hc h1
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x hx c, fun h => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ h
  have e : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
  rwa [e] at this

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CommutatorClosurePropagation
