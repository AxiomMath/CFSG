module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S] [Finite S]

theorem even_arm_typed
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hT : EvenOuterTypedInput) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    {τ : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible τ n 2 f) (hmod : LieModel S τ n 2 f)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧
      ((∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
          LieModel (↥D ⧸ center ↥D) τ' n' 2 f' ∧
          (τ' = .PSL → n' = 4 → τ = .PSL ∧ n = 4 ∧ f = 2 * f')) ∨
        Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 6)) ∨
        LieModel (↥D ⧸ center ↥D) .PSU 3 3 1) := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exfalso
    obtain ⟨u, hu⟩ := hin
    have hκ := mulAut_conj_injective_of_simple hna
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_injective _ hκ u, hu]
      exact hσ
    have hfix : fixedSubgroup σ = centralizer ({u} : Set S) := by
      rw [← hu]
      ext x
      rw [mem_centralizer_singleton_iff]
      change u * x * u⁻¹ = x ↔ x * u = u * x
      rw [mul_inv_eq_iff_eq_mul]
      exact eq_comm
    let φ := MulEquiv.subgroupCongr hfix
    exact hEI S ⟨τ, n, f, hadm, hmod⟩ u hu2 (D.map φ.toMonoidHom)
      (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
  · refine ⟨hin, ?_⟩
    have hP : IsPComponent 2 D :=
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
    have hZD : Open.fusionZStar ↥D = center ↥D :=
      fusionZStar_eq_center_of_quasisimple hD.1 (pPrimeCore_ne_top_of_isPComponent hP)
    let e : ↥D ⧸ Open.fusionZStar ↥D ≃* ↥D ⧸ center ↥D := QuotientGroup.quotientMulEquivOfEq hZD
    rcases hT S τ n f hadm hmod σ hσ hin D hP with ⟨τ', n', f', hadm', hmod', himp⟩ | hA | hU
    · exact Or.inl ⟨τ', n', f', hadm', CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmod', himp⟩
    · obtain ⟨eA⟩ := hA
      exact Or.inr (Or.inl ⟨e.symm.trans eA⟩)
    · exact Or.inr (Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hU))

end CFSG.ComponentClassification.CatFC
