module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltArm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FixedComponentTypes (S : Type) [Group S] (σ : MulAut S)
    (D : Subgroup ↥(fixedSubgroup σ)) : Prop :=
  (∃ n k : ℕ, n ≠ 6 ∧ 5 ≤ k ∧ k + 2 ≤ n ∧ Even (n - k) ∧
      Nonempty (S ≃* alternatingGroup (Fin n)) ∧
      Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin k))) ∨
    (OddLieType S ∧ (OddLieType (↥D ⧸ center ↥D) ∨ LieModel ↥D .PSL 2 2 3)) ∨
    (EvenLieType S ∧ σ ∉ (MulAut.conj : S →* MulAut S).range ∧
      (EvenLieType (↥D ⧸ center ↥D) ∨ Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 6)) ∨
        LieModel (↥D ⧸ center ↥D) .PSU 3 3 1)) ∨
    SporadicRep S

theorem oddLieType_of_alternating_six {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) : OddLieType X := by
  have hm :=
    CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six X h
  exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
    ⟨Nat.prime_three, by norm_num, le_rfl, by decide, by decide⟩, Or.inl ⟨by decide, hm⟩⟩

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem odd_arm (hGLS : GLS3OddLieAutComponentsInput) (hodd : OddLieType S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) :
    OddLieType (↥D ⧸ center ↥D) ∨ LieModel ↥D .PSL 2 2 3 := by
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hmod σ hσ D hD with
    ⟨τ', n', f', hadm', hmod'⟩ | ⟨-, -, -, hL⟩
  · exact Or.inl ⟨τ', n', p, f', hp, hp2, hadm', hmod'⟩
  · exact Or.inr hL

theorem even_arm
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧
      (EvenLieType (↥D ⧸ center ↥D) ∨ Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 6)) ∨
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
    exact hEI S heven u hu2 (D.map φ.toMonoidHom) (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
  · refine ⟨hin, ?_⟩
    have hP : IsPComponent 2 D :=
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
    have hZD : Open.fusionZStar ↥D = center ↥D :=
      fusionZStar_eq_center_of_quasisimple hD.1 (pPrimeCore_ne_top_of_isPComponent hP)
    let e : ↥D ⧸ Open.fusionZStar ↥D ≃* ↥D ⧸ center ↥D := QuotientGroup.quotientMulEquivOfEq hZD
    obtain ⟨τ, n, f, hadm, hmod⟩ := heven
    rcases hEO S τ n f hadm hmod σ hσ hin D hP with
      ⟨τ', n', f', hadm', hmod'⟩ | hA | hU
    · exact Or.inl ⟨τ', n', f', hadm', CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmod'⟩
    · obtain ⟨eA⟩ := hA
      exact Or.inr (Or.inl ⟨e.symm.trans eA⟩)
    · exact Or.inr (Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hU))

theorem catalog_fixed_component
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) : FixedComponentTypes S σ D := by
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | hsp
  · by_cases hn6 : n = 6
    · subst hn6
      have hodd : OddLieType S := oddLieType_of_alternating_six ⟨θ⟩
      exact Or.inr (Or.inl ⟨hodd, odd_arm hGLS hodd hσ hD⟩)
    · obtain ⟨k, hk5, hkn, hpar, hDk⟩ := alt_arm hn hn6 θ hσ hD
      exact Or.inl ⟨n, k, hn6, hk5, hkn, hpar, ⟨θ⟩, hDk⟩
  · exact Or.inr (Or.inl ⟨hodd, odd_arm hGLS hodd hσ hD⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨heven, even_arm hEI hEO hna heven hσ hD⟩))
  · exact Or.inr (Or.inr (Or.inr hsp))

end CFSG.ComponentClassification.CatFC
