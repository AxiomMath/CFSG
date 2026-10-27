module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LnTwoCentralizerLift
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Curtis.Coordinator

namespace LnTwoAbs

section Linear

variable {K : Type} [Field K] [Finite K]

private theorem proj_injective_of_card_eq_two (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (proj n K) := by
  refine (MonoidHom.ker_eq_bot_iff _).1 ?_
  have h := card_scalars_dvd (K := K) hn
  rw [hK] at h
  rw [ker_proj]
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)

private theorem exists_specialFactor (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n) {A : GL (Fin n) K}
    (hA : A ^ 3 = 1) :
    ∃ F : Subgroup (SpecialLinearGroup (Fin n) K),
      F ≤ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n K A) ∧
      (∀ c ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n K A), ∀ g ∈ F,
        c * g * c⁻¹ ∈ F) ∧ CFSG.IsQuasisimple F ∧ 3 ∣ Nat.card F := by
  classical
  have h2 := two_eq_zero_of_card_eq_two hK
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    have : ((3 : ℕ) : K) = 1 := by
      have : ((3 : ℕ) : K) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [this]
    exact one_ne_zero
  have hx3 : aeval (glA A : Module.End K (Fin n → K)) (X ^ 3 - C 1 : K[X]) = 0 := by
    have hX : (glA A : Module.End K (Fin n → K)) =
        Matrix.toLinAlgEquiv' (A : Matrix (Fin n) (Fin n) K) :=
      (toLinAlgEquiv'_eq_toLin' _).symm
    have hM : (A : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hA, Units.val_one]
    rw [hX]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [← map_pow, hM]
    simp
  have hsq : Squarefree (minpoly K (glA A : Module.End K (Fin n → K))) :=
    squarefree_minpoly_of_aeval_eq_zero
      (separable_X_pow_sub_C (1 : K) h3 one_ne_zero).squarefree hx3
  obtain ⟨b, hb2, hb3⟩ := exists_good_primaryFactor hK hn hsq hx3
  have hirr : Irreducible (b : K[X]) := irreducible_of_mem_primaryFactors b.2
  have hgood : IsGoodFactor A b := by
    rcases hb3 with h3' | ⟨s, hs⟩
    · exact Or.inl h3'
    · refine Or.inr ⟨hb2, ?_⟩
      have : Fact (Irreducible (b : K[X])) := ⟨hirr⟩
      have : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
      have := Fintype.ofFinite (AdjoinRoot (b : K[X]))
      have h4 : s.card ≤ Fintype.card (AdjoinRoot (b : K[X])) := Finset.card_le_univ s
      rw [Nat.card_eq_fintype_card]
      omega
  refine ⟨specialFactor A b, specialFactor_le_fixSubgroup A b,
    fun c hc g hg => conj_mem_specialFactor hc hg, isQuasisimple_specialFactor hsq b.2 hgood, ?_⟩
  obtain ⟨e⟩ := LieComp.nonempty_mulEquiv_specialFactor hsq b.2
  rw [← Nat.card_congr e.toEquiv]
  exact three_dvd_card_special_linear_adjoinRoot hK hirr hb2

end Linear

section Model

private theorem exists_mulEquiv_projectiveSL_two {Y : Type} [Group Y] {r : ℕ}
    (h : IsLieOver Y (.A r) 2 1) : Nonempty (Y ≃* projectiveSL (r + 1) (GaloisField 2 1)) := by
  obtain ⟨⟨d, hv⟩, ⟨q, hp, he, hd⟩, ⟨e⟩⟩ := h
  simp only at hd
  subst hd
  obtain ⟨p, k, hpp, hk⟩ := q
  change p = 2 at hp
  change k = 1 at he
  subst hp
  subst he
  exact ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r ⟨2, 1, hpp, hk⟩ hv)).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩

end Model

end LnTwoAbs

open LnTwoAbs in
theorem kFactLnTwoCentralizerAbs_holds : KFactLnTwoCentralizerAbs := by
  intro Z _ _ Y z r hLie hz hz3 _
  have hr : 4 ≤ r := four_le_of_isLieOver_A hLie
  obtain ⟨e⟩ := exists_mulEquiv_projectiveSL_two hLie
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 one_ne_zero
  set ρ : MulAut ↥Y := Y.normalizerMonoidHom ⟨z, hz⟩ with hρdef
  have hρ : ρ ^ 3 = 1 := by
    rw [hρdef, ← map_pow]
    have : (⟨z, hz⟩ : Subgroup.normalizer (Y : Set Z)) ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  set α : MulAut (projectiveSL (r + 1) (GaloisField 2 1)) := MulAut.congr e ρ with hαdef
  have hα : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hρ, map_one]
  obtain ⟨A, σ, hAσ⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd
    (by omega : 3 ≤ r + 1) (m := 3) ⟨1, rfl⟩ hα
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun a => ?_
    rcases eq_zero_or_eq_one_of_card_eq_two hK a with rfl | rfl
    · exact (map_zero σ).trans (map_zero (1 : GaloisField 2 1 ≃+* GaloisField 2 1)).symm
    · exact (map_one σ).trans (map_one (1 : GaloisField 2 1 ≃+* GaloisField 2 1)).symm
  rw [hσ, map_one, mul_one] at hAσ
  have hA3 : A ^ 3 = 1 := by
    have h1 : conjAut (r + 1) (GaloisField 2 1) (A ^ 3) *
        fieldAut (r + 1) (GaloisField 2 1) 1 = 1 := by
      rw [map_one, mul_one, map_pow, ← hAσ]
      exact hα
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by omega : 3 ≤ r + 1) (A ^ 3) 1 h1
    have hc1 : c = 1 := by
      refine Units.ext ?_
      rcases eq_zero_or_eq_one_of_card_eq_two hK (c : GaloisField 2 1) with h0 | h0
      · exact absurd h0 c.ne_zero
      · exact h0
    rw [← hc, hc1, map_one]
  obtain ⟨F, hFle, hFn, hFq, hF3⟩ := exists_specialFactor hK (by omega : 5 ≤ r + 1) hA3
  have hπ := proj_injective_of_card_eq_two hK (by omega : 1 ≤ r + 1)
  let ψ : SpecialLinearGroup (Fin (r + 1)) (GaloisField 2 1) →* Z :=
    Y.subtype.comp (e.symm.toMonoidHom.comp (proj (r + 1) (GaloisField 2 1)))
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp (e.symm.injective.comp hπ)
  have hψY : ∀ g, ψ g ∈ Y := fun g => (e.symm (proj (r + 1) (GaloisField 2 1) g)).2
  have hψsurj : ∀ y ∈ Y, ∃ g, ψ g = y := by
    intro y hy
    obtain ⟨g, hg⟩ := proj_surjective (r + 1) (GaloisField 2 1) (e ⟨y, hy⟩)
    refine ⟨g, ?_⟩
    show ((e.symm (proj (r + 1) (GaloisField 2 1) g) : ↥Y) : Z) = y
    rw [hg, MulEquiv.symm_apply_apply]
  have hψ : ∀ g, z * ψ g * z⁻¹ =
      ψ (CatalogueBHigherLinearAction.slConjugation (r + 1) (GaloisField 2 1) A g) := by
    intro g
    have h1 : α (proj (r + 1) (GaloisField 2 1) g) = proj (r + 1) (GaloisField 2 1)
        (CatalogueBHigherLinearAction.slConjugation (r + 1) (GaloisField 2 1) A g) := by
      rw [hAσ]
      exact conjAut_proj A g
    have h2 : e (ρ (e.symm (proj (r + 1) (GaloisField 2 1) g))) = proj (r + 1) (GaloisField 2 1)
        (CatalogueBHigherLinearAction.slConjugation (r + 1) (GaloisField 2 1) A g) := h1
    have h3 : ρ (e.symm (proj (r + 1) (GaloisField 2 1) g)) = e.symm (proj (r + 1)
        (GaloisField 2 1) (CatalogueBHigherLinearAction.slConjugation (r + 1) (GaloisField 2 1)
          A g)) := by
      rw [← h2, MulEquiv.symm_apply_apply]
    exact ((Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨z, hz⟩ _).symm).trans
      (congrArg Subtype.val h3)
  have hfix : (fixSubgroup (CatalogueBHigherLinearAction.slConjugation (r + 1)
      (GaloisField 2 1) A)).map ψ = Y ⊓ Subgroup.centralizer ({z} : Set Z) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hψY g, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h := hψ g
      rw [mem_fixSubgroup.1 hg] at h
      calc w * ψ g = (w * ψ g * w⁻¹) * w := by group
        _ = ψ g * w := by rw [h]
    · rintro ⟨hy, hyc⟩
      obtain ⟨g, rfl⟩ := hψsurj y hy
      refine ⟨g, ?_, rfl⟩
      rw [mem_fixSubgroup]
      apply hψinj
      rw [← hψ g]
      have h := Subgroup.mem_centralizer_iff.1 hyc z rfl
      calc z * ψ g * z⁻¹ = (ψ g * z) * z⁻¹ := by rw [h]
        _ = ψ g := by group
  refine ⟨F.map ψ, ?_, ?_⟩
  · rw [← hfix]
    have hle : F.map ψ ≤ (fixSubgroup (CatalogueBHigherLinearAction.slConjugation (r + 1)
        (GaloisField 2 1) A)).map ψ := Subgroup.map_mono hFle
    refine ⟨hle, CFSG.Open.IsSubnormal.step hle ?_ (CFSG.Open.IsSubnormal.refl _), ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff hle]
      rintro _ _ ⟨x, hx, rfl⟩ ⟨c, hc, rfl⟩
      exact ⟨c * x * c⁻¹, hFn c hc x hx, by simp⟩
    · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (F.equivMapOfInjective ψ hψinj) (open_isQuasisimple hFq)
  · rw [Subgroup.card_map_of_injective hψinj]
    exact hF3

end CFSG.LocalAnalysis.RankThreeTheoremC
