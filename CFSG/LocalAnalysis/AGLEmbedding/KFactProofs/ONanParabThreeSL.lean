module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem

section SL

variable {m : ℕ} {F : Type} [Field F]

theorem torus_gen_pow [Finite F] (k : Fin m) {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (t : Fˣ) (ht : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (Function.update (Function.update 1 k.castSucc (t : F)) k.succ
        ((t⁻¹ : Fˣ) : F))) : h ^ (Nat.card F - 1) = 1 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ht, Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.pow_apply]
  refine FiniteField.pow_card_sub_one_eq_one _ ?_
  by_cases h1 : i = k.succ
  · subst h1
    simp
  · by_cases h2 : i = k.castSucc
    · subst h2
      simp [Function.update_of_ne (Fin.castSucc_lt_succ).ne]
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

theorem torus_pow_eq_one [Finite F] (k : Fin m) {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ torus m F k) : g ^ (Nat.card F - 1) = 1 := by
  refine pow_eq_one_of_mem_closure ?_ ?_ hg
  · rintro _ ⟨t, ht⟩ _ ⟨t', ht'⟩ _
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht, ht',
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rintro _ ⟨t, ht⟩
    exact torus_gen_pow k t ht

theorem center_pow_eq_one [Finite F] {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    z ^ (Nat.card F - 1) = 1 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  obtain ⟨c, hc, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hcz, ← map_pow,
    FiniteField.pow_card_sub_one_eq_one c hc0, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem borelQuotient_sl [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) :
    BorelQuotient (rootDatum m F) (weylRep m F) (torus m F)
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center _))) (Nat.card F - 1) where
  ct := isCTGroupDatum m F
  extras := steinbergExtras m F
  pGroup := fun γ hγ => isPGroup_of_isParametrization SL.isParametrization hγ
  surj := e.surjective.comp (QuotientGroup.mk'_surjective _)
  odd := odd_card_sub_one F
  torus_pow := fun k g hg => torus_pow_eq_one k hg
  ker_central := fun z hz => by
    rw [MonoidHom.mem_ker] at hz
    exact (QuotientGroup.eq_one_iff z).1 (e.injective (by simpa using hz))
  ker_pow := fun z hz => by
    rw [MonoidHom.mem_ker] at hz
    exact center_pow_eq_one ((QuotientGroup.eq_one_iff z).1 (e.injective (by simpa using hz)))

theorem hasSL2Node_sl (i : Fin m) : HasSL2Node (rootDatum m F) i F := by
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  have hpar := SL.isParametrization (m := m) (F := F)
  have hα : (Pi.single i 1 : Fin m → ℤ) ∈ (rootDatum m F).roots :=
    (RootSystem.ofCartan (rootDatum m F).isFiniteType (rootDatum m F).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin m → ℤ) ∈ (rootDatum m F).roots :=
    (RootSystem.ofCartan (rootDatum m F).isFiniteType (rootDatum m F).divisible).neg_mem _ hα
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact ((hpar _ hα).1 _).2 ⟨c, rfl⟩
  · rw [hy c]
    exact ((hpar _ hα').1 _).2 ⟨c, rfl⟩

theorem threeDvd_sl_psl [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J :=
  (borelQuotient_sl e).three_dvd_card (fun i => (hasSL2Node_sl i).hasOrderThree) T J hNJ hJ

end SL

theorem threeDvd_sl {Y : Type} [Group Y] [Finite Y] (r : ℕ) (q : TauCeti.PrimePower)
    (hq : q.p = 2) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  exact threeDvd_sl_psl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
    e.symm) T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
