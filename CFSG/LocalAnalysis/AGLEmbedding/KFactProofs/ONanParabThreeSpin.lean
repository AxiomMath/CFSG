module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabStated
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem borelQuotient_of_spin {Q : QuadraticForm F (σ → F)} {Q₀ : (σ → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀)
    (hcen : (spinToStatedProj Q hR).ker ≤ Subgroup.center (spinGroup Q))
    (hker : (spinMatrix Q).ker = ⊥) {Y : Type} [Group Y] (e : Y ≃* StatedProj (StatedOmega Q₀))
    {M : ℕ} (hM : Nat.card F - 1 ∣ M) (hodd : Odd M)
    {D : UniversalRootDatum (spinGroup Q)} {n : Fin D.rank → spinGroup Q}
    {T : Fin D.rank → Subgroup (spinGroup Q)}
    (ct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n T)
    (extras : SteinbergExtras D n T) (pGroup : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (torus_pow : ∀ i, ∀ g ∈ T i, g ^ M = 1) :
    BorelQuotient D n T (e.symm.toMonoidHom.comp (spinToStatedProj Q hR)) M where
  ct := ct
  extras := extras
  pGroup := pGroup
  surj := e.symm.surjective.comp (spinToStatedProj_surjective Q hR)
  odd := hodd
  torus_pow := torus_pow
  ker_central := fun z hz =>
    hcen (e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz))
  ker_pow := fun z hz => by
    have h1 : z ∈ (spinToStatedProj Q hR).ker :=
      e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
    have hsc : spinMatrix Q z ∈ StatedScalars σ F :=
      Subgroup.mem_comap.1 ((ker_spinToStatedProj Q hR).le h1)
    have h2 : z ^ (Nat.card F - 1) ∈ (spinMatrix Q).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact statedScalars_pow_eq_one hsc
    rw [hker, Subgroup.mem_bot] at h2
    obtain ⟨m, rfl⟩ := hM
    rw [pow_mul, h2, one_pow]

end Generic

section Plus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem torusD_pow_eq_one (hn : 3 ≤ n) (k : Fin n) {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (torusD F hn k).range) : g ^ (Nat.card F - 1) = 1 := by
  obtain ⟨c, rfl⟩ := hg
  rw [← map_pow, unit_pow_card_sub_one, map_one]

theorem borelQuotient_spinPlus (hn : 3 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) :
    BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range)
      (e.symm.toMonoidHom.comp
        (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn))) (Nat.card F - 1) :=
  borelQuotient_of_spin (range_spinMatrix_quadPlus hn)
    (spinToStatedProj_quadPlus hn).2.2.le (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero) e
    dvd_rfl (odd_card_sub_one F) (plusDatum_isCTGroupDatum hn (plusDatum_iSup_eq_top n F hn))
    (plusDatum_steinbergExtras hn)
    (fun _ hγ => isPGroup_of_isParametrization (SpinPlus.isParametrization (K := F) hn) hγ)
    (fun k _ hg => torusD_pow_eq_one hn k hg)

omit [Finite F] [CharP F 2] in
theorem hasSL2Node_spinPlus (hn : 3 ≤ n) (i : Fin n) : HasSL2Node (plusDatum n F hn) i F := by
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
  have hpar := SpinPlus.isParametrization (K := F) hn
  have hα : (Pi.single i 1 : Fin n → ℤ) ∈ (plusDatum n F hn).roots :=
    (RootSystem.ofCartan (plusDatum n F hn).isFiniteType (plusDatum n F hn).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin n → ℤ) ∈ (plusDatum n F hn).roots :=
    (RootSystem.ofCartan (plusDatum n F hn).isFiniteType (plusDatum n F hn).divisible).neg_mem _ hα
  refine ⟨φ, hφ, fun c => ?_, fun c => ?_⟩
  · rw [hx c]
    exact ((hpar _ hα).1 _).2 ⟨c, rfl⟩
  · rw [hy c]
    exact ((hpar _ hα').1 _).2 ⟨c, rfl⟩

theorem threeDvd_spinPlus (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact (borelQuotient_spinPlus hn e).three_dvd_card
    (fun i => (hasSL2Node_spinPlus hn i).hasOrderThree) T J hNJ hJ

end Plus

theorem threeDvd_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact threeDvd_spinPlus (by omega) e T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
