module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCover

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.pow_eq_one_of_mem_iSup
    (h : BorelQuotient D n H π M) {t : K}
    (ht : t ∈ ⨆ i, H i) : t ^ M = 1 := by
  rw [Subgroup.iSup_eq_closure] at ht
  refine pow_eq_one_of_mem_closure (S := ⋃ i, (H i : Set K)) ?_ ?_ ht
  · intro a ha b hb _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    exact h.extras.torus_commute i j a hi b hj
  · intro s hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hs
    exact h.torus_pow i s hi

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.parabCore [Finite K] [Finite Y]
    (h : BorelQuotient D n H π M) {q : ℕ}
    (hq4 : 4 ≤ q) (hMq : M ∣ q ^ 2 - 1) (hrank : ∀ i, RankOneNode D i q) : ParabCore Y q := by
  intro T J hNJ hJ p hp hp5
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hne : J ≠ (borel D H).map π' := by
    rw [← hNπ]
    exact hJ
  obtain ⟨hpq, hpJ⟩ := exists_perfect_dvd_of_borel_lt h.ct h.extras h.pGroup hπ'
    (fun z hz => hQ.ker_central z hz) hq4 hrank
    (fun t ht => by
      obtain ⟨k, hk⟩ := hMq
      rw [hk, pow_mul, hQ.pow_eq_one_of_mem_iSup ht, one_pow]) hp hp5 hBJ hne
  exact ⟨hpq, fun hpJ' => Or.inr (hpJ hpJ')⟩

end CFSG.AGLEmbedding.ParabPrime
