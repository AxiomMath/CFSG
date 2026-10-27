module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

@[expose] def ParabStruct (Y : Type) [Group Y] : Prop :=
  ∀ (S₀ : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer (S₀ : Set Y) ≤ J →
    ∃ T : Subgroup Y, T ≤ J ∧ (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1) ∧ T ≤ Subgroup.normalizer (S₀ : Set Y) ∧
      J ≤ T ⊔ (S₀ : Subgroup Y) ⊔ perfectJoin J

section Quotient

variable {K : Type*} {Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.torus_mul_comm
    (h : BorelQuotient D n H π M) {a b : K} (ha : a ∈ ⨆ i, H i) (hb : b ∈ ⨆ i, H i) :
    a * b = b * a := by
  rw [Subgroup.iSup_eq_closure] at ha hb
  have hS : (⋃ i, (H i : Set K)).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact h.extras.torus_commute i j x hi y hj
  have hcomm : IsMulCommutative (Subgroup.closure (⋃ i, (H i : Set K))) :=
    Subgroup.isMulCommutative_closure hS
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.parabStruct [Finite K] [Finite Y]
    (h : BorelQuotient D n H π M) {q : ℕ} (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q) :
    ParabStruct Y := by
  intro S₀ J hNJ
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S₀
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
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ' hBJ
  have hUB : (posUnipotent D).map π' ≤ J :=
    (Subgroup.map_mono (posUnipotent_le_borel)).trans hBJ
  have hTB : (⨆ i, H i).map π' ≤ J := (Subgroup.map_mono (iSup_le_borel)).trans hBJ
  refine ⟨(⨆ i, H i).map π', hTB, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.torus_mul_comm ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨M, h.odd, by rw [← map_pow, hQ.pow_eq_one_of_mem_iSup ha, map_one]⟩
  · change _ ≤ Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y)
    rw [hT]
    exact (Subgroup.map_mono ((iSup_le_borel).trans
      (borel_le_normalizer_posUnipotent hQ.ct))).trans (Subgroup.le_normalizer_map π')
  · rw [hT]
    refine hJeq.le.trans (sup_le ?_ ?_)
    · calc (CFSG.LieType.Steinberg.borel D H).map π'
          = (⨆ i, H i).map π' ⊔ (posUnipotent D).map π' := by
            simp only [CFSG.LieType.Steinberg.borel, Subgroup.map_sup]
        _ ≤ _ := le_sup_left
    · refine iSup₂_le fun i hi => ?_
      have hLi : (rankOne D.rootGroup i).map π' ≤ J := by
        refine le_trans ?_ hJeq.ge
        exact le_sup_of_le_right (le_iSup₂_of_le (f := fun i
          (_ : i ∈ negIndices D (J.comap π')) => (rankOne D.rootGroup i).map π') i hi le_rfl)
      refine le_sup_right.trans' (le_perfectJoin hLi ?_)
      rw [← Subgroup.map_commutator, (hrank i).perfect hq4]

end Quotient

end CFSG.AGLEmbedding.ParabAutIrr
