module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKStarAut
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMStepZero
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveQuot
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

namespace TwelveSixKCtx

private theorem mem_xSub_iff {z : G} (hz : z ∈ H) :
    z ∈ xSub p M H ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨z, hz⟩ ∈
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  unfold xSub CFSG.AGLEmbedding.d1PlusCore
  constructor
  · rintro ⟨y, hy, hyz⟩
    have hy' : y = ⟨z, hz⟩ := Subtype.ext hyz
    subst hy'
    simpa using hy
  · intro h
    exact ⟨⟨z, hz⟩, by simpa using h, rfl⟩

private theorem starImg_V_isElemAbelian
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    IsElemAbelian 3 (starImg p H D.V) :=
  (D.cfg.elem.subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))

private theorem starImg_V_card
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    Nat.card (starImg p H D.V) = 27 := by
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hdisjV : D.V ⊓ relPPrimeCore p H = ⊥ := hc.V_inf_relPPrimeCore_eq_bot D
  have hcard1 : Nat.card (starImg p H D.V) ∣ Nat.card D.V := by
    have h := Subgroup.card_map_dvd (D.V.subgroupOf H)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    have hc' := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
    rw [starImg, ← hc']
    exact h
  have hcard2 : Nat.card D.V ∣ Nat.card (starImg p H D.V) := by
    have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_range_dvd_card_map_mul_card_starImg
      hc.ctx.p_prime hVH (MonoidHom.id ↥(D.V))
    have hmap : ((relPPrimeCore p H).subgroupOf D.V).map (MonoidHom.id ↥(D.V)) = ⊥ := by
      have hbot : (relPPrimeCore p H).subgroupOf D.V = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot]
        exact disjoint_iff.mpr (by rwa [inf_comm] at hdisjV)
      rw [hbot, Subgroup.map_bot]
    have hrange : (MonoidHom.id ↥(D.V)).range = ⊤ :=
      MonoidHom.range_eq_top.mpr Function.surjective_id
    rw [hrange, hmap] at h
    simpa using h
  rw [Nat.dvd_antisymm hcard1 hcard2, D.cfg.card]

private theorem starImg_V_le_normalizer_kStar
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    starImg p H D.V ≤
      Subgroup.normalizer (kStar p M H : Set (StarGroup p H)) := by
  have hDVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  have hnorm : D.V.subgroupOf H ≤
      Subgroup.normalizer ((kSub p M H).subgroupOf H : Set ↥H) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have haG : (a : G) ∈ H ⊓ M := hDVHM (Subgroup.mem_subgroupOf.mp ha)
    have hbG : (b : G) ∈ kSub p M H := Subgroup.mem_subgroupOf.mp hb
    have hconj := (Subgroup.mem_normalizer_iff.mp
      (inf_le_normalizer_kSub p M H haG) (b : G)).mp hbG
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hconj)
  calc starImg p H D.V
      = (D.V.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := rfl
    _ ≤ (Subgroup.normalizer ((kSub p M H).subgroupOf H : Set ↥H)).map
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := Subgroup.map_mono hnorm
    _ ≤ Subgroup.normalizer (((kSub p M H).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) :
            Set (StarGroup p H)) :=
        Subgroup.le_normalizer_map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    _ = Subgroup.normalizer (kStar p M H : Set (StarGroup p H)) := rfl

private theorem starImg_V_inf_centralizer_kStar_eq_bot
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    starImg p H D.V ⊓
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) = ⊥ := by
  have hVX : D.V ⊓ xSub p M H = ⊥ :=
    hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
      (D.centralizer_le₃ hc) (D.t₁_mem hc.data) (D.t₂_mem hc.data) (D.t₃_mem hc.data)
  refine le_bot_iff.mp ?_
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
  rcases Subgroup.mem_map.mp hxV with ⟨a, haV, rfl⟩
  have haX : (a : G) ∈ xSub p M H := (mem_xSub_iff a.2).mpr hxC
  have ha1 : (a : G) = 1 := by
    have h : (a : G) ∈ (⊥ : Subgroup G) := by
      rw [← hVX]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp haV, haX⟩
    simpa using h
  rw [show a = 1 from Subtype.ext ha1, map_one]

theorem false_of_pRank_mulAut_kStar_le_two
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(kStar p M H))) ≤ 2) : False := by
  have hElem : IsElemAbelian 3 (starImg p H D.V) := starImg_V_isElemAbelian D
  have hcard : Nat.card (starImg p H D.V) = 3 ^ 3 := by
    rw [starImg_V_card hc D]
    norm_num
  have hV3 : 3 ≤ CFSG.Open.pRank 3 (starImg p H D.V) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hElem (k := 3) hcard
  have hN := starImg_V_le_normalizer_kStar hc D
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_mulAut
    (p := 3) (by norm_num) (K := kStar p M H) (R := starImg p H D.V) hN
  have hbot := starImg_V_inf_centralizer_kStar_eq_bot hc D
  have h0 : CFSG.Open.pRank 3
      (starImg p H D.V ⊓
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H))) = 0 := by
    rw [hbot]
    exact CFSG.AGLEmbedding.pRank_bot_eq_zero Nat.prime_three
  rw [h0] at hineq
  omega

theorem nineTenOne_i
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hA : ¬ pLayerIn p H ≤ M) :
    xSub p M H ≤ M ∧ H = kSub p M H ⊔ (H ⊓ M) ∧
      ((kSub p M H).subgroupOf H).Normal := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  rcases (hc.h910 E hEQ hE hEc hΓ).1 hA with hi | ⟨-, hty, -, -, -⟩
  · exact hi
  · exact (hc.false_of_pRank_mulAut_kStar_le_two D
      (pRank_three_mulAut_le_two_of_kStarType hty)).elim

end TwelveSixKCtx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
