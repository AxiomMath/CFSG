module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Wreath
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCase
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem le_of_twentySeven_le_card (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {H Y : Subgroup G}
    (hH : IsTwoLocal H) (hYH : Y ≤ H) (hYM : Y ≤ M) (hY3 : IsPGroup 3 Y)
    (hY : 27 ≤ Nat.card Y) : H ≤ M := by
  have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  obtain ⟨m, hm⟩ :=
    pGroup_conjugate_into_sylow_within_overgroup 3 Nat.prime_three P M hPM Y hY3 hYM
  set φ := (MulAut.conj (m : G)).toMonoidHom
  have hY' : 27 ≤ Nat.card (Y.map φ) := by
    rwa [card_map_of_injective (MulAut.conj (m : G)).injective]
  obtain ⟨R, hRY, hR3, hRnc, hΓ⟩ :=
    exists_noncyclic_le_of_twentySeven_le_card hS hU0 hsit e hm hY'
  have hH' : IsTwoLocal (H.map φ) := twoLocal_map_automorphism H hH (MulAut.conj (m : G))
  refine (conjugate_subgroup_le_iff_of_conjugator_mem H M (m : G) m.2).1 ?_
  exact hD2 M hsit.isCoreMaxLocal.1 (fun p' hp' P' hM' => hU0 p' hp' P' M hM')
    (fun h3 P₃ hM₃ => ⟨fun Q hQP hQne hQ3 => normalizer_le_of_three_le_pRank_sup_centralizer hS
      hU0 h3 hM₃ hsit.largeObstruction_empty hQP hQne hQ3, fun h => absurd hsolv h⟩)
    3 hsit.mem_sigmaA P hsit.isCoreMaxLocal (H.map φ) R hH' (hRY.trans (map_mono hYH))
    (hRY.trans (hm.trans hPM)) hR3 hRnc hΓ

private theorem reduce614_twentySeven_le_card {B Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : B < Q) (hB : Nat.card B = 9) : 27 ≤ Nat.card Q := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hlt := card_lt_of_lt hBQ
  rw [hB, hn] at hlt
  rw [hn]
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num at hlt
  · calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h

private theorem reduce614_exists_sylow_le {B H : Subgroup G} (hB3 : IsPGroup 3 B) (hBH : B ≤ H)
    {k : ℕ} (hk : 3 ^ k ∣ Nat.card H) :
    ∃ Q : Subgroup G, B ≤ Q ∧ Q ≤ H ∧ IsPGroup 3 Q ∧ 3 ^ k ∣ Nat.card Q := by
  have hB3' : IsPGroup 3 (B.subgroupOf H) := hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  refine ⟨(Q' : Subgroup H).map H.subtype, ?_, map_subtype_le _, Q'.isPGroup'.map H.subtype, ?_⟩
  · intro b hb
    exact ⟨⟨b, hBH hb⟩, hQ' (mem_subgroupOf.mpr hb), rfl⟩
  · rw [card_map_of_injective H.subtype_injective]
    exact Q'.pow_dvd_card_of_pow_dvd_card hk

theorem le_of_three_dvd_relIndex (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M) (e : (P : Subgroup G) ≃* W₃) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H : Subgroup G}
    (hH : IsTwoLocal H) (hBH : zpowers x ⊔ zpowers z ≤ H)
    (h3 : 3 ∣ (zpowers x ⊔ zpowers z).relIndex H) : H ≤ M := by
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hBP : B ≤ P := hB.isIsolatedPlane.1
  have hBc : Nat.card B = 9 := hB.card_eq.trans (by norm_num)
  have hB3 : IsPGroup 3 B := P.isPGroup'.to_le hBP
  have hHc : 3 ^ 3 ∣ Nat.card H := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := H)
    rw [inf_eq_left.mpr hBH, hBc] at h
    obtain ⟨k, hk⟩ := h3
    exact ⟨k, by rw [← h, hk]; ring⟩
  obtain ⟨Q, hBQ, hQH, hQ3, hQc⟩ := reduce614_exists_sylow_le hB3 hBH hHc
  have hBQ' : B < Q := lt_of_le_of_ne hBQ fun h => by
    have := Nat.le_of_dvd Nat.card_pos hQc
    rw [← h, hBc] at this
    omega
  have hBN := pGroup_proper_subgroup_lt_internal_normalizer 3 Nat.prime_three Q B hQ3 hBQ'
  exact le_of_twentySeven_le_card hS hU0 hD2 hsit hsolv e hH (inf_le_left.trans hQH)
    (inf_le_right.trans (normalizer_plane_le hS hU0 hsit hx hz)) (hQ3.to_le inf_le_left)
    (reduce614_twentySeven_le_card (hQ3.to_le inf_le_left) hBN hBc)

theorem prop614_of_sylow (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h627 : GL83SmallRankProp627 G) (h632 : GL83SmallRankProp632 G)
    (h : GL83SmallRankProp614Sylow G) : GL83SmallRankProp614 G := by
  intro p P M hsit x z hx hz H hH hBH hS'
  obtain rfl := GL83SmallRankProp627.eq_three h627 hsit
  obtain ⟨hsolv, ⟨e⟩⟩ := h632 P M hsit
  by_cases h3 : 3 ∣ (zpowers x ⊔ zpowers z).relIndex H
  · exact le_of_three_dvd_relIndex hS hU0 hD2 hsit hsolv e hx hz hH hBH h3
  · exact h P M hsit hsolv ⟨e⟩ x z hx hz H hH hBH h3 hS'

end CFSG.LocalAnalysis.RankThreeTheoremC
