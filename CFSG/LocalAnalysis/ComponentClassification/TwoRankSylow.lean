module

public import CFSG.LocalAnalysis.ComponentClassification.TwoRankTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoRankSylow

theorem invariant {G : Type*} [Group G] [Finite G] (sylow : Sylow 2 G) :
    twoRank (sylow : Subgroup G) = twoRank G := by
  apply le_antisymm (TwoRankTransport.injective (sylow : Subgroup G).subtype
    (sylow : Subgroup G).subtype_injective)
  obtain ⟨elementary, helementary, hcard⟩ := Helpers.twoRank_witness G
  have htwo : IsPGroup 2 elementary := IsPGroup.of_card hcard
  obtain ⟨containing, hcontained⟩ := htwo.exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq G containing sylow
  have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom) hcontained
  have hsubgroup := congrArg (fun chosen : Sylow 2 G => (chosen : Subgroup G)) hactor
  change (containing : Subgroup G).map (MulAut.conj actor).toMonoidHom = sylow at hsubgroup
  rw [hsubgroup] at hmap
  let image := elementary.map (MulAut.conj actor).toMonoidHom
  have helementaryImage : IsElemAbelian 2 image :=
    TwoRankTransport.elementary_map (MulAut.conj actor).toMonoidHom elementary helementary
  have himageRank : twoRank G ≤ pRank 2 image := by
    apply TwoRankTransport.rank_le image image le_rfl helementaryImage
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]
    exact hcard
  rw [TwoRankTransport.subgroup]
  exact himageRank.trans (TwoRankTransport.mono hmap)

theorem positive {G : Type*} [Group G] [Finite G] (heven : Even (Nat.card G)) : 1 ≤ twoRank G := by
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.mp heven)
  let cyclic := Subgroup.zpowers member
  have helementary : IsElemAbelian 2 cyclic := by
    constructor
    · infer_instance
    · intro element hmem
      obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hsquare : member ^ 2 = 1 := by rw [← horder]; exact pow_orderOf_eq_one member
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hsquare, one_zpow]
  apply TwoRankTransport.rank_le (⊤ : Subgroup G) cyclic le_top helementary
  rw [Nat.card_zpowers, horder]
  rfl

end CFSG.ComponentClassification.TwoRankSylow
