module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pRank_eq_pRank_top_subgroup (H : Subgroup G) :
    Open.pRank p H = Open.pRank p (⊤ : Subgroup H) := by
  unfold Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hEH, hE, hk⟩
    have := hE.1
    refine ⟨E.subgroupOf H, le_top, ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun x hx => Subtype.ext (hE.2 _ hx)⟩, ?_⟩
    · change ((a : H) : G) * ((b : H) : G) = ((b : H) : G) * ((a : H) : G)
      exact congrArg Subtype.val (mul_comm' (⟨(a : H), a.2⟩ : E) ⟨(b : H), b.2⟩)
    · rw [← hk]
      exact Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv
  · rintro ⟨E, -, hE, hk⟩
    refine ⟨E.map H.subtype, map_subtype_le E, isElemAbelian_map hE _, ?_⟩
    rw [card_map_of_injective H.subtype_injective, hk]

theorem pRank_le_card_of_one_lt (hp : 1 < p) (H : Subgroup G) : Open.pRank p H ≤ Nat.card G := by
  obtain ⟨E, -, -, hE⟩ := exists_pRank hp H
  have h1 : Open.pRank p H < p ^ Open.pRank p H := Nat.lt_pow_self hp
  have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  omega

end CFSG.SectionRank
