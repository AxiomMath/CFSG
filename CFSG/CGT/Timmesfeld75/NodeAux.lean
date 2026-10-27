module

public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel H t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem suzukiModel_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel G p f) : CFSG.Blueprint.SuzukiModel H p f := by
  obtain ⟨hp, a, ha, K, hK, hfin, hf, hcard, ⟨φ⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hfin, hf, hcard, ⟨e.symm.trans φ⟩⟩

theorem lieModel_twistedB2_iff {G : Type} [Group G] {p f : ℕ} :
    CFSG.Blueprint.LieModel G .twistedB2 0 p f ↔ CFSG.Blueprint.SuzukiModel G p f :=
  CFSG.Blueprint.LieModel.twistedB2_iff.trans (and_iff_right rfl)

theorem isSporadic_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {s : TauCeti.SporadicName} (h : CFSG.Blueprint.NativeSporadic.IsSporadic G s) :
    CFSG.Blueprint.NativeSporadic.IsSporadic H s := by
  obtain ⟨φ⟩ := h
  exact ⟨e.symm.trans φ⟩

theorem ListGroup.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    ListGroup X → ListGroup Y := by
  rintro (⟨m, s, hm, hs, h⟩ | ⟨s, hs, h⟩ | ⟨s, hs, hs3, h⟩ | ⟨k, hk6, hk9, ⟨φ⟩⟩ | h | h | h)
  · exact Or.inl ⟨m, s, hm, hs, statedClassicalModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨s, hs, statedClassicalModel_of_mulEquiv e h⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨s, hs, hs3, ?_⟩))
    exact lieModel_twistedB2_iff.2 (suzukiModel_of_mulEquiv e (lieModel_twistedB2_iff.1 h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk6, hk9, ⟨e.symm.trans φ⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isSporadic_of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isSporadic_of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_mulEquiv e h))))))

theorem commute_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : Commute x y := by
  have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  exact h

theorem fusionOddCore_eq_bot_of_simple (H : Type) [Group H] [IsSimpleGroup H]
    (heven : Even (Nat.card H)) : CFSG.Open.fusionOddCore H = ⊥ := by
  refine le_antisymm (sSup_le ?_) bot_le
  rintro N ⟨hN, hodd⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h.le
  · rw [h, Subgroup.card_top] at hodd
    exact absurd heven (Nat.not_even_iff_odd.2 hodd)

theorem center_eq_bot_of_simple_nonabelian (H : Type) [Group H] [IsSimpleGroup H]
    (hnonab : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center H := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab

theorem not_zStarCase_of_simple (H : Type) [Group H] [Finite H] [IsSimpleGroup H]
    (hnonab : ∃ a b : H, a * b ≠ b * a) (heven : Even (Nat.card H)) : ¬ ZStarCase H := by
  intro hZ
  obtain ⟨a, b, hab⟩ := hnonab
  have hbot := fusionOddCore_eq_bot_of_simple H heven
  have ha : QuotientGroup.mk' (CFSG.Open.fusionOddCore H) a ∈
      Subgroup.center (H ⧸ CFSG.Open.fusionOddCore H) := by
    have h : a ∈ CFSG.Open.fusionZStar H := hZ ▸ Subgroup.mem_top a
    exact h
  have hcomm := Subgroup.mem_center_iff.1 ha (QuotientGroup.mk' (CFSG.Open.fusionOddCore H) b)
  have hq : ((b * a : H) : H ⧸ CFSG.Open.fusionOddCore H) =
      ((a * b : H) : H ⧸ CFSG.Open.fusionOddCore H) := hcomm
  have hmem := QuotientGroup.eq.1 hq
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hab hmem.symm

theorem listGroup_of_isCoveringOfList_simple (H : Type) [Group H] [Finite H] [IsSimpleGroup H]
    (hnonab : ∃ a b : H, a * b ≠ b * a) : IsCoveringOfList H → ListGroup H := by
  rintro ⟨-, Z, hZ, hnorm, hlist⟩
  have hZbot : Z = ⊥ :=
    le_bot_iff.1 (center_eq_bot_of_simple_nonabelian H hnonab ▸ hZ)
  exact ListGroup.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot) hlist

end CFSG.CGT.Timmesfeld75
