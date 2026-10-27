module

public import CFSG.CGT.PushingUpLit.T2KR.PairStar
public import CFSG.CGT.PushingUpLit.T2K.SixD

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {g : G}

theorem _root_.CFSG.CGT.PushingUpLit.T2K.Sit64.inf_conj_eq_bot
    (hs : Sit64 G L M T n ⊥ g) {x : G} (hx : x ∉ M) :
    QOf L M ⊓ conjSubgroup x (QOf L M) = ⊥ :=
  hs.ti x (Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, one_mul, mul_one]) hx

theorem _root_.CFSG.CGT.PushingUpLit.T2K.Sit64.ti_form (hs : Sit64 G L M T n ⊥ g) (x : G) :
    QOf L M ⊓ conjSubgroup x⁻¹ (QOf L M) = ⊥ ∨
      QOf L M ⊓ conjSubgroup x⁻¹ (QOf L M) = QOf L M := by
  by_cases hx : x⁻¹ ∈ M
  · right
    have hN : x⁻¹ ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
      rw [hs.sec6.N_Q]
      exact hx
    have : conjSubgroup x⁻¹ (QOf L M) = QOf L M := map_conj_eq_of_mem_normalizer hN
    rw [this, inf_idem]
  · left
    exact hs.inf_conj_eq_bot hx

theorem _root_.CFSG.CGT.PushingUpLit.T2K.Sit64.wc_form (hs : Sit64 G L M T n ⊥ g) (x : G)
    (hx : conjSubgroup x⁻¹ (QOf L M) ≤ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G)) :
    conjSubgroup x⁻¹ (QOf L M) = QOf L M := by
  rw [hs.sec6.N_Q] at hx
  have hxM : x⁻¹ ∈ M := T2Hyp.mem_of_map_conj_le_M hs.sec6 hx
  have hN : x⁻¹ ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
    rw [hs.sec6.N_Q]
    exact hxM
  exact map_conj_eq_of_mem_normalizer hN

theorem _root_.CFSG.CGT.PushingUpLit.T2K.T2Hyp.exists_noncomm (h : T2Hyp G L M n) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  exact h.natBlock.not_isSolvable (Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a b))

theorem _root_.CFSG.CGT.PushingUpLit.T2K.Sec6.sixteen_le_card_Q
    (hE1 : FooteNonsolvableSimple) (hs : Sec6 G L M T n) :
    16 ≤ Nat.card ↥(QOf L M) := by
  set H := MData.ofSec6 hE1 hs
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n H.n_ne_zero
  have hn : 2 ≤ n := hs.sec4.hyp.two_le
  have hV : Nat.card ↥(blockU L) = (2 ^ n) ^ 2 := by rw [H.card_V, hF]
  have hle : Nat.card ↥(blockU L) ≤ Nat.card ↥(QOf L M) :=
    Subgroup.card_le_of_le H.blockU_le_QM
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith

theorem _root_.CFSG.CGT.PushingUpLit.T2K.Sec6.QOf_eq_blockU
    (hE1 : FooteNonsolvableSimple) (hs : Sec6 G L M T n)
    (htr : ∀ x ∈ QOf L M, x ≠ 1 → ∀ y ∈ QOf L M, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G), g * x * g⁻¹ = y) :
    QOf L M = blockU L := by
  set H := MData.ofSec6 hE1 hs
  refine le_antisymm (fun y hy => ?_) H.blockU_le_QM
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  obtain ⟨x, hxV, hx1⟩ : ∃ x ∈ blockU L, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hs.sec4.hyp.blockU_ne_bot (Subgroup.eq_bot_iff_forall _ |>.2 hcon)
  obtain ⟨g, hg, hgxy⟩ := htr x (H.blockU_le_QM hxV) hx1 y hy hy1
  rw [hs.N_Q] at hg
  have hgV : g ∈ Subgroup.normalizer (blockU L : Set G) := by
    rw [hs.sec4.hyp.normalizer_blockU_eq hE1]
    exact hg
  rw [← hgxy]
  exact (Subgroup.mem_normalizer_iff.1 hgV x).1 hxV

end CFSG.CGT.PushingUpLit.T2KR
