module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOReach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L3Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONRank

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def SporadicOrderEight (s : TauCeti.SporadicName) : Prop :=
  ∃ g : Carrier s, orderOf g = 8

@[expose] def ONOddCenter : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .ONan →
    Odd (Nat.card (center X))

@[expose] def HeCoverRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .He →
    3 ≤ CFSG.pRank 2 X

theorem exists_orderOf_eight_of_cover {s : TauCeti.SporadicName} (h8 : SporadicOrderEight s)
    {L : Type} [Group L] [Finite L] (hodd : Odd (Nat.card (center L)))
    (hL : IsSporadic (L ⧸ center L) s) : ∃ y : L, orderOf y = 8 := by
  obtain ⟨g, hg⟩ := h8
  obtain ⟨e⟩ := hL
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm g)
  have h8x : orderOf (QuotientGroup.mk x : L ⧸ center L) = 8 := by
    rw [hx, MulEquiv.orderOf_eq, hg]
  have hdvd : 8 ∣ orderOf x := h8x ▸ orderOf_map_dvd (QuotientGroup.mk' (center L)) x
  obtain ⟨d, hd⟩ := hdvd
  have hxc : x ^ 8 ∈ center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← h8x, pow_orderOf_eq_one]
  have hpos : 0 < orderOf x := orderOf_pos x
  have hd0 : d ≠ 0 := by
    rintro rfl
    omega
  have hord : orderOf (x ^ 8) = d := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨d, hd⟩, hd, Nat.mul_div_cancel_left _ (by norm_num)]
  have hdodd : Odd d := by
    have h1 : orderOf (⟨x ^ 8, hxc⟩ : ↥(center L)) = d := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    exact hodd.of_dvd_nat (h1 ▸ orderOf_dvd_natCard _)
  refine ⟨x ^ d, ?_⟩
  rw [orderOf_pow_of_dvd hd0 ⟨8, by rw [hd, mul_comm]⟩, hd,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]

theorem false_of_cover_in_psl_three {s : TauCeti.SporadicName} (h8 : SporadicOrderEight s)
    {Y : Type} [Group Y] [Finite Y] {N L : Subgroup Y} {n : ℕ} (hn : 1 ≤ n)
    (hN : LieModel ↥N .PSL 3 2 n) (hLN : L ≤ N) (hL : OddCover s L) : False := by
  obtain ⟨y, hy⟩ := exists_orderOf_eight_of_cover h8 hL.2.1 hL.2.2
  have h1 : orderOf (⟨(y : Y), hLN y.2⟩ : ↥N) = 8 :=
    calc orderOf (⟨(y : Y), hLN y.2⟩ : ↥N) = orderOf ((⟨(y : Y), hLN y.2⟩ : ↥N) : Y) :=
          (Subgroup.orderOf_coe _).symm
      _ = orderOf ((y : ↥L) : Y) := rfl
      _ = orderOf y := Subgroup.orderOf_coe _
      _ = 8 := hy
  exact lieModel_psl_three_no_order_eight hn hN _ h1

theorem two_mul_le_card_of_cover {s : TauCeti.SporadicName} {m : ℕ}
    (hcard : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = m)
    {Y : Type} [Group Y] [Finite Y] {N L : Subgroup Y} (hLN : L ≤ N) (hne : L ≠ N)
    (hL : OddCover s L) : 2 * m ≤ Nat.card ↥N := by
  have hmL : m ∣ Nat.card ↥L := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
    rw [hcard _ hL.2.2] at h
    exact ⟨Nat.card ↥(center ↥L), by rw [h, mul_comm]⟩
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hm : m ≤ Nat.card ↥L := Nat.le_of_dvd hLpos hmL
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLN
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hLN (by rw [hk, mul_one]))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card ↥N := Nat.card_pos
    omega
  have hk2 : 2 ≤ k := by omega
  calc 2 * m ≤ 2 * Nat.card ↥L := Nat.mul_le_mul_left 2 hm
    _ ≤ k * Nat.card ↥L := Nat.mul_le_mul_right _ hk2
    _ = Nat.card ↥N := by rw [hk, mul_comm]

theorem so_hty {X : Type} [Group X] (hR : SOR X) (hnON : ¬ IsSporadic X .ONan) :
    (∃ n : ℕ, 2 ≤ n ∧ LieModel X .PSL 3 2 n) ∨ IsSporadic X .Suz ∨ IsSporadic X .He := by
  rcases hR with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hnON


theorem so_notR {s : TauCeti.SporadicName} {m : ℕ}
    (hcard : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = m)
    (hm : 460815505920 < 2 * m) (h8 : SporadicOrderEight s) {Y : Type} [Group Y] [Finite Y]
    {N : Subgroup Y} (hN : FStarSimple N) (hidx : N.index ≤ 2) {L : Subgroup Y} (hLL : InL L)
    (hcov : OddCover s L) : ¬ SOR ↥N := by
  intro hR
  have : N.Normal := hN.normal
  have hLN : L ≤ N := le_of_perfect_of_index_le_two hidx hcov.1.1
  have hne : L ≠ N := inL_ne_of_fStarSimple hN hLL
  have h2 := two_mul_le_card_of_cover hcard hLN hne hcov
  rcases hR with ⟨n, hn, hNn⟩ | hS | hH | hO
  · exact false_of_cover_in_psl_three h8 (by omega) hNn hLN hcov
  · have := suz_card_pinned _ hS
    omega
  · have := (he_pinned _ hH).2
    omega
  · have := on_card_pinned _ hO
    omega

theorem so_rank (hon : ONOddCenter) (hHe : HeCoverRank)
    (hsuz : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      IsSporadic (X ⧸ center X) .Suz → 3 ≤ CFSG.pRank 2 X) :
    ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → SOR (X ⧸ center X) →
      3 ≤ CFSG.pRank 2 X := by
  intro X _ _ hq h
  rcases h with ⟨n, hn, hX⟩ | hS | hH | hO
  · exact three_le_pRank_of_quotient_L3 hn hX
  · exact hsuz X hq hS
  · exact hHe X hq hH
  · exact on_pRank_L X ⟨.ONan, List.mem_singleton_self _, hq, hon X hq hO, hO⟩

theorem upFacts_on (hon : ONOddCenter) : UpFacts [.ONan] where
  fi23 s hs := by
    rcases List.mem_singleton.1 hs with rfl
    exact on_fi23
  not_exc s hs := by
    rcases List.mem_singleton.1 hs with rfl
    exact on_sp_not_exc
  odd s hs X _ _ hq hX := by
    rcases List.mem_singleton.1 hs with rfl
    exact hon X hq hX
  rank s hs X _ _ hq hX := by
    rcases List.mem_singleton.1 hs with rfl
    exact on_pRank_L X ⟨.ONan, List.mem_singleton_self _, hq, hon X hq hX, hX⟩

end CFSG.EvenSporadicStandard.Induction
