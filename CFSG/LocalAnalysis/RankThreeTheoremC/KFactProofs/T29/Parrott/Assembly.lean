module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Split

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.LocalAnalysis.RankThreeTheoremC (IsLinThreeCover3)

@[expose] def IsRankOneIndex : LieTypeIndex → Prop
  | .A r q => r = 1 ∨ (r = 2 ∧ q.card % 3 = 2)
  | .twistedA r q => r = 2 ∧ q.card % 3 = 1
  | _ => False

@[expose] def IsRankFourIndex : LieTypeIndex → Prop
  | .A r q => (4 ≤ r ∧ q.card % 3 = 1) ∨ (7 ≤ r ∧ q.card % 3 = 2)
  | .twistedA r q => (4 ≤ r ∧ q.card % 3 = 2) ∨ (7 ≤ r ∧ q.card % 3 = 1)
  | .B r _ => 4 ≤ r
  | .C r _ => 4 ≤ r
  | .D _ _ => True
  | .twistedD r _ => 5 ≤ r
  | _ => False

theorem card_mod_three_ne_zero {q : PrimePower} (hp3 : q.p ≠ 3) : q.card % 3 ≠ 0 := by
  intro h
  rw [PrimePower.card_def] at h
  exact not_three_dvd_prime_pow q.prime_p hp3 (Nat.dvd_of_mod_eq_zero h)

theorem isOpenIndex_cases (d : ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hL3 : ¬ IsLinThreeCover3 d) (hd : IsOpenIndex d.1) :
    IsRankOneIndex d.1 ∨ IsRankTwoIndex d.1 ∨ IsRankThreeIndex d.1 ∨ IsRankFourIndex d.1 := by
  obtain ⟨dd, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    have hq := card_mod_three_ne_zero hp3
    have hq2 : 2 ≤ q.card := q.isPrimePow_card.two_le
    have hr1 : 1 ≤ r := hr.1
    have hne : ¬ (r = 2 ∧ q.card % 3 = 1) := by
      rintro ⟨rfl, h2⟩
      exact hL3 (Or.inl ⟨q, rfl, by omega⟩)
    simp only [IsRankOneIndex, IsRankTwoIndex, IsRankThreeIndex, IsRankFourIndex]
    omega
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedA] using hch
    have hq := card_mod_three_ne_zero hp3
    have hr2 : 2 ≤ r := hr.1
    have hne : ¬ (r = 2 ∧ q.card % 3 = 2) := by
      rintro ⟨rfl, h2⟩
      exact hL3 (Or.inr ⟨q, rfl, by omega⟩)
    simp only [IsRankOneIndex, IsRankTwoIndex, IsRankThreeIndex, IsRankFourIndex]
    omega
  | B r q =>
    have hr2 : 2 ≤ r := hr.1
    simp only [IsRankOneIndex, IsRankTwoIndex, IsRankThreeIndex, IsRankFourIndex]
    omega
  | C r q =>
    have hr3 : 3 ≤ r := hr.1
    simp only [IsRankOneIndex, IsRankTwoIndex, IsRankThreeIndex, IsRankFourIndex]
    omega
  | D r q => exact Or.inr (Or.inr (Or.inr trivial))
  | twistedD r q =>
    have hr4 : 4 ≤ r := hr
    simp only [IsRankOneIndex, IsRankTwoIndex, IsRankThreeIndex, IsRankFourIndex]
    omega
  | G2 q => exact Or.inr (Or.inl trivial)
  | trialityD4 q => exact Or.inr (Or.inl trivial)
  | reeF4 k => exact Or.inr (Or.inl trivial)
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | tits => exact hd.elim

@[expose] def OuterFixedE9 : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → (IsRankTwoIndex d.1 ∨ IsRankThreeIndex d.1) →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range →
        ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e

@[expose] def InnerFusionE9 : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → IsRankTwoIndex d.1 →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range →
        ∀ x : K, orderOf x = 3 → ∃ (g : K) (E : Subgroup K), IsElemAbelian 3 E ∧
          Nat.card E = 9 ∧ g * x * g⁻¹ ∈ E ∧ ∀ e ∈ E, α e = e

@[expose] def RankFourOpen : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → IsRankFourIndex d.1 →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)

@[expose] def RankOneAut : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → IsRankOneIndex d.1 →
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      Nonempty (K ≃* (CFSGIndex.lie d).Group) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2

section Classes

theorem centRankAt_of_pRank_mulAut {d : ValidLieTypeIndex}
    (hA : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      Nonempty (K ≃* (CFSGIndex.lie d).Group) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2) : CentRankAt d := by
  intro X _ _ L hLn hs hnab he hC hX x _
  exfalso
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
    (MulAut.conjNormal : X →* MulAut ↥L) hinj
  have h2 := hA ↥L hs hnab he
  omega

theorem centRankAt_of_rankThree (h2a : OuterFixedE9) (d : ValidLieTypeIndex)
    (hch : d.1.characteristic ≠ 3) (hd : IsRankThreeIndex d.1) : CentRankAt d := by
  refine centRankAt_of_parts (fun X _ _ L _ _ _ he _ _ x hx hxL => ?_)
    (fun K _ _ he => h2a d hch (Or.inr hd) K he)
  obtain ⟨e⟩ := he
  have h := innerRankThreeAt_of_isRankThreeIndex d hch hd ↥L ⟨e⟩ ⟨x, hxL⟩
    (by rw [Subgroup.orderOf_mk]; exact hx)
  exact h.trans (le_pRank_centralizer_of_subgroup L ⟨x, hxL⟩)


theorem centRankAt_of_rankTwo (h2a : OuterFixedE9) (h2b : InnerFusionE9)
    (d : ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3) (hd : IsRankTwoIndex d.1) :
    CentRankAt d := by
  refine centRankAt_of_parts (fun X _ _ L hLn _ _ he hC hX x hx hxL => ?_)
    (fun K _ _ he => h2a d hch (Or.inl hd) K he)
  haveI := hLn
  obtain ⟨y, hy, hyL⟩ := exists_outer_of_noE27 hX (noE27Index_of_isRankTwoIndex d hch hd ↥L he)
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hα3 : (MulAut.conjNormal y : MulAut ↥L) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hαo : (MulAut.conjNormal y : MulAut ↥L) ∉ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    fun h => hyL (mem_of_conjNormal_mem_range hC h)
  obtain ⟨g, E, hE, hE9, hgx, hEfix⟩ := h2b d hch hd ↥L he _ hα3 hαo ⟨x, hxL⟩
    (by rw [Subgroup.orderOf_mk]; exact hx)
  exact three_le_of_inner_fusion hxL hy hyL hE hE9 hgx hEfix

theorem centRankOpen_of_kfacts (h2a : OuterFixedE9) (h2b : InnerFusionE9)
    (h2c : RankFourOpen) (h2d : RankOneAut) : CentRankOpen := by
  intro d hch hL3 hd
  rcases isOpenIndex_cases d hch hL3 hd with h | h | h | h
  · exact centRankAt_of_pRank_mulAut fun K _ _ hs hnab he => h2d d hch h K hs hnab he
  · exact centRankAt_of_rankTwo h2a h2b d hch h
  · exact centRankAt_of_rankThree h2a d hch h
  · exact centRankAt_of_four_le fun K _ _ e => h2c d hch h K ⟨e⟩

end Classes

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
