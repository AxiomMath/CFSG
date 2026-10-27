module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallBase

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightExOrGood_of_centralR {n : ℕ} (hb : TightBelowR r n) (hn : Nat.card Y = n)
    (hd : TightDatum R S t) (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t) {c : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc2 : orderOf c = 2) (hnt : ∀ y : Y, y * t * y⁻¹ ≠ t * c) :
    TightEx Y R S t ∨ GoodThreeElement R t := by
  set N : Subgroup Y := Subgroup.zpowers c with hNdef
  have hNc : N ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr hcZ
  have hNn : N.Normal := ⟨fun m hm g => by
    rw [Subgroup.mem_center_iff.mp (hNc hm) g, mul_inv_cancel_right]
    exact hm⟩
  have hN2 : IsPGroup 2 ↥N :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  have htN : t ∉ N := fun h => hE2 ⟨N, hNn, hN2, h⟩
  have hntN : ∀ y : Y, ∀ m ∈ N, y * t * y⁻¹ = t * m → m = 1 := by
    intro y m hm hy
    rcases mem_zpowers_of_orderOf_two hc2 hm with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy) (hnt y)
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hN1 : N ≠ ⊥ := fun h1 => hc1 (by
    have : c ∈ N := Subgroup.mem_zpowers c
    rwa [h1, Subgroup.mem_bot] at this)
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hd' := TwistQ.datum hd hN2 htN hntN
  have hc' := twistQ_clsR hd hNc hN2 htN hc
  have hlt : Nat.card (Y ⧸ N) < n := hn ▸ TwistQ.card_lt hN1
  rcases hb (Y ⧸ N) hlt _ _ _ hd' hc' with hex | hgood
  · rcases hex with h2 | ⟨hedgeless, hnot3⟩ | ⟨hedgeless, f, hfs, hfk⟩ | h4
    · exact absurd (TwistQ.inO2_of hN2 h2) hE2
    · refine Or.inl (Or.inr (Or.inl ⟨?_, fun h3 => hnot3 (TwistQ.acts3_map hd hRN h3)⟩))
      by_contra hne
      exact TwistQ.not_edgeless_map hd hNc hN2 htN hntN hne hedgeless
    · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, f.comp (QuotientGroup.mk' N),
        hfs.comp (QuotientGroup.mk'_surjective N), ?_⟩)))
      · by_contra hne
        exact TwistQ.not_edgeless_map hd hNc hN2 htN hntN hne hedgeless
      · rw [← MonoidHom.comap_ker]
        exact hfk.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (h4.of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2)))))
  · exact Or.inr (TwistQ.good_of hd hNc hN2 htN hntN hgood)

theorem tightEx_of_centralR (hr : 4 ≤ r) {n : ℕ} (hb : TightBelowR r n) (hn : Nat.card Y = n)
    (hd : TightDatum R S t) (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t) {c : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc2 : orderOf c = 2) (hnt : ∀ y : Y, y * t * y⁻¹ ≠ t * c) :
    TightEx Y R S t :=
  (tightExOrGood_of_centralR hb hn hd hc hE2 hcZ hc2 hnt).resolve_right
    (not_goodThreeElement_of_four_le hr hd hc.1)

section Cit3


@[expose] def TightTwistAllTwinR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → TightTwisted Y t →
      (∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c) →
        ¬ TightEdgeless R → ¬ TightE4 Y → False

@[expose] def TightTwistStepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → TightTwisted Y t → TightEx Y R S t

theorem tightTwistStepR_of_allTwin (hr : 4 ≤ r) (h : ∀ n, TightTwistAllTwinR r n) (n : ℕ) :
    TightTwistStepR r n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw
  by_cases hall : ∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c
  · by_cases hE4 : TightE4 Y
    · exact Or.inr (Or.inr (Or.inr hE4))
    refine (h n hA hb Y hn R S t hd hc hE2 htw hall ?_ hE4).elim
    obtain ⟨c, hcZ, hc2⟩ := htw.exists_central_involution hc.2.2
    obtain ⟨y, hy⟩ := hall c hcZ hc2
    have hc1 : c ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    exact hd.not_edgeless_of_twin hcZ hc1 hy
  push Not at hall
  obtain ⟨c, hcZ, hc2, hnt⟩ := hall
  exact tightEx_of_centralR hr hb hn hd hc hE2 hcZ hc2 hnt

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
