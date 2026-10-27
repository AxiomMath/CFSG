module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcAutRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcSL2Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTorusLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley

theorem three_le_orderOf_of_not_dvd {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (h : ¬ p ∣ n ^ 2 - 1) : 3 ≤ orderOf ((n : ℕ) : ZMod p) := by
  haveI := Fact.mk hp
  have h0 : ((n : ℕ) : ZMod p) ≠ 0 := fun h0 => hpn ((ZMod.natCast_eq_zero_iff n p).1 h0)
  have hpos : 0 < orderOf ((n : ℕ) : ZMod p) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by have := hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one h0⟩)
  by_contra hlt
  have hdvd : orderOf ((n : ℕ) : ZMod p) ∣ 2 := by
    rcases (by omega : orderOf ((n : ℕ) : ZMod p) = 1 ∨ orderOf ((n : ℕ) : ZMod p) = 2)
      with h1 | h2
    · rw [h1]; exact one_dvd 2
    · rw [h2]
  have hsq : ((n : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
  apply h
  rw [← ZMod.natCast_eq_zero_iff]
  have hn1 : 1 ≤ n ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (dvd_zero p) hpn
    · exact Nat.one_le_pow _ _ hn
  rw [Nat.cast_sub hn1, Nat.cast_pow, hsq, Nat.cast_one, sub_self]

private theorem three_le_of_card {p n : ℕ} (hp : p.Prime) {G : Type*} [Group G] {B : Subgroup G}
    (hB4 : p ^ 4 ≤ Nat.card B) (hB : Nat.card B ≤ p ^ (n + 1)) : 3 ≤ n := by
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hB4.trans hB)
  omega

section Dispatch

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem false_of_badExcCore_E8_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E8 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1) (h54 : ¬ (p = 5 ∧ orderOf ((Q.card : ℕ) : ZMod p) = 4))
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_E8] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hrk := pRank_mulAut_le_E8 Q hv e hp hpq he h54
  have hμ : degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p)) ≤ 4 := by
    by_contra h
    have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega :
      0 < degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.E8 e ≤ 4 := by decide
    exact h (key _ h30 he)
  have hrk' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) ≤ 5 := by
    refine hrk.trans ?_
    split_ifs <;> omega
  have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk'
  exact false_of_hq_of_lift (r := 7) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
    hHq e fun X _ _ φ hφ => seven_le_twoLocalRank_cat_E8 Q hv hq2 φ hφ

theorem false_of_badExcCore_E7_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E7 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_E7] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hp5 := five_le_of_three_le_orderOf hp he
  have hrk := pRank_mulAut_le_E7 Q hv e hp hpq he
  obtain ⟨a, ha⟩ : ∃ a, degCount Tag.E7 (orderOf ((Q.card : ℕ) : ZMod p)) = a := ⟨_, rfl⟩
  rw [ha] at hrk
  have hμ : a ≤ 3 := by
    rw [← ha]
    by_contra h
    have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) (by omega :
      0 < degCount Tag.E7 (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.E7 e ≤ 3 := by decide
    exact h (key _ h30 he)
  rcases le_or_gt (max 1 a + if p ∣ Q.exponent then 1 else 0) 3 with h3 | h4
  · have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC (hrk.trans h3)
    exact false_of_hq_of_lift (r := 5) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ => five_le_twoLocalRank_cat_E7 Q hv hq2 φ hφ
  ·
    have hpf : p ∣ Q.exponent := by
      by_contra hpf
      rw [if_neg hpf] at h4
      omega
    rw [if_pos hpf] at h4
    have ha3 : a = 3 := by omega
    have h7 : 7 ≤ p := by
      rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCount_E7
        (ha ▸ (by omega : 3 ≤ a)) with h | h | h | h
      · omega
      · omega
      · exact ExcHigh.seven_le_of_orderOf_three hp hp5 h
      · exact ExcHigh.seven_le_of_orderOf_six hp h
    have hf7 : 7 ≤ Q.exponent := h7.trans (Nat.le_of_dvd Q.exponent_pos hpf)
    have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC
      (hrk.trans (by rw [if_pos hpf]; omega : max 1 a + (if p ∣ Q.exponent then 1 else 0) ≤ 4))
    exact false_of_hq_of_lift (r := 6) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ => le_twoLocalRank_cat_E7 Q hv hq2 (by omega) (by omega) (by omega) φ hφ

theorem false_of_badExcCore_E6_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hp5 := five_le_of_three_le_orderOf hp he
  have hrk := pRank_mulAut_le_E6 Q hv e hp hpq he
  obtain ⟨a, ha⟩ : ∃ a, degCount Tag.E6 (orderOf ((Q.card : ℕ) : ZMod p)) = a := ⟨_, rfl⟩
  rw [ha] at hrk
  have hμ : a ≤ 3 := by
    rw [← ha]
    by_contra h
    have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (by omega :
      0 < degCount Tag.E6 (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.E6 e ≤ 3 := by decide
    exact h (key _ h30 he)
  rcases le_or_gt (max 1 a + if p ∣ Q.exponent then 1 else 0) 3 with h3 | h4
  · have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC (hrk.trans h3)
    exact false_of_hq_of_lift (r := 5) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ => five_le_twoLocalRank_cat_E6 Q hv hq2 φ hφ
  · have hpf : p ∣ Q.exponent := by
      by_contra hpf
      rw [if_neg hpf] at h4
      omega
    rw [if_pos hpf] at h4
    have ha3 : a = 3 := by omega
    have h7 : 7 ≤ p := by
      rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCount_E6
        (ha ▸ (by omega : 3 ≤ a)) with h | h | h
      · omega
      · omega
      · exact ExcHigh.seven_le_of_orderOf_three hp hp5 h
    have hf7 : 7 ≤ Q.exponent := h7.trans (Nat.le_of_dvd Q.exponent_pos hpf)
    have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC
      (hrk.trans (by rw [if_pos hpf]; omega : max 1 a + (if p ∣ Q.exponent then 1 else 0) ≤ 4))
    exact false_of_hq_of_lift (r := 6) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ => le_twoLocalRank_cat_E6 Q hv hq2 (by omega) (by omega) (by omega) φ hφ

theorem false_of_badExcCore_F4_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.F4 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_F4] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hp5 := five_le_of_three_le_orderOf hp he
  have hrk := pRank_mulAut_le_F4 Q hv e hp hpq he
  obtain ⟨a, ha⟩ : ∃ a, degCount Tag.F4 (orderOf ((Q.card : ℕ) : ZMod p)) = a := ⟨_, rfl⟩
  rw [ha] at hrk
  have hμ : a ≤ 2 := by
    rw [← ha]
    by_contra h
    have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (by simp) (by omega :
      0 < degCount Tag.F4 (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 30, 3 ≤ e → degCount Tag.F4 e ≤ 2 := by decide
    exact h (key _ h30 he)
  have h3 := three_le_of_card hp hB4 (card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk)
  have hpf : p ∣ Q.exponent := by
    by_contra hpf
    rw [if_neg hpf] at h3
    omega
  have hf5 : 5 ≤ Q.exponent := hp5.trans (Nat.le_of_dvd Q.exponent_pos hpf)
  have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC
    (hrk.trans (by rw [if_pos hpf]; omega : max 1 a + (if p ∣ Q.exponent then 1 else 0) ≤ 3))
  exact false_of_hq_of_lift (r := 5) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
    hHq e fun X _ _ φ hφ => le_twoLocalRank_cat_F4 Q hv hq2 (by omega) (by omega) (by omega) φ hφ

theorem false_of_badExcCore_twistedE6_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hB4 : p ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hndvd : ¬ p ∣ Q.card ^ 2 - 1)
    (h6 : ¬ (orderOf ((Q.card : ℕ) : ZMod p) = 6 ∧ ¬ p ∣ Q.exponent ∧ Q.exponent ≤ 4))
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    False := by
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar
  subst hchar
  have hpq : p ≠ Q.p := Ne.symm hqp
  have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hndvd
  have hp5 := five_le_of_three_le_orderOf hp he
  have hrk := pRank_mulAut_le_twistedE6 Q hv e hp hpq he
  obtain ⟨a, ha⟩ : ∃ a, degCountTw (orderOf ((Q.card : ℕ) : ZMod p)) = a := ⟨_, rfl⟩
  rw [ha] at hrk
  have hμ : a ≤ 3 := by
    rw [← ha]
    by_contra h
    have h60 := le_sixty_of_degCountTw_pos (by omega :
      0 < degCountTw (orderOf ((Q.card : ℕ) : ZMod p)))
    have key : ∀ e ≤ 60, 3 ≤ e → degCountTw e ≤ 3 := by decide
    exact h (key _ h60 he)
  have h3 := three_le_of_card hp hB4 (card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk)
  rcases le_or_gt (max 1 a + if p ∣ Q.exponent then 1 else 0) 3 with h3' | h4
  ·
    have hf5 : 5 ≤ Q.exponent := by
      by_contra hf
      by_cases hpf : p ∣ Q.exponent
      · exact hf (hp5.trans (Nat.le_of_dvd Q.exponent_pos hpf))
      · rw [if_neg hpf] at h3
        have ha3 : 3 ≤ a := by omega
        rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCountTw
          (ha ▸ (by omega : 3 ≤ a)) with h | h | h
        · omega
        · omega
        · exact h6 ⟨h, hpf, by omega⟩
    have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC (hrk.trans h3')
    exact false_of_hq_of_lift (r := 5) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ =>
        le_twoLocalRank_cat_twistedE6 Q hv hq2 (by omega) (by omega) (by omega) φ hφ
  ·
    have hpf : p ∣ Q.exponent := by
      by_contra hpf
      rw [if_neg hpf] at h4
      omega
    rw [if_pos hpf] at h4
    have ha3 : a = 3 := by omega
    have h7 : 7 ≤ p := by
      rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCountTw
        (ha ▸ (by omega : 3 ≤ a)) with h | h | h
      · omega
      · omega
      · exact ExcHigh.seven_le_of_orderOf_six hp h
    have hf7 : 7 ≤ Q.exponent := h7.trans (Nat.le_of_dvd Q.exponent_pos hpf)
    have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC
      (hrk.trans (by rw [if_pos hpf]; omega : max 1 a + (if p ∣ Q.exponent then 1 else 0) ≤ 4))
    exact false_of_hq_of_lift (r := 6) ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num))
      hHq e fun X _ _ φ hφ =>
        le_twoLocalRank_cat_twistedE6 Q hv hq2 (by omega) (by omega) (by omega) φ hφ

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
