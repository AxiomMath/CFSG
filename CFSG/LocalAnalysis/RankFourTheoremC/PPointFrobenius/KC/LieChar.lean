module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.AGLEmbedding

private theorem kcLie_exp_eq {p a k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    (hk : p ^ k ∣ p ^ a * m) (hk' : ¬ p ^ (k + 1) ∣ p ^ a * m) : k = a := by
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have h1 : p ^ k ∣ p ^ a := Nat.Coprime.dvd_of_dvd_mul_right hcop hk
  have h2 : k ≤ a := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1
  refine le_antisymm h2 ?_
  by_contra hlt
  push Not at hlt
  exact hk' (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega : k + 1 ≤ a)) m)

private theorem kcLie_two_mul_half {x : ℕ} (hx : x % 2 = 1) :
    2 * ((x ^ 2 - 1) / 2) + 1 = x ^ 2 := by
  have h2 : x ^ 2 % 2 = 1 := Nat.odd_iff.mp (Nat.odd_iff.mpr hx).pow
  generalize x ^ 2 = y at h2 ⊢
  omega

private theorem kcLie_not_dvd_half {p x : ℕ} (hp : p.Prime) (hx : x % 2 = 1) (hpx : p ∣ x) :
    ¬ p ∣ (x ^ 2 - 1) / 2 := by
  intro hm
  have h1 : p ∣ 2 * ((x ^ 2 - 1) / 2) + 1 := by
    rw [kcLie_two_mul_half hx]
    exact dvd_pow hpx two_ne_zero
  exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_right hm 2)).mp h1)

private theorem kcLie_not_dvd_pow_sub_one {p x c : ℕ} (hp : p.Prime) (hpx : p ∣ x) (hc : c ≠ 0)
    (hx : 0 < x) : ¬ p ∣ x ^ c - 1 := by
  intro h
  have h1 : p ∣ x ^ c := dvd_pow hpx hc
  have h2 : 1 ≤ x ^ c := Nat.one_le_pow _ _ hx
  have h3 : x ^ c - 1 + 1 = x ^ c := Nat.sub_add_cancel h2
  rw [← h3] at h1
  exact hp.not_dvd_one ((Nat.dvd_add_right h).mp h1)

private theorem kcLie_not_dvd_pow_add_one {p x c : ℕ} (hp : p.Prime) (hpx : p ∣ x) (hc : c ≠ 0) :
    ¬ p ∣ x ^ c + 1 := by
  intro h
  have h1 : p ∣ x ^ c := dvd_pow hpx hc
  exact hp.not_dvd_one ((Nat.dvd_add_right h1).mp h)

private theorem kcLie_ordTwistedA_two (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ M : ℕ, M ∣ (Q ^ 2 - 1) * (Q ^ 3 + 1) ∧ M ≤ (Q ^ 2 - 1) * (Q ^ 3 + 1) ∧
      ordTwistedA 2 Q = Q ^ 3 * M := by
  have hg : Nat.gcd (2 + 1) (Q + 1) ∣ (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    refine Dvd.dvd.mul_right ?_ _
    obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
    exact ⟨k, by
      have h : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
      omega⟩
  refine ⟨(Q ^ 2 - 1) * (Q ^ 3 + 1) / Nat.gcd (2 + 1) (Q + 1), Nat.div_dvd_of_dvd hg,
    Nat.div_le_self _ _, ?_⟩
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, prod_toNat_icc_two_three Q hQ,
    Nat.mul_div_assoc _ hg]

private theorem kcLie_poly (Q : ℕ) (hQ : 3 ≤ Q) :
    2 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) + 1 < (Q ^ 3) ^ 2 := by
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX : (Q ^ 2 - 1) * (Q ^ 3 + 1) + (Q ^ 3 + 1) = Q ^ 5 + Q ^ 2 := by
    calc (Q ^ 2 - 1) * (Q ^ 3 + 1) + (Q ^ 3 + 1)
        = (Q ^ 2 - 1 + 1) * (Q ^ 3 + 1) := by ring
      _ = Q ^ 2 * (Q ^ 3 + 1) := by rw [Nat.sub_add_cancel h1]
      _ = Q ^ 5 + Q ^ 2 := by ring
  have h3 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have h5 : 2 * Q ^ 2 ≤ Q ^ 5 := by
    have e5 : Q ^ 5 = Q ^ 2 * Q ^ 3 := by ring
    rw [e5]
    calc 2 * Q ^ 2 = Q ^ 2 * 2 := by ring
      _ ≤ Q ^ 2 * Q ^ 3 := Nat.mul_le_mul (le_refl _) h3
  have h6 : 3 * Q ^ 5 ≤ Q ^ 6 := by
    have e6 : Q ^ 6 = Q * Q ^ 5 := by ring
    rw [e6]
    exact Nat.mul_le_mul hQ (le_refl _)
  have hsq : (Q ^ 3) ^ 2 = Q ^ 6 := by ring
  rw [hsq]
  omega

private theorem kcLie_unitary_absurd (Q M : ℕ) (hQ : 3 ≤ Q) (hodd : Q ^ 3 % 2 = 1)
    (hMle : M ≤ (Q ^ 2 - 1) * (Q ^ 3 + 1)) (hmle : ((Q ^ 3) ^ 2 - 1) / 2 ≤ M) : False := by
  have hpoly := kcLie_poly Q hQ
  have hhalf := kcLie_two_mul_half hodd
  omega

theorem kc_linTwoIndex {K : Type} [Group K] [Finite K] {p n f : ℕ} [Fact p.Prime]
    {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsLinTwoIndex p f d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : L = ⊤ := by
  have hf0 : f ≠ 0 := by
    obtain ⟨q, -, -, hqf⟩ := hd
    rw [← hqf]
    exact q.exponent_pos.ne'
  have hp5 : 5 ≤ p := h.p5
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two h.prime (by omega)
  have hodd_pf : p ^ f % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  have hcK : Nat.card K = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_catGroup_linTwo (by omega) hf0 hd
  have hm : ¬ p ∣ ((p ^ f) ^ 2 - 1) / 2 :=
    kcLie_not_dvd_half h.prime hodd_pf (dvd_pow_self p hf0)
  have hdvd1 : p ^ n ∣ p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [← hcK]; exact h.dvd
  have hndvd1 : ¬ p ^ (n + 1) ∣ p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
    rw [← hcK]; exact h.not_dvd
  have hnf : n = f := kcLie_exp_eq h.prime hm hdvd1 hndvd1
  subst hnf
  exact Subgroup.eq_top_of_card_eq L (h.card_L.trans hcK.symm)

theorem kc_unitaryIndex {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsUnitaryIndex p d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨q, hqp, hq⟩ := hd
  have hp5 : 5 ≤ p := h.p5
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two h.prime (by omega)
  have hf0 : q.exponent ≠ 0 := q.exponent_pos.ne'
  have hpf : p ∣ p ^ q.exponent := dvd_pow_self p hf0
  have hQpos : 0 < p ^ q.exponent := pow_pos h.prime.pos _
  have hQ3 : 3 ≤ p ^ q.exponent := by
    have := Nat.le_self_pow hf0 p
    omega
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hcK : Nat.card K = ordTwistedA 2 (p ^ q.exponent) := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_twistedA hq, hqp]
  obtain ⟨M, hMdvd, hMle, hMeq⟩ :=
    kcLie_ordTwistedA_two (p ^ q.exponent) (Nat.one_le_pow _ _ h.prime.pos)
  have hK3 : Nat.card K = p ^ (3 * q.exponent) * M := by
    rw [hcK, hMeq, ← pow_mul, mul_comm q.exponent 3]
  have hpM : ¬ p ∣ M := by
    intro hdM
    rcases (Nat.Prime.dvd_mul h.prime).1 (hdM.trans hMdvd) with h1 | h1
    · exact kcLie_not_dvd_pow_sub_one h.prime hpf (by norm_num) hQpos h1
    · exact kcLie_not_dvd_pow_add_one h.prime hpf (by norm_num) h1
  have hdvd1 : p ^ n ∣ p ^ (3 * q.exponent) * M := by
    rw [← hK3]; exact h.dvd
  have hndvd1 : ¬ p ^ (n + 1) ∣ p ^ (3 * q.exponent) * M := by
    rw [← hK3]; exact h.not_dvd
  have hn3 : n = 3 * q.exponent := kcLie_exp_eq h.prime hpM hdvd1 hndvd1
  have hle : Nat.card L ≤ Nat.card K := Nat.le_of_dvd hKpos h.card_L_dvd
  have hN : p ^ (3 * q.exponent) = (p ^ q.exponent) ^ 3 := pow_mul' p 3 q.exponent
  rw [h.card_L, hK3, hn3, hN] at hle
  have hmle : (((p ^ q.exponent) ^ 3) ^ 2 - 1) / 2 ≤ M :=
    Nat.le_of_mul_le_mul_left hle (pow_pos hQpos 3)
  have hodd : (p ^ q.exponent) ^ 3 % 2 = 1 := Nat.odd_iff.mp hpodd.pow.pow
  exact kcLie_unitary_absurd (p ^ q.exponent) M hQ3 hodd hMle hmle

theorem kc_lieChar (hC : CharPGen) {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L) (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpd : p = d.1.characteristic)
    (hΓ : GLBCore p 1 (S : Subgroup K) ≠ ⊤) : L = ⊤ := by
  have hp5 : 5 ≤ p := h.p5
  have hp2 : p ≠ 2 := by omega
  have hrank : IsRankOneLieIndex d.1 := by
    by_contra hr
    exact hΓ (hC K hs hnab d ⟨e⟩ p h.prime hp2 hpd hr S)
  unfold IsRankOneLieIndex at hrank
  rcases hrank with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
  · have hqp : p = q.p := hpd.trans (by rw [hq, TauCeti.LieTypeIndex.characteristic_A])
    exact kc_linTwoIndex (f := q.exponent) h d ⟨q, hq, hqp.symm, rfl⟩ e
  · have hqp : p = q.p := hpd.trans (by rw [hq, TauCeti.LieTypeIndex.characteristic_twistedA])
    exact (kc_unitaryIndex h d ⟨q, hqp.symm, hq⟩ e).elim
  · have h3 : p = 3 := hpd.trans (by rw [hm, TauCeti.LieTypeIndex.characteristic_reeG2])
    exfalso
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
