module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big8
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big14
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big17

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section ArithE

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem mod_of_two_pow_exact {n r : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) (h1 : 2 ^ r ∣ n - 1)
    (h2 : ¬ 2 ^ (r + 1) ∣ n - 1) : n % 2 ^ (r + 1) = 2 ^ r + 1 := by
  obtain ⟨t, ht⟩ := h1
  have hodd : t % 2 = 1 := by
    rcases Nat.even_or_odd t with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      apply h2
      refine ⟨j, ?_⟩
      rw [ht, hj, show 2 ^ (r + 1) = 2 ^ r * 2 by rw [pow_succ]]
      ring
    · exact Nat.odd_iff.mp ho
  have hlt : 2 ^ r < 2 ^ (r + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have ht2 : t = 2 * (t / 2) + 1 := by
    have h := Nat.div_add_mod t 2
    rw [hodd] at h
    omega
  have hmod : (n - 1) % 2 ^ (r + 1) = 2 ^ r := by
    rw [ht, ht2, show 2 ^ (r + 1) = 2 ^ r * 2 by rw [pow_succ]]
    rw [mul_add, mul_one, ← mul_assoc, ← pow_succ]
    rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlt
  have hlt2 : 2 ^ r + 1 < 2 ^ (r + 1) := by
    have h1lt : 1 < 2 ^ r := Nat.one_lt_pow (by omega) (by norm_num)
    rw [pow_succ]
    omega
  have hM : 1 < 2 ^ (r + 1) := by omega
  conv_lhs => rw [← Nat.sub_add_cancel hn]
  rw [Nat.add_mod, hmod, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt hlt2]

theorem arith_of_tight [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2)))
    (htight : ∀ x : X, x * quatInvolution r e = quatInvolution r e * x →
      (∃ j : ℕ, x ^ 2 ^ j = 1) → x ^ 2 ^ r = 1) :
    p ^ f % 2 ^ (r + 1) = 2 ^ r + 1 := by
  have h1 : 2 ^ r ∣ p ^ f - 1 :=
    two_pow_dvd_card_sub_one E e hF hp2 h4 hf hidx hr hz hσ₀1 hσ₀2 hq
  refine mod_of_two_pow_exact (by omega : 1 ≤ r)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero f (Fact.out : p.Prime).ne_zero)) h1 ?_
  intro hbig
  obtain ⟨w, hwz, hw⟩ :=
    exists_large_element E e hF hp2 h4 hf hidx hr hz hσ₀1 hσ₀2 hq hbig
  set N := orderOf w with hN
  set d := 2 ^ (r + 1) with hd
  have hdvd : d ∣ N := by rw [hN, hd]; exact hw
  have hNpos : 0 < N := by rw [hN]; exact orderOf_pos w
  have hN0 : N ≠ 0 := hNpos.ne'
  set m := N / d with hm
  have hdpos : 0 < d := by rw [hd]; positivity
  have hm0 : m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hNpos hdvd) hdpos).ne'
  have hmdvd : m ∣ N := Nat.div_dvd_of_dvd hdvd
  have hw'm : orderOf (w ^ m) = d := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hm, ← hN]
    exact Nat.div_div_self hdvd hN0
  have hcomm : Commute (w ^ m) (quatInvolution r e) := Commute.pow_left hwz m
  have hw'z : w ^ m * quatInvolution r e = quatInvolution r e * w ^ m := hcomm.eq
  have hw'ord : (w ^ m) ^ 2 ^ (r + 1) = 1 := by
    rw [← hd, ← hw'm, pow_orderOf_eq_one]
  have htight' : (w ^ m) ^ 2 ^ r = 1 := htight (w ^ m) hw'z ⟨r + 1, hw'ord⟩
  have hdvd2 : d ∣ 2 ^ r := by
    have h : orderOf (w ^ m) ∣ 2 ^ r := orderOf_dvd_of_pow_eq_one htight'
    rwa [hw'm] at h
  have hle : d ≤ 2 ^ r := Nat.le_of_dvd (pow_pos (by norm_num : (0 : ℕ) < 2) r) hdvd2
  have hlt : 2 ^ r < d := by
    rw [hd]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end ArithE

section Cit3

theorem z2BigModelArith_holds (r : ℕ) : Z2BigModelArith r := by
  intro hr X _ _ Φ hΦ hs hidx p f hp hp2 hf hl
  obtain ⟨hR, -, hgen, -⟩ := hΦ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M₀, hM₀⟩ : Φ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : omegaGen Φ = ⊥ := by
      rw [omegaGen, hne]
      simp
    rw [hgen] at hbot
    have := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(genFittingFStar X))
    apply hx
    apply Subtype.ext
    have hx' : (x : X) ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at hx'
    exact hx'
  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hR.hyp.omega1 M₀ hM₀
  obtain ⟨-, P₀, hP₀, -⟩ := hR.hyp.omega1 M₀ hM₀
  obtain ⟨e₀⟩ := hR.quat M₀ hM₀ P₀ hP₀
  have hzq : quatInvolution r e₀ = z₀ :=
    quatInvolution_eq_of_uniqueInvolution hr hz₀ hP₀.1 e₀
  obtain ⟨F, _, _, hF, h4, _, E, hz⟩ :=
    exists_normalized_emb hs hp2 hf hl (quatInvolution_sq hr e₀) (quatInvolution_ne_one hr e₀)
      (quatInvolution_mem_fstar hidx hr e₀)
  have hzE : E.ρ (MulAut.conj (quatInvolution r e₀)) = SemidirectProduct.inl (pD (-1)) := hz
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hF h4
    omega
  obtain ⟨σ₀, hσ₀1, hσ₀2, hq⟩ := exists_frob_half hF hf hf0
  have hcent : ∀ (R : Subgroup X) (_ : ↥R ≃* QuaternionGroup (2 ^ (r - 2))), R ≤ M₀ →
      ∀ x : X, (∀ y ∈ R, x * y = y * x) → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        x = 1 ∨ x = z₀ := by
    intro R eR hRM x hx hk
    have hzR : quatInvolution r eR = z₀ := quatInvolution_eq_of_uniqueInvolution hr hz₀ hRM eR
    have hzR' : E.ρ (MulAut.conj (quatInvolution r eR)) = SemidirectProduct.inl (pD (-1)) := by
      rw [hzR, ← hzq]; exact hzE
    rcases cent_two_elements E eR hF hp2 h4 hf hidx hr hzR' hσ₀1 hσ₀2 hq hx hk with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzR)
  have htight : ∀ x : X, x * quatInvolution r e₀ = quatInvolution r e₀ * x →
      (∃ j : ℕ, x ^ 2 ^ j = 1) → x ^ 2 ^ r = 1 := by
    intro x hx hk
    have hxz : x * z₀ = z₀ * x := by rw [← hzq]; exact hx
    obtain ⟨j, hkj⟩ := hk
    exact pow_two_pow_eq_one_of_tight hr hR hM₀ hz₀ hcent hxz hkj
  exact arith_of_tight E e₀ hF hp2 h4 hf hidx hr hzE hσ₀1 hσ₀2 hq htight

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
