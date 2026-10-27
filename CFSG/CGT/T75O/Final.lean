module

public import CFSG.CGT.T75O.Contra
public import CFSG.CGT.T75O.Fix
public import CFSG.CGT.T75O.Orders
public import CFSG.CGT.T75E.UtiInd
public import CFSG.CGT.T75G.Sec68Basic

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.CGT.T75G CFSG.CGT.T75E

theorem exists_ne_zero_one {E : Type} [Field E] [Finite E] (h : 3 ≤ Nat.card E) :
    ∃ l : E, l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : E) else 0 := fun l => by
    by_cases hl : l = 0
    · exact ⟨false, by simp [hl]⟩
    · exact ⟨true, by simp [hcon l hl]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega


namespace Cfg56

variable {G : Type} [Group G] {T T₁ : Subgroup G} (c : Cfg56 T T₁)
include c

theorem false_of_setup {R : Set (Subgroup G)} {A₀ P P' : Subgroup G}
    (S : CaseH.Setup R (secA T T₁) A₀ P P')
    (h23 : ¬ (Nat.card (secA T T₁) = 2 ∧ (linesThrough R (secA T T₁)).ncard = 3)) : False := by
  have := S.hyp.finite
  obtain ⟨n, m, hn, hm, hq, hL, ⟨cc⟩⟩ := S.exists_coords
  obtain ⟨e, he⟩ := cc.exists_ringHom
  obtain ⟨τ, hτ0, hτ⟩ := cc.exists_tau
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hE : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases cc.classify e he hτ0 hτ hn hF hE with ⟨rfl, hsq⟩ | ⟨rfl, hsq⟩ | ⟨rfl, rfl⟩
  · have h2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m = 1 := by omega
      subst hm1
      exact h23 ⟨by rw [hq]; norm_num, by rw [hL]; norm_num⟩
    have hω : ∃ ω : GaloisField 2 m, ω ≠ 0 ∧ ω ≠ 1 :=
      exists_ne_zero_one (by
        rw [hE]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2)
    obtain ⟨o, hodd, hG⟩ := card_g2 cc e he hτ0 hτ hsq (hE.trans hF.symm) hF h2
    exact c.false_of_coords S cc e he (hfix_g2 cc e he hτ0 hτ hsq hω) hq hL hE hodd hG
      (le_of_eq (by ring))
  · have hE' : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ 3 := by
      rw [hE, ← pow_mul, mul_comm]
    let σ : GaloisField 2 (3 * n) →+* GaloisField 2 (3 * n) :=
      iterateFrobenius (GaloisField 2 (3 * n)) 2 n
    have hσ : ∀ x, σ x = x ^ 2 ^ n := fun x => iterateFrobenius_def 2 n x
    have hσ3 : ∀ x, σ (σ (σ x)) = x :=
      CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hE' hσ
    have hsq' : ∀ s, cc.sharp s = σ s * σ (σ s) := fun s => by
      rw [hsq, hσ, hσ, ← pow_mul, ← pow_add]
      congr 1
      rw [two_mul, pow_add]
    have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hs : ∃ s, σ s ≠ s := by
      by_contra hcon
      push Not at hcon
      have hsurj : Function.Surjective e := fun x => CaseH.exists_e_eq e hF hσ hq1 (hcon x)
      have h1 := Nat.card_le_card_of_surjective e hsurj
      rw [hE, hF] at h1
      have h2 : 2 ^ n < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨o, hodd, hG⟩ := card_d4 cc e he hτ0 hτ hsq hF hE hn
    exact c.false_of_coords S cc e he (hfix_d4 cc e he hτ0 hτ σ hσ3 hsq' hs) hq hL hE hodd hG
      (le_of_eq (by ring))
  · exact absurd (by rw [hL]; norm_num)
      (CaseH.ncard_linesThrough_ne_five S.hyp S.hH S.hA (by rw [hq]; norm_num))

end Cfg56

end CFSG.CGT.T75O
