module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VKap

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG.GorensteinWalter CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open scoped commutatorElement

theorem l2_commutator {K : Type} [Field K] (γ : Kˣ) (ε : ℕ) (hε : ε ≤ 1) (σ : K ≃+* K) :
    ⁅(TwinSocF4.tor γ * TwinSocF4.wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K),
      (TwinSocF4.tor (-1) * TwinSocF4.wref : PGammaL2 K)⁆ = TwinSocF4.tor (γ ^ 2) := by
  have hn1 : (-1 : Kˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)
  have hsz : (SemidirectProduct.inr σ : PGammaL2 K) * TwinSocF4.tor (-1) =
      TwinSocF4.tor (-1) * SemidirectProduct.inr σ := by
    rw [TwinSocF4.inr_mul_tor, TwinSocF4.umap_neg_one]
  have hsw : (SemidirectProduct.inr σ : PGammaL2 K) * TwinSocF4.wref =
      TwinSocF4.wref * SemidirectProduct.inr σ := TwinSocF4.inr_mul_wref σ
  have hwa : ∀ a : Kˣ, (TwinSocF4.wref : PGammaL2 K) * TwinSocF4.tor a =
      TwinSocF4.tor a⁻¹ * TwinSocF4.wref := fun a => TwinSocF4.wref_mul_tor a
  have hwz : (TwinSocF4.wref : PGammaL2 K) * TwinSocF4.tor (-1) =
      TwinSocF4.tor (-1) * TwinSocF4.wref := by
    rw [hwa, hn1]
  have hm : (TwinSocF4.tor (γ ^ 2) : PGammaL2 K) * TwinSocF4.tor γ⁻¹ = TwinSocF4.tor γ := by
    rw [← map_mul, show γ ^ 2 * γ⁻¹ = γ by group]
  have hww : (TwinSocF4.wref : PGammaL2 K) * TwinSocF4.wref = 1 := TwinSocF4.wref_mul_wref
  obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
  · simp only [pow_zero, mul_one]
    have hL : (TwinSocF4.tor γ * SemidirectProduct.inr σ : PGammaL2 K) *
        (TwinSocF4.tor (-1) * TwinSocF4.wref) =
        TwinSocF4.tor γ * TwinSocF4.tor (-1) * TwinSocF4.wref * SemidirectProduct.inr σ := by
      calc (TwinSocF4.tor γ * SemidirectProduct.inr σ : PGammaL2 K) *
            (TwinSocF4.tor (-1) * TwinSocF4.wref)
          = TwinSocF4.tor γ * (SemidirectProduct.inr σ * TwinSocF4.tor (-1)) *
              TwinSocF4.wref := by simp only [mul_assoc]
        _ = TwinSocF4.tor γ * (TwinSocF4.tor (-1) * SemidirectProduct.inr σ) *
              TwinSocF4.wref := by rw [hsz]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * (SemidirectProduct.inr σ * TwinSocF4.wref) := by
              simp only [mul_assoc]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * (TwinSocF4.wref * SemidirectProduct.inr σ) := by
              rw [hsw]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * TwinSocF4.wref * SemidirectProduct.inr σ := by
              simp only [mul_assoc]
    have hR : TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
        (TwinSocF4.tor γ * SemidirectProduct.inr σ) =
        TwinSocF4.tor γ * TwinSocF4.tor (-1) * TwinSocF4.wref * SemidirectProduct.inr σ := by
      calc TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
            (TwinSocF4.tor γ * SemidirectProduct.inr σ)
          = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * (TwinSocF4.wref * TwinSocF4.tor γ) *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * (TwinSocF4.tor γ⁻¹ * TwinSocF4.wref) *
              SemidirectProduct.inr σ := by rw [hwa γ]
        _ = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * TwinSocF4.tor γ⁻¹ * TwinSocF4.wref *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor (-1) * TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor γ⁻¹ * TwinSocF4.wref *
              SemidirectProduct.inr σ := by rw [TwinSocF4.tor_comm (γ ^ 2) (-1)]
        _ = TwinSocF4.tor (-1) * (TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor γ⁻¹) * TwinSocF4.wref *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor (-1) * TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ := by
              rw [hm]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * TwinSocF4.wref * SemidirectProduct.inr σ := by
              rw [TwinSocF4.tor_comm (-1) γ]
    have key : (TwinSocF4.tor γ * SemidirectProduct.inr σ : PGammaL2 K) *
        (TwinSocF4.tor (-1) * TwinSocF4.wref) =
        TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
          (TwinSocF4.tor γ * SemidirectProduct.inr σ) := hL.trans hR.symm
    rw [commutatorElement_def, key]
    group
  · simp only [pow_one]
    have hL : (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
        (TwinSocF4.tor (-1) * TwinSocF4.wref) =
        TwinSocF4.tor γ * TwinSocF4.tor (-1) * SemidirectProduct.inr σ := by
      calc (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
            (TwinSocF4.tor (-1) * TwinSocF4.wref)
          = TwinSocF4.tor γ * TwinSocF4.wref * (SemidirectProduct.inr σ * TwinSocF4.tor (-1)) *
              TwinSocF4.wref := by simp only [mul_assoc]
        _ = TwinSocF4.tor γ * TwinSocF4.wref * (TwinSocF4.tor (-1) * SemidirectProduct.inr σ) *
              TwinSocF4.wref := by rw [hsz]
        _ = TwinSocF4.tor γ * TwinSocF4.wref * TwinSocF4.tor (-1) *
              (SemidirectProduct.inr σ * TwinSocF4.wref) := by simp only [mul_assoc]
        _ = TwinSocF4.tor γ * TwinSocF4.wref * TwinSocF4.tor (-1) *
              (TwinSocF4.wref * SemidirectProduct.inr σ) := by rw [hsw]
        _ = TwinSocF4.tor γ * (TwinSocF4.wref * TwinSocF4.tor (-1) * TwinSocF4.wref) *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor γ * (TwinSocF4.tor (-1) * TwinSocF4.wref * TwinSocF4.wref) *
              SemidirectProduct.inr σ := by rw [hwz]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * (TwinSocF4.wref * TwinSocF4.wref) *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * SemidirectProduct.inr σ := by
              rw [hww, mul_one]
    have hR : TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
        (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) =
        TwinSocF4.tor γ * TwinSocF4.tor (-1) * SemidirectProduct.inr σ := by
      calc TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
            (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ)
          = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * (TwinSocF4.wref * TwinSocF4.tor γ) *
              (TwinSocF4.wref * SemidirectProduct.inr σ) := by simp only [mul_assoc]
        _ = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * (TwinSocF4.tor γ⁻¹ * TwinSocF4.wref) *
              (TwinSocF4.wref * SemidirectProduct.inr σ) := by rw [hwa γ]
        _ = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * TwinSocF4.tor γ⁻¹ *
              (TwinSocF4.wref * TwinSocF4.wref) * SemidirectProduct.inr σ := by
              simp only [mul_assoc]
        _ = TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor (-1) * TwinSocF4.tor γ⁻¹ *
              SemidirectProduct.inr σ := by rw [hww, mul_one]
        _ = TwinSocF4.tor (-1) * TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor γ⁻¹ *
              SemidirectProduct.inr σ := by rw [TwinSocF4.tor_comm (γ ^ 2) (-1)]
        _ = TwinSocF4.tor (-1) * (TwinSocF4.tor (γ ^ 2) * TwinSocF4.tor γ⁻¹) *
              SemidirectProduct.inr σ := by simp only [mul_assoc]
        _ = TwinSocF4.tor (-1) * TwinSocF4.tor γ * SemidirectProduct.inr σ := by rw [hm]
        _ = TwinSocF4.tor γ * TwinSocF4.tor (-1) * SemidirectProduct.inr σ := by
              rw [TwinSocF4.tor_comm (-1) γ]
    have key : (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
        (TwinSocF4.tor (-1) * TwinSocF4.wref) =
        TwinSocF4.tor (γ ^ 2) * (TwinSocF4.tor (-1) * TwinSocF4.wref) *
          (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) := hL.trans hR.symm
    rw [commutatorElement_def, key]
    group

theorem l2_alpha_facts {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 4 ≤ r) {α : Kˣ}
    (hα : orderOf α = 2 ^ (r - 1)) {γ : Kˣ} {ε : ℕ} (hε : ε ≤ 1) {σ : K ≃+* K} {q : ℕ}
    (hq : ∀ x : K, σ x = x ^ q) (hσ2 : σ * σ = 1)
    (hBB : (TwinSocF4.tor γ * TwinSocF4.wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) *
        (TwinSocF4.tor γ * TwinSocF4.wref ^ ε * SemidirectProduct.inr σ) = TwinSocF4.tor (-1))
    (hBα : (TwinSocF4.tor γ * TwinSocF4.wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) *
        TwinSocF4.tor α * (TwinSocF4.tor γ * TwinSocF4.wref ^ ε * SemidirectProduct.inr σ)⁻¹ =
        TwinSocF4.tor α⁻¹) :
    (ε = 0 → α ^ (q + 1) = 1 ∧ γ ^ (q + 1) = -1) ∧
    (ε = 1 → 1 ≤ q ∧ α ^ (q - 1) = 1 ∧ γ ^ (q - 1) = -1) := by
  have hum : ∀ c : Kˣ, TwinSocF4.umap σ c = c ^ q := fun c =>
    Units.ext (by rw [TwinSocF4.coe_umap, hq, Units.val_pow_eq_pow_val])
  have hss : (SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inr σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  have hsw : (SemidirectProduct.inr σ : PGammaL2 K) * TwinSocF4.wref =
      TwinSocF4.wref * SemidirectProduct.inr σ := TwinSocF4.inr_mul_wref σ
  have hwa : ∀ a : Kˣ, (TwinSocF4.wref : PGammaL2 K) * TwinSocF4.tor a =
      TwinSocF4.tor a⁻¹ * TwinSocF4.wref := fun a => TwinSocF4.wref_mul_tor a
  have hww : (TwinSocF4.wref : PGammaL2 K) * TwinSocF4.wref = 1 := TwinSocF4.wref_mul_wref
  have hn1 : (-1 : Kˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · exfalso
      have h := hq 0
      rw [h0, pow_zero, map_zero] at h
      exact zero_ne_one h
    · omega
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · subst h0
    simp only [pow_zero, mul_one] at hBB hBα
    have hc : ∀ c : Kˣ, (TwinSocF4.tor γ * SemidirectProduct.inr σ : PGammaL2 K) *
        TwinSocF4.tor c = TwinSocF4.tor (c ^ q) * (TwinSocF4.tor γ * SemidirectProduct.inr σ) := by
      intro c
      calc (TwinSocF4.tor γ * SemidirectProduct.inr σ : PGammaL2 K) * TwinSocF4.tor c
          = TwinSocF4.tor γ * (SemidirectProduct.inr σ * TwinSocF4.tor c) := by
              simp only [mul_assoc]
        _ = TwinSocF4.tor γ * (TwinSocF4.tor (TwinSocF4.umap σ c) * SemidirectProduct.inr σ) := by
              rw [TwinSocF4.inr_mul_tor]
        _ = TwinSocF4.tor γ * (TwinSocF4.tor (c ^ q) * SemidirectProduct.inr σ) := by
              rw [hum]
        _ = TwinSocF4.tor (c ^ q) * (TwinSocF4.tor γ * SemidirectProduct.inr σ) := by
              rw [← mul_assoc, ← mul_assoc, TwinSocF4.tor_comm γ (c ^ q)]
    have chain : (TwinSocF4.tor (γ ^ (q + 1)) : PGammaL2 K) =
        (TwinSocF4.tor γ * SemidirectProduct.inr σ) *
          (TwinSocF4.tor γ * SemidirectProduct.inr σ) := by
      calc (TwinSocF4.tor (γ ^ (q + 1)) : PGammaL2 K)
          = TwinSocF4.tor (γ ^ q) * TwinSocF4.tor γ := by
              rw [pow_succ, map_mul]
        _ = TwinSocF4.tor (γ ^ q) * TwinSocF4.tor γ *
              (SemidirectProduct.inr σ * SemidirectProduct.inr σ) := by
              rw [hss, mul_one]
        _ = TwinSocF4.tor (γ ^ q) * (TwinSocF4.tor γ * SemidirectProduct.inr σ) *
              SemidirectProduct.inr σ := by
              simp only [mul_assoc]
        _ = (TwinSocF4.tor γ * SemidirectProduct.inr σ * TwinSocF4.tor γ) *
              SemidirectProduct.inr σ := by
              rw [← hc γ]
        _ = (TwinSocF4.tor γ * SemidirectProduct.inr σ) *
              (TwinSocF4.tor γ * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
    have hγ : γ ^ (q + 1) = -1 := TwinSocF4.tor_injective (chain.trans hBB)
    rw [hc α, mul_inv_cancel_right] at hBα
    have hα' : α ^ q = α⁻¹ := TwinSocF4.tor_injective hBα
    exact ⟨by rw [pow_succ, hα', inv_mul_cancel], hγ⟩
  · subst h1
    simp only [pow_one] at hBB hBα
    have hc : ∀ c : Kˣ, (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
        TwinSocF4.tor c = TwinSocF4.tor ((c ^ q)⁻¹) *
          (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) := by
      intro c
      calc (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
            TwinSocF4.tor c
          = TwinSocF4.tor γ * (TwinSocF4.wref * (SemidirectProduct.inr σ * TwinSocF4.tor c)) := by
              simp only [mul_assoc]
        _ = TwinSocF4.tor γ * (TwinSocF4.wref *
              (TwinSocF4.tor (TwinSocF4.umap σ c) * SemidirectProduct.inr σ)) := by
              rw [TwinSocF4.inr_mul_tor]
        _ = TwinSocF4.tor γ * (TwinSocF4.wref * (TwinSocF4.tor (c ^ q) * SemidirectProduct.inr σ)) := by
              rw [hum]
        _ = TwinSocF4.tor γ * ((TwinSocF4.wref * TwinSocF4.tor (c ^ q)) * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
        _ = TwinSocF4.tor γ * ((TwinSocF4.tor ((c ^ q)⁻¹) * TwinSocF4.wref) * SemidirectProduct.inr σ) := by
              rw [hwa (c ^ q)]
        _ = (TwinSocF4.tor γ * TwinSocF4.tor ((c ^ q)⁻¹)) *
              (TwinSocF4.wref * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
        _ = (TwinSocF4.tor ((c ^ q)⁻¹) * TwinSocF4.tor γ) *
              (TwinSocF4.wref * SemidirectProduct.inr σ) := by
              rw [TwinSocF4.tor_comm γ ((c ^ q)⁻¹)]
        _ = TwinSocF4.tor ((c ^ q)⁻¹) *
              (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
    have hαq : α ^ q = α := by
      rw [hc α, mul_inv_cancel_right] at hBα
      exact inv_inj.mp (TwinSocF4.tor_injective hBα)
    have hq0 : q ≠ 0 := by omega
    have hαq1 : α ^ (q - 1) = 1 := by
      have h : α ^ (q - 1) * α = 1 * α := by
        rw [pow_sub_one_mul hq0, one_mul, hαq]
      exact mul_right_cancel h
    have hγ : γ ^ (q - 1) = -1 := by
      have hchain : (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
          (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) =
          TwinSocF4.tor ((γ ^ q)⁻¹) * TwinSocF4.tor γ := by
        calc (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ : PGammaL2 K) *
              (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ)
            = ((TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ) * TwinSocF4.tor γ) *
                (TwinSocF4.wref * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
          _ = (TwinSocF4.tor ((γ ^ q)⁻¹) *
                (TwinSocF4.tor γ * TwinSocF4.wref * SemidirectProduct.inr σ)) *
                (TwinSocF4.wref * SemidirectProduct.inr σ) := by
              rw [hc γ]
          _ = TwinSocF4.tor ((γ ^ q)⁻¹) * (TwinSocF4.tor γ * TwinSocF4.wref *
                (SemidirectProduct.inr σ * TwinSocF4.wref) * SemidirectProduct.inr σ) := by
              simp only [mul_assoc]
          _ = TwinSocF4.tor ((γ ^ q)⁻¹) * (TwinSocF4.tor γ * TwinSocF4.wref *
                (TwinSocF4.wref * SemidirectProduct.inr σ) * SemidirectProduct.inr σ) := by
              rw [hsw]
          _ = TwinSocF4.tor ((γ ^ q)⁻¹) * (TwinSocF4.tor γ * (TwinSocF4.wref * TwinSocF4.wref) *
                (SemidirectProduct.inr σ * SemidirectProduct.inr σ)) := by
              simp only [mul_assoc]
          _ = TwinSocF4.tor ((γ ^ q)⁻¹) * TwinSocF4.tor γ := by
              simp only [hww, hss, mul_one]
      have hG2 : (TwinSocF4.tor ((γ ^ q)⁻¹ * γ) : PGammaL2 K) = TwinSocF4.tor (-1) := by
        rw [map_mul, ← hchain]
        exact hBB
      have hγ2 : (γ ^ q)⁻¹ * γ = -1 := TwinSocF4.tor_injective hG2
      have hqγ : γ ^ (q - 1) * γ = γ ^ q := pow_sub_one_mul hq0 γ
      rw [← hqγ, mul_inv_rev, mul_comm γ⁻¹, inv_mul_cancel_right] at hγ2
      exact (inv_eq_iff_eq_inv.mp hγ2).trans hn1
    exact ⟨hq1, hαq1, hγ⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
