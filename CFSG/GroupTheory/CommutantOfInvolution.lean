module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

theorem commute_and_mul_self_of_commute_involution {G : Type*} [Group G] {B K : Subgroup G}
    {τ : G} (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b * b = 1)
    (hτ : τ * τ = 1) (hτB : ∀ b ∈ B, τ * b * τ⁻¹ ∈ B)
    (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hKτ : ∀ k ∈ K, k * τ = τ * k)
    (hKU : ∀ k ∈ K, ∀ b ∈ B, b * τ = τ * b → k * b = b * k)
    (hKfaith : ∀ k ∈ K, (∀ b ∈ B, k * b = b * k) → k = 1) :
    (∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k) ∧ ∀ k ∈ K, k * k = 1 := by
  set c : G → G → G := fun k b => k * b * k⁻¹ * b⁻¹ with hc_def
  have hc_mem : ∀ k ∈ K, ∀ b ∈ B, c k b ∈ B := by
    intro k hk b hb
    exact B.mul_mem (hKB k hk b hb) (B.inv_mem hb)
  have hτ_inv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hτ_conj_self : ∀ b ∈ B, (τ * b * τ⁻¹) * (τ * b * τ⁻¹) = 1 := by
    intro b hb
    have := hB2 (τ * b * τ⁻¹) (hτB b hb)
    simpa [mul_assoc] using this
  have hd_fix : ∀ k ∈ K, ∀ b ∈ B,
      (b⁻¹ * (τ * b * τ⁻¹)) * τ = τ * (b⁻¹ * (τ * b * τ⁻¹)) := by
    intro k hk b hb
    have hbτ : (τ * b * τ⁻¹) ∈ B := hτB b hb
    have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hB2 b hb)
    have hconj : τ * (b⁻¹ * (τ * b * τ⁻¹)) * τ⁻¹ = b⁻¹ * (τ * b * τ⁻¹) := by
      rw [hb1]
      calc τ * (b * (τ * b * τ⁻¹)) * τ⁻¹
          = (τ * b * τ⁻¹) * (τ * (τ * b * τ⁻¹) * τ⁻¹) := by group
        _ = (τ * b * τ⁻¹) * b := by
            have h1 : τ * (τ * b * τ⁻¹) * τ⁻¹ = b := by
              calc τ * (τ * b * τ⁻¹) * τ⁻¹
                  = (τ * τ) * b * (τ⁻¹ * τ⁻¹) := by group
                _ = b := by simp [hτ, hτ_inv]
            rw [h1]
        _ = b * (τ * b * τ⁻¹) := (hB b hb (τ * b * τ⁻¹) hbτ).symm
    calc (b⁻¹ * (τ * b * τ⁻¹)) * τ
        = (τ * (b⁻¹ * (τ * b * τ⁻¹)) * τ⁻¹) * τ := by rw [hconj]
      _ = τ * (b⁻¹ * (τ * b * τ⁻¹)) := by group
  have hc_tau : ∀ k ∈ K, ∀ b ∈ B, c k (τ * b * τ⁻¹) = c k b := by
    intro k hk b hb
    have hbτ : (τ * b * τ⁻¹) ∈ B := hτB b hb
    have hd : b⁻¹ * (τ * b * τ⁻¹) ∈ B := B.mul_mem (B.inv_mem hb) hbτ
    have hkd : k * (b⁻¹ * (τ * b * τ⁻¹)) = (b⁻¹ * (τ * b * τ⁻¹)) * k :=
      hKU k hk _ hd (hd_fix k hk b hb)
    have hbd : b * (b⁻¹ * (τ * b * τ⁻¹)) = τ * b * τ⁻¹ := by group
    show k * (τ * b * τ⁻¹) * k⁻¹ * (τ * b * τ⁻¹)⁻¹ = k * b * k⁻¹ * b⁻¹
    rw [← hbd]
    have hdk : (b⁻¹ * (τ * b * τ⁻¹)) * k⁻¹ = k⁻¹ * (b⁻¹ * (τ * b * τ⁻¹)) := by
      calc (b⁻¹ * (τ * b * τ⁻¹)) * k⁻¹
          = k⁻¹ * (k * (b⁻¹ * (τ * b * τ⁻¹))) * k⁻¹ := by group
        _ = k⁻¹ * ((b⁻¹ * (τ * b * τ⁻¹)) * k) * k⁻¹ := by rw [hkd]
        _ = k⁻¹ * (b⁻¹ * (τ * b * τ⁻¹)) := by group
    rw [show k * (b * (b⁻¹ * (τ * b * τ⁻¹))) * k⁻¹ * (b * (b⁻¹ * (τ * b * τ⁻¹)))⁻¹
        = k * b * ((b⁻¹ * (τ * b * τ⁻¹)) * k⁻¹ * (b⁻¹ * (τ * b * τ⁻¹))⁻¹) * b⁻¹ by group]
    rw [hdk]
    group
  have hc_fix : ∀ k ∈ K, ∀ b ∈ B, (c k b) * τ = τ * (c k b) := by
    intro k hk b hb
    have hbτ : (τ * b * τ⁻¹) ∈ B := hτB b hb
    have hτk : τ * k * τ⁻¹ = k := by
      rw [← hKτ k hk]
      group
    have hτk' : τ * k⁻¹ * τ⁻¹ = k⁻¹ := by
      have := congrArg Inv.inv hτk
      simpa [mul_assoc] using this
    have hconj : τ * (c k b) * τ⁻¹ = c k (τ * b * τ⁻¹) := by
      show τ * (k * b * k⁻¹ * b⁻¹) * τ⁻¹
          = k * (τ * b * τ⁻¹) * k⁻¹ * (τ * b * τ⁻¹)⁻¹
      calc τ * (k * b * k⁻¹ * b⁻¹) * τ⁻¹
          = (τ * k * τ⁻¹) * (τ * b * τ⁻¹) * (τ * k⁻¹ * τ⁻¹) *
              (τ * b⁻¹ * τ⁻¹) := by group
        _ = k * (τ * b * τ⁻¹) * k⁻¹ * (τ * b⁻¹ * τ⁻¹) := by rw [hτk, hτk']
        _ = k * (τ * b * τ⁻¹) * k⁻¹ * (τ * b * τ⁻¹)⁻¹ := by group
    have h1 : τ * (c k b) * τ⁻¹ = c k b := by rw [hconj, hc_tau k hk b hb]
    calc c k b * τ = (τ * (c k b) * τ⁻¹) * τ := by rw [h1]
      _ = τ * (c k b) := by group
  have hc_central : ∀ k ∈ K, ∀ b ∈ B, ∀ k' ∈ K, k' * c k b = c k b * k' := by
    intro k hk b hb k' hk'
    exact hKU k' hk' (c k b) (hc_mem k hk b hb) (hc_fix k hk b hb)
  have hcc : ∀ k ∈ K, ∀ k' ∈ K, ∀ b ∈ B,
      (k * k') * b * (k * k')⁻¹
        = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by
    intro k hk k' hk' b hb
    have hkb : k' * b * k'⁻¹ = (k' * b * k'⁻¹ * b⁻¹) * b := by group
    have hkc : k * (k' * b * k'⁻¹ * b⁻¹) = (k' * b * k'⁻¹ * b⁻¹) * k :=
      hc_central k' hk' b hb k hk
    have hkb' : k * b * k⁻¹ = (k * b * k⁻¹ * b⁻¹) * b := by group
    calc (k * k') * b * (k * k')⁻¹
        = k * (k' * b * k'⁻¹) * k⁻¹ := by group
      _ = k * ((k' * b * k'⁻¹ * b⁻¹) * b) * k⁻¹ := by conv_lhs => rw [hkb]
      _ = (k * (k' * b * k'⁻¹ * b⁻¹) * k⁻¹) * (k * b * k⁻¹) := by group
      _ = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹) := by rw [hkc]; group
      _ = (k' * b * k'⁻¹ * b⁻¹) * ((k * b * k⁻¹ * b⁻¹) * b) := by conv_lhs => rw [hkb']
      _ = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by group
  have hcc' : ∀ k ∈ K, ∀ k' ∈ K, ∀ b ∈ B,
      (k' * k) * b * (k' * k)⁻¹
        = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by
    intro k hk k' hk' b hb
    have hkb : k * b * k⁻¹ = (k * b * k⁻¹ * b⁻¹) * b := by group
    have hkc : k' * (k * b * k⁻¹ * b⁻¹) = (k * b * k⁻¹ * b⁻¹) * k' :=
      hc_central k hk b hb k' hk'
    have hkb' : k' * b * k'⁻¹ = (k' * b * k'⁻¹ * b⁻¹) * b := by group
    calc (k' * k) * b * (k' * k)⁻¹
        = k' * (k * b * k⁻¹) * k'⁻¹ := by group
      _ = k' * ((k * b * k⁻¹ * b⁻¹) * b) * k'⁻¹ := by conv_lhs => rw [hkb]
      _ = (k' * (k * b * k⁻¹ * b⁻¹) * k'⁻¹) * (k' * b * k'⁻¹) := by group
      _ = (k * b * k⁻¹ * b⁻¹) * (k' * b * k'⁻¹) := by rw [hkc]; group
      _ = (k * b * k⁻¹ * b⁻¹) * ((k' * b * k'⁻¹ * b⁻¹) * b) := by conv_lhs => rw [hkb']
      _ = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by
          calc (k * b * k⁻¹ * b⁻¹) * ((k' * b * k'⁻¹ * b⁻¹) * b)
              = ((k * b * k⁻¹ * b⁻¹) * (k' * b * k'⁻¹ * b⁻¹)) * b := by group
            _ = ((k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹)) * b := by
                rw [hB (k * b * k⁻¹ * b⁻¹) (hc_mem k hk b hb)
                  (k' * b * k'⁻¹ * b⁻¹) (hc_mem k' hk' b hb)]
            _ = (k' * b * k'⁻¹ * b⁻¹) * (k * b * k⁻¹ * b⁻¹) * b := by group
  have hcomm : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := by
    intro k hk k' hk'
    set m := (k * k')⁻¹ * (k' * k) with hm_def
    have hm : m ∈ K := K.mul_mem (K.inv_mem (K.mul_mem hk hk')) (K.mul_mem hk' hk)
    have hm_cent : ∀ b ∈ B, m * b = b * m := by
      intro b hb
      have e : (k * k') * b * (k * k')⁻¹ = (k' * k) * b * (k' * k)⁻¹ := by
        rw [hcc k hk k' hk' b hb, hcc' k hk k' hk' b hb]
      have h1 : m * b * m⁻¹ = b := by
        calc m * b * m⁻¹
            = (k * k')⁻¹ * ((k' * k) * b * (k' * k)⁻¹) * (k * k') := by
                rw [hm_def]; group
          _ = (k * k')⁻¹ * ((k * k') * b * (k * k')⁻¹) * (k * k') := by rw [← e]
          _ = b := by group
      calc m * b = (m * b * m⁻¹) * m := by group
        _ = b * m := by rw [h1]
    exact inv_mul_eq_one.mp (hKfaith m hm hm_cent)
  have hsq : ∀ k ∈ K, k * k = 1 := by
    intro k hk
    have hk2 : k * k ∈ K := K.mul_mem hk hk
    have hcent : ∀ b ∈ B, (k * k) * b = b * (k * k) := by
      intro b hb
      have hkb : k * b * k⁻¹ = (k * b * k⁻¹ * b⁻¹) * b := by group
      have hkc : k * (k * b * k⁻¹ * b⁻¹) = (k * b * k⁻¹ * b⁻¹) * k :=
        hc_central k hk b hb k hk
      have h1 : (k * k) * b * (k * k)⁻¹ = b := by
        calc (k * k) * b * (k * k)⁻¹
            = k * (k * b * k⁻¹) * k⁻¹ := by group
          _ = k * ((k * b * k⁻¹ * b⁻¹) * b) * k⁻¹ := by conv_lhs => rw [hkb]
          _ = (k * (k * b * k⁻¹ * b⁻¹) * k⁻¹) * (k * b * k⁻¹) := by group
          _ = (k * b * k⁻¹ * b⁻¹) * (k * b * k⁻¹) := by rw [hkc]; group
          _ = (k * b * k⁻¹ * b⁻¹) * ((k * b * k⁻¹ * b⁻¹) * b) := by
              conv_lhs => arg 2; rw [hkb]
          _ = b := by
              rw [← mul_assoc, hB2 (k * b * k⁻¹ * b⁻¹) (hc_mem k hk b hb), one_mul]
      calc (k * k) * b = ((k * k) * b * (k * k)⁻¹) * (k * k) := by group
        _ = b * (k * k) := by rw [h1]
    exact hKfaith (k * k) hk2 hcent
  exact ⟨hcomm, hsq⟩

end CFSG.GroupTheory

end
