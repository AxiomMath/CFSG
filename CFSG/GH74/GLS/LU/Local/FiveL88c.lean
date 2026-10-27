module

public import CFSG.GH74.GLS.LU.Local.FiveL85a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L88c

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.five_le_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {A : Subgroup G} (hA5 : IsPGroup 5 ↥A)
    (hAN : A ≤ normalizer ((XB t X₁ : Subgroup G) : Set G)) (hAz : A ≤ centralizer ({z} : Set G))
    (hKA : ∀ k ∈ K₁, ∀ b ∈ A, k * b * k⁻¹ ∈ A) : A ≤ XB t X₁ := by
  have hcentX := centralizes_of_five_group hA5 c.card_X2 hAN
  have hAC : ∀ a ∈ A, a ∈ centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
    fun a ha => ⟨Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcentX a ha x hx).symm), hAz ha⟩
  intro a ha
  have haCC := hAC a ha
  rw [c.b82.CC_X2] at haCC
  obtain ⟨x, hx, k, hk, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := K₁)
    (fun a ha b hb => (c.hc.comm b hb a (c.X2_le_K2 ha)).symm)).mp haCC
  have hN : A ⊓ K₁ = ⊥ := by
    apply c.five_normal_in_K1 inf_le_right
    · exact hA5.to_le inf_le_left
    · intro k' hk' n hn
      exact ⟨hKA k' hk' n hn.1, K₁.mul_mem (K₁.mul_mem hk' hn.2) (K₁.inv_mem hk')⟩
  have hkc : ∀ k' ∈ K₁, k' * k * k'⁻¹ * k⁻¹ = 1 := by
    intro k' hk'
    have h1 : k' * (x * k) * k'⁻¹ * (x * k)⁻¹ ∈ A := mul_mem (hKA k' hk' _ ha) (inv_mem ha)
    have hxk' : x * k' = k' * x := (c.hc.comm k' hk' x (c.X2_le_K2 hx)).symm
    have h2 : k' * (x * k) * k'⁻¹ * (x * k)⁻¹ = k' * k * k'⁻¹ * k⁻¹ := by
      have hx' : k' * x * k'⁻¹ = x := by rw [← hxk']; group
      calc k' * (x * k) * k'⁻¹ * (x * k)⁻¹ = (k' * x * k'⁻¹) * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ := by
            group
        _ = x * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ := by rw [hx']
        _ = k' * k * k'⁻¹ * k⁻¹ := by
            have hc0 : k' * k * k'⁻¹ * k⁻¹ ∈ K₁ :=
              K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hk' hk) (K₁.inv_mem hk')) (K₁.inv_mem hk)
            have hcomm : x * (k' * k * k'⁻¹ * k⁻¹) = (k' * k * k'⁻¹ * k⁻¹) * x :=
              (c.hc.comm _ hc0 x (c.X2_le_K2 hx)).symm
            calc x * (k' * k * k'⁻¹) * k⁻¹ * x⁻¹ = x * (k' * k * k'⁻¹ * k⁻¹) * x⁻¹ := by group
              _ = (k' * k * k'⁻¹ * k⁻¹) := by rw [hcomm]; group
    have h3 : k' * k * k'⁻¹ * k⁻¹ ∈ A ⊓ K₁ :=
      ⟨h2 ▸ h1, K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hk' hk) (K₁.inv_mem hk')) (K₁.inv_mem hk)⟩
    rw [hN] at h3
    exact h3
  have hkz : k ∈ zpowers z := by
    have hmem : (⟨k, hk⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨g', hg'⟩
      apply Subtype.ext
      show g' * k = k * g'
      have := hkc g' hg'
      calc g' * k = (g' * k * g'⁻¹ * k⁻¹) * k * g' := by group
        _ = k * g' := by rw [this]; group
    rw [← c.hc.cen₁]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hk1 : k = 1 := by
    rcases mem_zpowers_of_sq_eq_one c.hs.z_sq hkz with h | h
    · exact h
    · exfalso
      obtain ⟨n, hn⟩ := hA5 ⟨x * k, ha⟩
      have hn' : (x * k) ^ (5 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hxz : Commute x z := (c.hc.cz₂ (c.X2_le_K2 hx))
      rw [h, hxz.mul_pow] at hn'
      have hz5 : z ^ (5 ^ n) = z := by
        have hodd : Odd (5 ^ n) := Odd.pow (by decide)
        obtain ⟨m, hm⟩ := hodd
        rw [hm, pow_succ, pow_mul, pow_two, c.hs.z_sq, one_pow, one_mul]
      rw [hz5] at hn'
      have hzX : z ∈ XB t X₁ := by
        have : z = (x ^ (5 ^ n))⁻¹ := eq_inv_of_mul_eq_one_right hn'
        rw [this]; exact inv_mem (pow_mem hx _)
      have h5 : z ^ 5 = 1 := pow_five_of_card c.card_X2 hzX
      have h2 : z ^ 2 = 1 := by rw [pow_two]; exact c.hs.z_sq
      apply c.z_ne_one
      calc z = z ^ 5 * ((z ^ 2)⁻¹) ^ 2 := by group
        _ = 1 := by rw [h5, h2]; simp
  rw [hk1, mul_one]
  exact hx


end L88c

end CFSG.GH74.GLS.LU.Local.Five
