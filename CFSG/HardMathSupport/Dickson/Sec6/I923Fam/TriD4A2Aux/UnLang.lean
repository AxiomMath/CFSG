module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

theorem fixed_y_eq_one_of_z_eq_one (θ : X ≃* X)
    (hθ₂ : ∀ b ∈ D.root 2, θ b ∈ D.root 2)
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    {y b : X} (hy : y ∈ D.root 1) (hb : b ∈ D.root 2) (hfix : θ (y * b * 1) = y * b * 1) :
    y = 1 := by
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  obtain ⟨b', hb', z', hz', hθy⟩ := hθ₁ y hy
  have hθb := hθ₂ b hb
  have hc : z' * θ b * z'⁻¹ ∈ D.root 2 := D.conj_root₂_mem (hU3 hz') hθb
  have e : θ (y * b * 1) = 1 * (b' * (z' * θ b * z'⁻¹)) * z' := by
    rw [mul_one, map_mul, hθy]
    group
  rw [e, mul_one] at hfix
  have := un_unique D hy (D.root 1).one_mem hb (D.root 2 |>.mul_mem hb' hc) (D.root 3).one_mem hz'
    (by rw [mul_one, hfix])
  exact this.1

theorem fixed_z_eq_one_of_y_eq_one (θ : X ≃* X)
    (hθ₂ : ∀ b ∈ D.root 2, θ b ∈ D.root 2)
    (hθ₃ : ∀ z ∈ D.root 3, ∃ b ∈ D.root 2, ∃ y ∈ D.root 1, θ z = b * y)
    {b z : X} (hb : b ∈ D.root 2) (hz : z ∈ D.root 3) (hfix : θ (1 * b * z) = 1 * b * z) :
    z = 1 := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  obtain ⟨b', hb', y', hy', hθz⟩ := hθ₃ z hz
  have hθb := hθ₂ b hb
  have hc : y'⁻¹ * (θ b * b') * y' ∈ D.root 2 := by
    have := D.conj_root₂_mem (D.U.inv_mem (hU1 hy')) ((D.root 2).mul_mem hθb hb')
    simpa using this
  have e : θ (1 * b * z) = y' * (y'⁻¹ * (θ b * b') * y') * 1 := by
    rw [one_mul, map_mul, hθz]
    simp [mul_assoc]
  rw [e] at hfix
  have := un_unique D hy' (D.root 1).one_mem hc hb (D.root 3).one_mem hz
    hfix
  exact this.2.2.symm

theorem lang_fixfree (θ : X ≃* X) (hθ₂ : ∀ b ∈ D.root 2, θ b ∈ D.root 2)
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    (hθ₃ : ∀ z ∈ D.root 3, ∃ b ∈ D.root 2, ∃ y ∈ D.root 1, θ z = b * y)
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    {h e : X} (hh : h ∈ D.B ⊓ D.N) (he : e ∈ D.U) (hh1 : h ≠ 1)
    (hmid : ∀ b ∈ D.root 2, (h * e) * b * (h * e)⁻¹ = b → b = 1)
    {u : X} (hu : u ∈ D.U) (hθu : θ u = u) (hc : (h * e) * u * (h * e)⁻¹ = u) : u = 1 := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  obtain ⟨y, hy, b, hb, z, hz, rfl⟩ := un_decomp D hu
  by_cases hy1 : y = 1
  · subst hy1
    have hz1 : z = 1 := fixed_z_eq_one_of_y_eq_one D θ hθ₂ hθ₃ hb hz hθu
    subst hz1
    have hb1 : b = 1 := hmid b hb (by simpa using hc)
    subst hb1
    simp
  · have hz1 : z ≠ 1 := fun hz1 => by
      subst hz1
      exact hy1 (fixed_y_eq_one_of_z_eq_one D θ hθ₂ hθ₁ hy hb hθu)
    exfalso
    obtain ⟨h1, h2⟩ := commute_outer_of_commute_fixed' D.U (D.root 1) (D.root 2) (D.root 3)
      hU1 hU2 hU3 (fun y y' b b' z z' hy hy' hb hb' hz hz' e => un_unique D hy hy' hb hb' hz hz' e)
      (fun u hu y hy => D.conj_root₂_mem hu hy)
      (fun u hu v hv => D.commutator_mem_root₂ hab₁ hab₃ hu hv) h e he
      (fun y hy => D.roots.invariant 1 ⟨by norm_num, by norm_num⟩ h hh y hy)
      (fun y hy => D.roots.invariant 2 ⟨by norm_num, by norm_num⟩ h hh y hy)
      (fun y hy => D.roots.invariant 3 ⟨by norm_num, by norm_num⟩ h hh y hy) hy hb hz hc
    exact hh1 (hTor h hh y hy hy1 z hz hz1 (mul_inv_eq_iff_eq_mul.1 h1)
      (mul_inv_eq_iff_eq_mul.1 h2))

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
