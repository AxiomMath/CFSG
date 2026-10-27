module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P33d
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Model

public section

open Subgroup CFSG CFSG.ABGLocalTools

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G35

section Aux

variable {G : Type} [Group G]

omit [Group G] in
theorem no_normal_index_two' {H : Type} [Group H] (hs : IsSimpleGroup H)
    (hnab : ∃ a b : H, a * b ≠ b * a) : ∀ M : Subgroup H, M.Normal → M.index ≠ 2 := by
  intro M hM hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
  · have hcard : Nat.card H = 2 := by simpa [Subgroup.index_bot] using hidx
    obtain ⟨a, b, hab⟩ := hnab
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic H := isCyclic_of_prime_card hcard
    exact hab ((IsCyclic.commGroup (α := H)).mul_comm a b)
  · simp at hidx

theorem card_Vsub : Nat.card ↥Vsub = 64 := by
  have h1 : Nat.card ↥(SemidirectProduct.inl : D8 × D8 →* M35).range = Nat.card (D8 × D8) :=
    (Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv).symm
  have h2 : (SemidirectProduct.inl : D8 × D8 →* M35).range = Vsub :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  rw [← h2, h1, Nat.card_prod, DihedralGroup.nat_card]

theorem rot_sq : ∀ u : D8, u ^ 4 = 1 → u ^ 2 ≠ 1 → u ^ 2 = DihedralGroup.r 2 := by decide

theorem refl_of_inv : ∀ s : D8, s * s = 1 → s ≠ 1 → s ≠ DihedralGroup.r 2 →
    alphaFn s = Multiplicative.ofAdd 1 := by decide

theorem conj_eq_inv {D : Subgroup G} {a x : G} (ha4 : orderOf a = 4)
    (hxa : x * a * x⁻¹ ∈ zpowers a)
    (hDa : ∀ d ∈ D, d ∈ zpowers a ∨ x⁻¹ * d ∈ zpowers a)
    (hnc : ∃ d ∈ D, d * x ≠ x * d) : x * a * x⁻¹ = a⁻¹ := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxa
  have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  have hmod : a ^ (k % 4) = a ^ k := by
    have := zpow_mod_orderOf a k
    rwa [ha4] at this
  have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  have hxa' : x * a * x⁻¹ = a ^ (k % 4) := by rw [hmod]; exact hk.symm
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha4; omega
  rcases hr with h | h | h | h
  · exfalso
    rw [h, zpow_zero] at hxa'
    apply ha1
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [hxa']; group
  · exfalso
    rw [h, zpow_one] at hxa'
    have hxc : a * x = x * a := by
      calc a * x = (x * a * x⁻¹) * x := by rw [hxa']
        _ = x * a := by group
    obtain ⟨d, hd, hdx⟩ := hnc
    apply hdx
    have hcx : ∀ g ∈ zpowers a, g * x = x * g := by
      intro g hg
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
      exact (Commute.zpow_left (show Commute a x from hxc) i).eq
    rcases hDa d hd with h1 | h1
    · exact hcx d h1
    · have h2 := hcx _ h1
      calc d * x = x * (x⁻¹ * d) * x := by group
        _ = x * ((x⁻¹ * d) * x) := by group
        _ = x * (x * (x⁻¹ * d)) := by rw [h2]
        _ = x * d := by group
  · exfalso
    rw [h] at hxa'
    have hsq : x * a ^ 2 * x⁻¹ = 1 := by
      calc x * a ^ 2 * x⁻¹ = (x * a * x⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        _ = (a ^ (2 : ℤ)) ^ 2 := by rw [hxa']
        _ = a ^ 4 := by rw [← zpow_natCast, ← zpow_mul]; norm_num
        _ = 1 := ha4'
    have ha2 : a ^ 2 = 1 := by
      calc a ^ 2 = x⁻¹ * (x * a ^ 2 * x⁻¹) * x := by group
        _ = 1 := by rw [hsq]; group
    have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
    rw [ha4] at this
    omega
  · rw [h] at hxa'
    rw [hxa']
    have h3 : a ^ (3 : ℤ) = a ^ 3 := by norm_cast
    rw [h3]
    apply eq_inv_of_mul_eq_one_left
    calc a ^ 3 * a = a ^ 4 := by rw [← pow_succ]
      _ = 1 := ha4'

theorem exists_involution_coset {D D' V : Subgroup G} {b₁ : G}
    (hD' : D' = D.map (MulAut.conj b₁).toMonoidHom)
    (hDn : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D)
    (hb₁2 : b₁ * b₁ ∈ V) (hinf : D ⊓ D' = ⊥) (hcomm : ∀ d ∈ D, ∀ e ∈ D', d * e = e * d)
    (hdec : ∀ v ∈ V, ∃ d ∈ D, ∃ e ∈ D', v = d * e) :
    ∃ w' ∈ D', (b₁ * w'⁻¹) * (b₁ * w'⁻¹) = 1 := by
  obtain ⟨w, hw, w', hw', hww'⟩ := hdec (b₁ * b₁) hb₁2
  have hτw : b₁ * w * b₁⁻¹ ∈ D' := by
    rw [hD']
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  have hτw' : b₁ * w' * b₁⁻¹ ∈ D := by
    have hw'' := hw'
    rw [hD'] at hw''
    obtain ⟨d₀, hd₀, hd₀w⟩ := hw''
    have hd₀w' : w' = b₁ * d₀ * b₁⁻¹ := by
      rw [← hd₀w]
      simp [MulAut.conj_apply]
    have : b₁ * w' * b₁⁻¹ = (b₁ * b₁) * d₀ * (b₁ * b₁)⁻¹ := by
      rw [hd₀w']
      group
    rw [this]
    exact hDn _ hb₁2 d₀ hd₀
  have hcentral : b₁ * (w * w') * b₁⁻¹ = w * w' := by
    rw [← hww']
    group
  have h1 : (b₁ * w' * b₁⁻¹) * (b₁ * w * b₁⁻¹) = w * w' := by
    calc (b₁ * w' * b₁⁻¹) * (b₁ * w * b₁⁻¹) = b₁ * (w' * w) * b₁⁻¹ := by group
      _ = b₁ * (w * w') * b₁⁻¹ := by rw [hcomm w hw w' hw']
      _ = w * w' := hcentral
  obtain ⟨-, hτweq⟩ := Thm1G33.unique_decomp hinf hτw' hw hτw hw' h1
  refine ⟨w', hw', ?_⟩
  have hwinv : b₁⁻¹ * w'⁻¹ * b₁ = w⁻¹ := by
    calc b₁⁻¹ * w'⁻¹ * b₁ = b₁⁻¹ * (b₁ * w * b₁⁻¹)⁻¹ * b₁ := by rw [hτweq]
      _ = w⁻¹ := by group
  calc (b₁ * w'⁻¹) * (b₁ * w'⁻¹) = (b₁ * b₁) * (b₁⁻¹ * w'⁻¹ * b₁) * w'⁻¹ := by group
    _ = (w * w') * w⁻¹ * w'⁻¹ := by rw [← hww', hwinv]
    _ = (w' * w) * w⁻¹ * w'⁻¹ := by rw [hcomm w hw w' hw']
    _ = 1 := by group

end Aux

end CFSG.GH74.GLS.C3.Layer1.Thm1G35

end
