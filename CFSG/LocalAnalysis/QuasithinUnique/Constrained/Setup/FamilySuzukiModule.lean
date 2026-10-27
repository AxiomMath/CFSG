module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiTorus
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsSuzuki

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def suzukiSylow
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Sylow 2 (suzukiGroup a K) :=
  have hU := (suzuki_unipotent_structure hK).2.1
  have hord := suzuki_order hK
  have hidx : (suzukiU a K).index = (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    have h := Subgroup.card_mul_index (suzukiU a K)
    rw [hU, hord] at h
    have hq2 : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
    apply Nat.eq_of_mul_eq_mul_left hq2
    rw [h]
    ring
  IsPGroup.toSylow (P := suzukiU a K)
    (IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [hU, ← pow_mul, mul_comm (2 * a + 1) 2])) (by
    rw [hidx]
    have hq : Even (2 ^ (2 * a + 1)) := even_two.pow_of_ne_zero (by omega)
    have h1 : Odd (2 ^ (2 * a + 1) - 1) := by
      have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨k, hk⟩ := hq
      generalize 2 ^ (2 * a + 1) = q at hk hq2 ⊢
      exact ⟨k - 1, by omega⟩
    have h2 : Odd ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
      (hq.pow_of_ne_zero (by norm_num)).add_one
    exact fun h => (Nat.not_even_iff_odd.2 (h1.mul h2)) (even_iff_two_dvd.2 h))

theorem coe_suzukiSylow (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((suzukiSylow hK : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) = suzukiU a K :=
  rfl

theorem card_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiZ0 a K) = 2 ^ (2 * a + 1) := by
  rw [← CFSG.QuasithinUnique.range_suzukiRootCenterHom hK,
    ← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.QuasithinUnique.suzukiRootCenterHom_injective hK)).toEquiv, ← hK]
  exact Nat.card_congr Multiplicative.toAdd

theorem suzuki_sq_eq_one_mem_Z0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ suzukiU a K, x * x = 1 → x ∈ suzukiZ0 a K := by
  intro x hx hx2
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  rw [suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK] at hx2
  have h := (suzukiSElt_inj.1 hx2)
  have hu : u = 0 := by
    have h2 : u ^ 2 ^ (a + 1) * u = 0 := by
      have := h.2
      rw [CharTwo.add_self_eq_zero, zero_add] at this
      exact this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).1 h3
    · exact h3
  subst hu
  exact (mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩

theorem suzuki_Z0_conj (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ z ∈ suzukiZ0 a K, z ≠ 1 → ∀ z' ∈ suzukiZ0 a K, z' ≠ 1 → IsConj z z' := by
  intro z hz hz1 z' hz' hz'1
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
  obtain ⟨v', rfl⟩ := (mem_suzukiZ0_iff hK).1 hz'
  have hv : v ≠ 0 := fun h => hz1 (h ▸ suzukiSElt_zero_zero hK)
  have hv' : v' ≠ 0 := fun h => hz'1 (h ▸ suzukiSElt_zero_zero hK)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  obtain ⟨m, hm⟩ := hbij.2 (Units.mk0 (v' / v) (div_ne_zero hv' hv))
  refine isConj_iff.2 ⟨suzukiDElt a K m⁻¹, ?_⟩
  have h := CFSG.QuasithinUnique.suzukiDElt_conj_center hK m⁻¹ v
  rw [CFSG.QuasithinUnique.suzukiRootCenterHom_apply,
    CFSG.QuasithinUnique.suzukiRootCenterHom_apply] at h
  rw [h, inv_inv]
  congr 1
  have hm' : m ^ (2 ^ (a + 1) + 1) = Units.mk0 (v' / v) (div_ne_zero hv' hv) := by
    have h2 : m ^ ((2 : ℤ) ^ (a + 1) + 1) = Units.mk0 (v' / v) (div_ne_zero hv' hv) := hm
    have h3 : ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h3, zpow_natCast] at h2
    exact h2
  rw [hm']
  simp [hv]

theorem suzuki_involutions_conjugate
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x y : suzukiGroup a K, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
  involutions_conjugate_of_sylow_two (suzukiSylow hK) (suzukiZ0 a K)
    (suzuki_sq_eq_one_mem_Z0 hK) (suzuki_Z0_conj hK)

theorem suzuki_exponent_two_card_le
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (A : Subgroup (suzukiGroup a K)) (hA : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 ^ (2 * a + 1) := by
  rw [← card_suzukiZ0 hK]
  exact card_le_of_sylow_two (suzukiSylow hK) (suzukiZ0 a K) (suzuki_sq_eq_one_mem_Z0 hK) A hA

theorem suzuki_excludes_faithful_binary_FF
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : suzukiGroup a K →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) :
    (∀ t : suzukiGroup a K, orderOf t = 2 →
      (2 * a + 1) + 1 ≤ finrank (ZMod 2) (LinearMap.range ((ρ t : W →ₗ[ZMod 2] W) - 1))) ∧
    ∀ A : Subgroup (suzukiGroup a K), A ≠ ⊥ → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ x ∈ A, x * x = 1) →
      Nat.card A * Nat.card {w : W // ∀ g ∈ A, ρ g w = w} < Nat.card W := by
  obtain ⟨-, ⟨x, t, hx, ht, hxt⟩, -, hlt, hdvd⟩ := suzuki_nonsplit_torus_and_inverter a hK
  have hn : Odd (2 * a + 1) := odd_two_mul_add_one a
  have hxm : orderOf x ∣ 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [hx, pow_mul']
    exact hdvd
  have hm : 2 ^ (2 * a + 1) ≤ orderOf x := by rw [hx]; exact hlt.le
  have hconj := suzuki_involutions_conjugate hK
  refine ⟨quartic_torus_involution_rank hn hconj ht hxt hxm hm ρ hρ, ?_⟩
  intro A hA0 hAc hA2
  exact quartic_torus_card_lt hn hconj (fun A _ hA2 => suzuki_exponent_two_card_le hK A hA2)
    ht hxt hxm hm ρ hρ A hA0 hAc hA2

end CFSG.QuasithinUnique.Setup.Family
