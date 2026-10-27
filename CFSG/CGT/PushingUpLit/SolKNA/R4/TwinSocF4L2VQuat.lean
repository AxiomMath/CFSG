module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.GorensteinWalter CFSG.ClassicalInvolution.Q3.TL4.MF163

variable {K : Type} [Field K]

theorem pgl2_contra (h2 : (2 : K) ≠ 0) {c w : PGammaL2 K} (hcR : c.right = 1) (hwR : w.right = 1)
    (hc2 : c ^ 2 ≠ 1) (hc4 : c ^ 4 = 1) (hw : w * c * w⁻¹ = c⁻¹) (hww : w * w = c ^ 2) : False := by
  have hce := eq_inl_of_right_eq_one hcR
  have hwe := eq_inl_of_right_eq_one hwR
  set c₀ := c.left
  set w₀ := w.left
  have hc2' : c₀ ^ 2 ≠ 1 := by
    intro h; apply hc2
    rw [hce, ← map_pow, h, map_one]
  have hc4' : c₀ ^ 4 = 1 := by
    have : (SemidirectProduct.inl (c₀ ^ 4) : PGammaL2 K) = SemidirectProduct.inl 1 := by
      rw [map_pow, ← hce, hc4, map_one]
    exact SemidirectProduct.inl_injective this
  have hw' : w₀ * c₀ * w₀⁻¹ = c₀⁻¹ := by
    have : (SemidirectProduct.inl (w₀ * c₀ * w₀⁻¹) : PGammaL2 K) = SemidirectProduct.inl c₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, ← hce, ← hwe, hw]
    exact SemidirectProduct.inl_injective this
  have h1 := pgl2_mul_self_of_inv h2 hc2' hc4' hw'
  apply hc2
  rw [← hww, hwe, ← map_mul, h1, map_one]

theorem quat_pgl2 [Finite K] (hK : IsOddPrimePower (Nat.card K)) (h2 : (2 : K) ≠ 0) {r : ℕ}
    (hr : 4 ≤ r) {X B : PGammaL2 K} (hXo : orderOf X = 2 ^ (r - 1))
    (hBX : B * X * B⁻¹ = X⁻¹) (hBB : B * B = X ^ 2 ^ (r - 2)) :
    X.right = 1 ∧ B.right ≠ 1 ∧ B.right * B.right = 1 := by
  classical
  haveI : IsCyclic (K ≃+* K) := ringAut_isCyclic K hK
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcomm : ∀ x y : K ≃+* K, x * y = y * x := fun x y => IsMulCommutative.is_comm.comm x y
  set rh : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom with hrh
  have hrhv : ∀ g : PGammaL2 K, rh g = g.right := fun g => rfl
  set ξ := X.right with hξ
  set β := B.right with hβ
  have hξ2 : ξ * ξ = 1 := by
    have h1 := congrArg rh hBX
    rw [map_mul, map_mul, map_inv, map_inv, hrhv, hrhv, ← hξ, ← hβ, hcomm β ξ, mul_assoc,
      mul_inv_cancel, mul_one] at h1
    exact mul_eq_one_iff_eq_inv.mpr h1
  have hev : ∀ n : ℕ, 2 ∣ n → ξ ^ n = 1 := by
    intro n ⟨j, hj⟩
    rw [hj, pow_mul, sq, hξ2, one_pow]
  have hβ2 : β * β = 1 := by
    have h1 := congrArg rh hBB
    rw [map_mul, map_pow, hrhv, hrhv, ← hξ, ← hβ] at h1
    rw [h1]
    exact hev _ (dvd_pow_self 2 (by omega))
  set c₁ : PGammaL2 K := X ^ 2 ^ (r - 3) with hc₁
  have hc₁2 : c₁ ^ 2 = X ^ 2 ^ (r - 2) := by
    rw [hc₁, ← pow_mul, ← pow_succ]
    congr 2
    omega
  have hc₁o : orderOf c₁ = 4 := by
    have h4 : 2 ^ (r - 1) = 4 * 2 ^ (r - 3) := by
      rw [show r - 1 = (r - 3) + 2 by omega, pow_add]; ring
    rw [hc₁, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hXo]; exact pow_dvd_pow 2 (by omega)), hXo, h4]
    exact Nat.mul_div_cancel 4 (by positivity)
  have hc₁4 : c₁ ^ 4 = 1 := by rw [← hc₁o]; exact pow_orderOf_eq_one c₁
  have hc₁ne : c₁ ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hc₁o] at this
    omega
  have hc₁R : c₁.right = ξ ^ 2 ^ (r - 3) := by
    rw [hc₁, ← hrhv, map_pow, hrhv]
  have hBc : B * c₁ * B⁻¹ = c₁⁻¹ := by
    rw [hc₁, ← conj_pow, hBX, inv_pow]
  have hXc : X * c₁ = c₁ * X := (Commute.pow_right (Commute.refl X) _).eq
  have hBR_ne : ξ = 1 := by
    by_contra hξ1
    have hc1R : c₁.right = 1 := by
      rw [hc₁R]; exact hev _ (dvd_pow_self 2 (by omega))
    by_cases hβ1 : β = 1
    · exact pgl2_contra h2 hc1R hβ1 hc₁ne hc₁4 hBc (by rw [hc₁2]; exact hBB)
    · have hβξ : β = ξ := eq_of_mul_self_eq_one hβ2 hξ2 hβ1 hξ1
      have hwR : (X * B).right = 1 := by
        rw [SemidirectProduct.mul_right, ← hξ, ← hβ, hβξ, hξ2]
      refine pgl2_contra h2 hc1R hwR hc₁ne hc₁4 ?_ ?_
      · calc X * B * c₁ * (X * B)⁻¹ = X * (B * c₁ * B⁻¹) * X⁻¹ := by group
          _ = X * c₁⁻¹ * X⁻¹ := by rw [hBc]
          _ = c₁⁻¹ := by
            rw [mul_inv_eq_iff_eq_mul]
            exact (Commute.inv_right (show Commute X c₁ from hXc)).eq
      · calc X * B * (X * B) = X * (B * X * B⁻¹) * (B * B) := by group
          _ = c₁ ^ 2 := by rw [hBX, hBB, hc₁2]; group
  refine ⟨hBR_ne, ?_, hβ2⟩
  intro hβ1
  have hc1R : c₁.right = 1 := by rw [hc₁R, hBR_ne, one_pow]
  exact pgl2_contra h2 hc1R hβ1 hc₁ne hc₁4 hBc (by rw [hc₁2]; exact hBB)

theorem odd_mul_self_mod_eight {m : ℕ} (hm : Odd m) : (m * m) % 8 = 1 := by
  have h : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
    obtain ⟨k, hk⟩ := hm
    omega
  rw [Nat.mul_mod]
  rcases h with h | h | h | h <;> rw [h]

theorem isSquare_neg_one_of_fieldAut [Finite K] (hK : IsOddPrimePower (Nat.card K))
    {σ : K ≃+* K} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : IsSquare (-1 : K) := by
  classical
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP K p := charP_of_card_eq_prime_pow hcardF
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  have hcardaut : Nat.card (K ≃+* K) = Module.finrank (ZMod p) K := by
    rw [Nat.card_congr e.toEquiv]
    exact IsGalois.card_aut_eq_finrank (ZMod p) K
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hdvd : 2 ∣ Module.finrank (ZMod p) K := by
    rw [← hcardaut, ← hord]
    exact orderOf_dvd_natCard σ
  obtain ⟨k, hk⟩ := hdvd
  have hcard' : Nat.card K = (p ^ k) * (p ^ k) := by
    rw [← FiniteField.pow_finrank_eq_natCard p K, hk, two_mul, pow_add]
  have hmod : Fintype.card K % 8 = 1 := by
    rw [← Nat.card_eq_fintype_card, hcard']
    exact odd_mul_self_mod_eight hpodd.pow
  rw [FiniteField.isSquare_neg_one_iff]
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
