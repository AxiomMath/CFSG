module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem mem_S_of_commute_t {s : G} (hsT : s ∈ T) (hsN : s ∈ normalizer (S : Set G))
    (htQs : t ∈ conjugate Q s) {y : G} (hyT : y ∈ T) (hyt : y * t = t * y) : y ∈ S := by
  have huQ : s * t * s⁻¹ ∈ Q := mem_conjugate_iff.mp htQs
  have hu2 : orderOf (s * t * s⁻¹) = 2 := by rw [orderOf_conj', h.t2]
  have huS : ∀ g ∈ S, g * (s * t * s⁻¹) = s * t * s⁻¹ * g := by
    intro g hg
    have h1 := h.tZ _ (conj_mem_of_mem_normalizer hsN hg)
    calc g * (s * t * s⁻¹) = s * ((s⁻¹ * g * s) * t) * s⁻¹ := by group
      _ = s * (t * (s⁻¹ * g * s)) * s⁻¹ := by rw [h1]
      _ = s * t * s⁻¹ * g := by group
  have hu := h.repoint huQ hu2 huS
  have h1 : s * y * s⁻¹ ∈ S := hu.mem_S_of_commute (mul_mem (mul_mem hsT hyT) (inv_mem hsT))
    (by
      calc s * y * s⁻¹ * (s * t * s⁻¹) = s * (y * t) * s⁻¹ := by group
        _ = s * (t * y) * s⁻¹ := by rw [hyt]
        _ = s * t * s⁻¹ * (s * y * s⁻¹) := by group)
  have h2 := conj_mem_of_mem_normalizer hsN h1
  rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h2

include ε in
theorem exists_r₀ (hD : Foote5AutData 𝕊 Lin) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hbot : Q ⊓ conjugate Q s = ⊥) (hnf : ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin)
    (htQs : t ∈ conjugate Q s) (e : ↥(S ⊓ L) ≃* DihedralGroup 4) :
    ∃ r₀ ∈ S ⊓ L, r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ r₀ ≠ t ∧
      ∀ x ∈ S, x * r₀ * x⁻¹ = r₀ ∨ x * r₀ * x⁻¹ = t * r₀ := by
  classical
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hQs4 : Nat.card (conjugate Q s) = 4 := by rw [card_conjugate_eq_card, hQ4]
  have hQssq : ∀ c ∈ conjugate Q s, c * c = 1 := fun c hc => conjugate_sq_eq_one hQsq hc
  obtain ⟨v, hv, hv1, hvt⟩ : ∃ v ∈ conjugate Q s, v ≠ 1 ∧ v ≠ t := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1, t} : Finset G) fun c hc => by
      by_cases hc1 : c = 1
      · rw [hc1]
        exact Finset.mem_insert_self _ _
      · rw [hno c hc hc1]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({1, t} : Finset G).card ≤ 2 := Finset.card_le_two
    omega
  have hvS := h.conjugate_Q_le hsN hv
  obtain ⟨q, hq, r₀, hr₀, rfl⟩ := h.exists_mul_of_inner ε hvS
    (h.mem_innAut_of_mem_conjugate_Q ε hD hQ4 hQsq hsN htQs e hv (hnf _ hv))
  have hqr : q * r₀ = r₀ * q := h.commute_Q_R hq hr₀
  have hr₀2 : r₀ * r₀ = 1 := by
    have h1 := hQssq _ hv
    calc r₀ * r₀ = q * q * (r₀ * r₀) := by rw [hQsq q hq, one_mul]
      _ = q * r₀ * (q * r₀) := by
          rw [show q * r₀ * (q * r₀) = q * (r₀ * q) * r₀ by group, ← hqr]; group
      _ = 1 := h1
  have hQR : ∀ c ∈ Q, c ∈ S ⊓ L → c = 1 := fun c hcQ hcR => by
    have h1 : c ∈ Q ⊓ L := mem_inf.mpr ⟨hcQ, (mem_inf.mp hcR).2⟩
    rwa [h.Q_inf_L, mem_bot] at h1
  have hr₀1 : r₀ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hv hv1
    have h1 : q ∈ Q ⊓ conjugate Q s := mem_inf.mpr ⟨hq, hv⟩
    rw [hbot, mem_bot] at h1
    exact hv1 h1
  have hr₀t : r₀ ≠ t := by
    rintro rfl
    have h1 : q ∈ Q ⊓ conjugate Q s := by
      refine mem_inf.mpr ⟨hq, ?_⟩
      rw [show q = q * r₀ * r₀ by rw [mul_assoc, ht22, mul_one]]
      exact mul_mem hv htQs
    rw [hbot, mem_bot] at h1
    rw [h1, one_mul] at hvt
    exact hvt rfl
  refine ⟨r₀, hr₀, hr₀2, hr₀1, hr₀t, fun x hx => ?_⟩
  have hxv := h.conj_mem_conjugate_Q hsN hx hv
  have hxq : x * q * x⁻¹ ∈ Q := h.conj_mem_Q hx hq
  have hxr : x * r₀ * x⁻¹ ∈ S ⊓ L := h.conj_mem_R hx hr₀
  have hxt : x * t * x⁻¹ = t := by rw [h.tZ x hx, mul_inv_cancel_right]
  rcases eq_of_mem_four hQs4 hQssq htQs hv h.t_ne_one hv1 (Ne.symm hvt) hxv with
    h1 | h1 | h1 | h1
  ·
    right
    have h2 : x * r₀ * x⁻¹ * (t * r₀)⁻¹ = (x * q * x⁻¹)⁻¹ * q := by
      calc x * r₀ * x⁻¹ * (t * r₀)⁻¹ = (x * q * x⁻¹)⁻¹ * (x * (q * r₀) * x⁻¹) * (t * r₀)⁻¹ := by
            group
        _ = (x * q * x⁻¹)⁻¹ * (t * (q * r₀)) * (t * r₀)⁻¹ := by rw [h1]
        _ = (x * q * x⁻¹)⁻¹ * q * (t * r₀ * (t * r₀)⁻¹) := by
            rw [show t * (q * r₀) = q * (t * r₀) by
              rw [← mul_assoc, ← (h.commute_Q_R hq h.tR), mul_assoc]]; group
        _ = (x * q * x⁻¹)⁻¹ * q := by rw [mul_inv_cancel, mul_one]
    have hcR : (x * q * x⁻¹)⁻¹ * q ∈ S ⊓ L := by
      rw [← h2]
      exact mul_mem hxr (inv_mem (mul_mem h.tR hr₀))
    have h3 := hQR _ (mul_mem (inv_mem hxq) hq) hcR
    rw [← h2, mul_inv_eq_one] at h3
    exact h3
  · exact absurd (by
      calc q * r₀ = x⁻¹ * (x * (q * r₀) * x⁻¹) * x := by group
        _ = x⁻¹ * t * x := by rw [h1]
        _ = t := by rw [mul_assoc, ← h.tZ x hx, ← mul_assoc, inv_mul_cancel, one_mul]) hvt
  ·
    left
    have h2 : x * r₀ * x⁻¹ * r₀⁻¹ = (x * q * x⁻¹)⁻¹ * q := by
      calc x * r₀ * x⁻¹ * r₀⁻¹ = (x * q * x⁻¹)⁻¹ * (x * (q * r₀) * x⁻¹) * r₀⁻¹ := by group
        _ = (x * q * x⁻¹)⁻¹ * (q * r₀) * r₀⁻¹ := by rw [h1]
        _ = (x * q * x⁻¹)⁻¹ * q := by group
    have hcR : (x * q * x⁻¹)⁻¹ * q ∈ S ⊓ L := by
      rw [← h2]
      exact mul_mem hxr (inv_mem hr₀)
    have h3 := hQR _ (mul_mem (inv_mem hxq) hq) hcR
    rw [← h2, mul_inv_eq_one] at h3
    exact h3
  · exact absurd (by
      calc q * r₀ = x⁻¹ * (x * (q * r₀) * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group) hv1

include ε in
theorem card_S_le_sixtyfour (hD : Foote5AutData 𝕊 Lin) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hbot : Q ⊓ conjugate Q s = ⊥) (hnf : ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin)
    (htQs : t ∈ conjugate Q s) (e : ↥(S ⊓ L) ≃* DihedralGroup 4) : Nat.card S ≤ 64 := by
  obtain ⟨r₀, hr₀, hr₀2, hr₀1, hr₀t, hr₀x⟩ := h.exists_r₀ ε hD hQ4 hQsq hsN hbot hnf htQs e
  set ρ : G := ((e.symm (DihedralGroup.r 1) : ↥(S ⊓ L)) : G) with hρ
  have hρR : ρ ∈ S ⊓ L := (e.symm _).2
  have hρx : ∀ x ∈ S, x * ρ * x⁻¹ = ρ ∨ x * ρ * x⁻¹ = ρ⁻¹ := by
    intro x hx
    have hy : x * ρ * x⁻¹ ∈ S ⊓ L := h.conj_mem_R hx hρR
    have hd : e ⟨_, hy⟩ * e ⟨_, hy⟩ ≠ 1 := by
      intro h1
      rw [← map_mul, ← map_one e] at h1
      have h2 : x * ρ * x⁻¹ * (x * ρ * x⁻¹) = 1 := congrArg Subtype.val (e.injective h1)
      have h3 : e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.r 1) = 1 := by
        apply Subtype.ext
        show ρ * ρ = 1
        calc ρ * ρ = x⁻¹ * (x * ρ * x⁻¹ * (x * ρ * x⁻¹)) * x := by group
          _ = 1 := by rw [h2]; group
      have h4 : (DihedralGroup.r 1 * DihedralGroup.r 1 : DihedralGroup 4) = 1 := by
        rw [← e.apply_symm_apply (DihedralGroup.r 1 * DihedralGroup.r 1), map_mul, h3,
          map_one]
      exact absurd h4 (by decide)
    rcases dihedral_four_sq_ne_one _ hd with h1 | h1
    · left
      have h2 : (⟨_, hy⟩ : ↥(S ⊓ L)) = e.symm (DihedralGroup.r 1) := by
        rw [← h1, e.symm_apply_apply]
      exact congrArg Subtype.val h2
    · right
      have h2 : (⟨_, hy⟩ : ↥(S ⊓ L)) = (e.symm (DihedralGroup.r 1))⁻¹ := by
        rw [← map_inv, show (DihedralGroup.r 1 : DihedralGroup 4)⁻¹ = DihedralGroup.r 3 by
          decide, ← h1, e.symm_apply_apply]
      exact congrArg Subtype.val h2
  have hd₀ : e ⟨r₀, hr₀⟩ * e ⟨r₀, hr₀⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hr₀2
  have hd₀1 : e ⟨r₀, hr₀⟩ ≠ 1 := fun h1 => hr₀1 (by
    rw [← map_one e] at h1
    exact congrArg Subtype.val (e.injective h1))
  have hd₀2 : e ⟨r₀, hr₀⟩ ≠ DihedralGroup.r 2 := fun h1 => hr₀t (by
    rw [← h.dihedral_four_t e] at h1
    exact congrArg Subtype.val (e.injective h1))
  have hgen : ∀ r ∈ S ⊓ L, ∃ i j : ℕ, r = ρ ^ i * r₀ ^ j := by
    intro r hr
    obtain ⟨i, j, hij⟩ := dihedral_four_gen _ hd₀ hd₀1 hd₀2 (e ⟨r, hr⟩)
    refine ⟨i, j, ?_⟩
    have h1 : (⟨r, hr⟩ : ↥(S ⊓ L)) =
        e.symm (DihedralGroup.r 1) ^ (i : ℕ) * (⟨r₀, hr₀⟩ : ↥(S ⊓ L)) ^ (j : ℕ) := by
      apply e.injective
      rw [map_mul, map_pow, map_pow, e.apply_symm_apply, hij]
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, SubgroupClass.coe_pow] using h2
  have hC : ∀ x ∈ S, x * ρ * x⁻¹ = ρ → x * r₀ * x⁻¹ = r₀ →
      x ∈ S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro x hx h1 h2
    refine mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun r hr => ?_⟩
    obtain ⟨i, j, rfl⟩ := hgen r hr
    have h3 : x * (ρ ^ i * r₀ ^ j) * x⁻¹ = ρ ^ i * r₀ ^ j := by
      have h4 := map_mul (MulAut.conj x) (ρ ^ i) (r₀ ^ j)
      rw [map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, h1, h2]
        at h4
      exact h4
    calc ρ ^ i * r₀ ^ j * x = x * (ρ ^ i * r₀ ^ j) * x⁻¹ * x := by rw [h3]
      _ = x * (ρ ^ i * r₀ ^ j) := by group
  have hCab : ∀ c ∈ S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G),
      c * ρ * c⁻¹ = ρ ∧ c * r₀ * c⁻¹ = r₀ := by
    intro c hc
    have hcC := (mem_inf.mp hc).2
    constructor
    · rw [← mem_centralizer_iff.mp hcC ρ hρR, mul_inv_cancel_right]
    · rw [← mem_centralizer_iff.mp hcC r₀ hr₀, mul_inv_cancel_right]
  have h1 := card_le_four_mul_of_tests inf_le_left hρx hr₀x hCab hC
  have h2 := h.card_centralizer_R_le ε hD
  rw [hQ4] at h2
  omega

end Sec5

end CFSG.ComponentClassification.Foote5
