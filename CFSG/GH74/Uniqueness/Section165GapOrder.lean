module

public import CFSG.GH74.Uniqueness.Section165Field

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace SecGap

theorem exists_inverted_of_outer_order
    (S : ZDSetup X Z M) {F : Subgroup X} {k : ℕ} (hk : 1 ≤ k)
    (hF : Bender.BenderType ↥F (2 * k) 1 1) {z t a : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzF : z ∈ F) (htM : t ∉ M) (htF : t ∈ F) (ht2 : t * t = 1)
    (ha : a ∈ normalizer (F : Set X)) (haD : a ∈ M ⊓ conjugate M t) (ha2 : a * a = 1)
    (haz : a * z = z * a) (hout : ¬ ∃ g : ↥F, ∀ x : ↥F, Sec165.conjAut ha x = g * x * g⁻¹)
    (hiso : Nonempty (Bender.autFixed (Sec165.conjAut ha) ≃* CFSG.Theory.Comparator.PSL2Model k))
    {m : ℕ} (hm : m ∣ 2 ^ k + 1) :
    ∃ x ∈ (M ⊓ conjugate M t) ⊓ F, orderOf x = m ∧ t * x * t⁻¹ = x⁻¹ ∧
      a * x * a⁻¹ = x⁻¹ := by
  have hFM : ¬ F ≤ M := fun h => htM (h htF)
  obtain ⟨Q₀, hzR, hQ₀⟩ := Sec164.exists_sylow_borel_eq S hF hz hzM hzF hFM
  obtain ⟨hc, hcart⟩ := Sec164.cartan_eq_comap hF hQ₀ htF htM ht2
  have hcardC := hc.card_cartan
  have hinvC := hc.ncard_inv
  have hcycC := hc.isCyclic
  have hcbC : Bender.cartan (Q₀ : Subgroup ↥F) ⟨t, htF⟩ ≤ Bender.borel (Q₀ : Subgroup ↥F) :=
    Bender.cartan_le_borel _ _
  generalize Bender.cartan (Q₀ : Subgroup ↥F) ⟨t, htF⟩ = Ca at hcardC hinvC hcycC hcbC hcart
  have hmdvd : m ∣ Nat.card ↥Ca := by
    rw [hcardC, mul_one, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    have e : 4 ^ k - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
        rw [← mul_pow]
        norm_num
      rw [h4]
      zify [h1, show 1 ≤ 2 ^ k * 2 ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity)]
      ring
    rw [e]
    exact Dvd.dvd.mul_right hm _
  have : IsCyclic ↥Ca := hcycC
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Ca)
  have hNpos : 0 < Nat.card ↥Ca := Nat.card_pos
  have hgo : orderOf g ≠ 0 := by rw [hg]; exact hNpos.ne'
  set x₀ : ↥Ca := g ^ (orderOf g / m) with hx₀
  have hx₀o : orderOf x₀ = m := by
    rw [hx₀]
    exact orderOf_pow_orderOf_div hgo (by rw [hg]; exact hmdvd)
  set x₁ : ↥F := (x₀ : ↥F) with hx₁
  have hx₁C : x₁ ∈ Ca := x₀.2
  have hx₁o : orderOf x₁ = m := by rw [hx₁, Subgroup.orderOf_coe, hx₀o]
  have hinvAll : ∀ y ∈ Ca, (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹ := by
    have hsub : {y : ↥F | y ∈ Ca ∧ (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹} ⊆ (Ca : Set ↥F) :=
      fun y hy => hy.1
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [hinvC, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcardC, mul_one])
      (Set.toFinite _)
    intro y hy
    have : y ∈ {y : ↥F | y ∈ Ca ∧ (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹} := by
      rw [heq]; exact hy
    exact this.2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hαC : ∀ y ∈ Ca, Sec165.conjAut ha y ∈ Ca := by
    intro y hy
    rw [hcart] at hy ⊢
    rw [mem_comap] at hy ⊢
    rw [Subgroup.coe_subtype, Sec165.conjAut_apply]
    exact mul_mem (mul_mem haD hy) (inv_mem haD)
  have hcomm : ∀ y₁ ∈ Ca, ∀ y₂ ∈ Ca, y₁ * y₂ = y₂ * y₁ := by
    intro y₁ hy₁ y₂ hy₂
    exact congrArg Subtype.val (IsCyclic.commGroup.mul_comm (⟨y₁, hy₁⟩ : ↥Ca) ⟨y₂, hy₂⟩)
  have hza : Sec165.conjAut ha ⟨z, hzF⟩ = ⟨z, hzF⟩ := Sec165.conjAut_fix ha haz
  have hz'1 : (⟨z, hzF⟩ : ↥F) ≠ 1 := by
    intro h
    have := S.invariant.1 z hz
    rw [show z = 1 from congrArg Subtype.val h, orderOf_one] at this
    omega
  set u₁ := x₁ * Sec165.conjAut ha x₁ with hu₁
  have hαα : Sec165.conjAut ha (Sec165.conjAut ha x₁) = x₁ := by
    have := congrArg (fun σ : MulAut ↥F => σ x₁) (Sec165.conjAut_mul_self ha ha2)
    simpa using this
  have hu₁C : u₁ ∈ Ca := mul_mem hx₁C (hαC _ hx₁C)
  have hu₁fix : Sec165.conjAut ha u₁ = u₁ := by
    rw [hu₁, map_mul, hαα]
    exact hcomm _ (hαC _ hx₁C) _ hx₁C
  have hu₁1 : u₁ = 1 := by
    by_contra hne
    have hpow : u₁ ^ m = 1 := by
      rw [hu₁, (Commute.mul_pow (hcomm _ hx₁C _ (hαC _ hx₁C)) m), ← map_pow,
        ← hx₁o, pow_orderOf_eq_one, map_one, one_mul]
    have hord1 : orderOf u₁ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
    have hpm : p ∣ m := hpd.trans (orderOf_dvd_of_pow_eq_one hpow)
    have hpk : p ∣ 2 ^ k + 1 := hpm.trans hm
    have hp2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpk
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega
    have hu₁pos : orderOf u₁ ≠ 0 := (orderOf_pos u₁).ne'
    have hyo : orderOf (u₁ ^ (orderOf u₁ / p)) = p := orderOf_pow_orderOf_div hu₁pos hpd
    have hyC : u₁ ^ (orderOf u₁ / p) ∈ Ca := Ca.pow_mem hu₁C _
    have hyfix : Sec165.conjAut ha (u₁ ^ (orderOf u₁ / p)) = u₁ ^ (orderOf u₁ / p) := by
      rw [map_pow, hu₁fix]
    exact Sec165.not_fixed_of_dvd hk hF ha ha2 hout hiso hzR hz'1 hza hp hp2 hpk (hcbC hyC) hyo
      hyfix
  have hαx : Sec165.conjAut ha x₁ = x₁⁻¹ := eq_inv_of_mul_eq_one_right hu₁1
  refine ⟨(x₁ : X), ?_, by rw [Subgroup.orderOf_coe, hx₁o], ?_, ?_⟩
  · have := hx₁C
    rw [hcart, mem_comap] at this
    exact mem_inf.mpr ⟨this, x₁.2⟩
  · have := congrArg Subtype.val (hinvAll x₁ hx₁C)
    simp only [coe_mul, coe_inv] at this
    rw [hti]
    exact this
  · have := congrArg Subtype.val hαx
    rw [Sec165.conjAut_apply] at this
    rw [this, coe_inv]

end SecGap

end CFSG.GH74.Uniqueness
