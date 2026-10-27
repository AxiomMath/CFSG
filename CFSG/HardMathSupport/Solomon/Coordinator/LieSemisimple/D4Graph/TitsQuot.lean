module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldNoAbel

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.GLS.Stage2.Bender.Thm1

section RGD

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root)


include R in
theorem RGD2.eq_bot_or_isSolvable_quotient [(cartan (H ⊔ U) R.N).Normal]
    (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1)
    (A : Subgroup X) [A.Normal] : A = ⊥ ∨ Group.IsSolvable (X ⧸ A) := by
  have hT := R.isTitsSystem hgen
  have hst : R.w₁ ≠ R.w₂ := R.weyl_ne
  have h3 := R.three_le
  have hcomm : R.w₁ * R.w₂ ≠ R.w₂ * R.w₁ := by
    intro hc
    have hw1 : R.w₁ * R.w₁ = 1 := by
      have := R.orderOf_w 0
      have h' := pow_orderOf_eq_one R.w₁
      rwa [show orderOf R.w₁ = 2 from this, sq] at h'
    have hw2 : R.w₂ * R.w₂ = 1 := by
      have := R.orderOf_w 1
      have h' := pow_orderOf_eq_one R.w₂
      rwa [show orderOf R.w₂ = 2 from this, sq] at h'
    have h2 : (R.w₁ * R.w₂) ^ 2 = 1 := by
      calc (R.w₁ * R.w₂) ^ 2 = R.w₁ * (R.w₂ * R.w₁) * R.w₂ := by rw [sq]; group
        _ = R.w₁ * (R.w₁ * R.w₂) * R.w₂ := by rw [← hc]
        _ = (R.w₁ * R.w₁) * (R.w₂ * R.w₂) := by group
        _ = 1 := by rw [hw1, hw2, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [R.orderOf_w₁_mul_w₂] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rcases rank_two_normal_sup_eq_top_or_le hT hst hcomm A with hAtop | hAB
  ·
    right
    have hBsolv := R.isSolvable_B
    have hsurj : Function.Surjective ((QuotientGroup.mk' A).comp (H ⊔ U).subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : x ∈ A ⊔ (H ⊔ U) := by rw [hAtop]; trivial
      have hx' : x ∈ (A : Set X) * ((H ⊔ U : Subgroup X) : Set X) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk b = (QuotientGroup.mk (a * b) : X ⧸ A)
      rw [QuotientGroup.eq]
      have : b⁻¹ * (a * b) ∈ A := by
        have := (inferInstance : A.Normal).conj_mem a ha b⁻¹
        simpa [mul_assoc] using this
      exact this
    exact Group.isSolvable_of_surjective hsurj
  ·
    left
    have hsat := R.isSaturated
    have hAH : A ≤ H := by
      intro a ha
      have : a ∈ (H ⊔ U) ⊓ R.N := by
        rw [IsSaturated] at hsat
        rw [hsat, Subgroup.mem_iInf]
        intro m
        refine ⟨(m : X) * a * (m : X)⁻¹, hAB ((inferInstance : A.Normal).conj_mem a ha m), ?_⟩
        simp [mul_assoc]
      rwa [R.B_inf_N] at this
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hC a (hAH ha) fun u hu => ?_
    have h1 : a * u * a⁻¹ ∈ U := R.conj_mem_U (hAH ha) hu
    have h2 : u * a⁻¹ * u⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) u
    have h3 : a * (u * a⁻¹ * u⁻¹) ∈ A := A.mul_mem ha h2
    have h4 : a * (u * a⁻¹ * u⁻¹) = (a * u * a⁻¹) * u⁻¹ := by group
    have h5 : (a * u * a⁻¹) * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have h6 : (a * u * a⁻¹) * u⁻¹ ∈ U ⊓ H := ⟨h5, hAH (h4 ▸ h3)⟩
    rw [R.U_inf_H, Subgroup.mem_bot] at h6
    have h7 : a * u * a⁻¹ = u := mul_inv_eq_one.1 h6
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h7]


end RGD

end CFSG.GH74.GLS.SP

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

namespace FoldData

variable {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem eq_bot_or_isSolvable_quotient (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1)
    (A : Subgroup ↥(foldFix φ)) [A.Normal] : A = ⊥ ∨ Group.IsSolvable (↥(foldFix φ) ⧸ A) := by
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hf.exists_rgd2
  have hr₁ : r₁' ∈ foldFix φ := h1
  have hr₂ : r₂' ∈ foldFix φ := h2
  have hroot : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have hgen'' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have R'' := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
  have := R''.cartan_normal
  refine R''.eq_bot_or_isSolvable_quotient hgen'' ?_ A
  intro t ht htc
  apply Subtype.ext
  exact hC t.1 ⟨(Subgroup.mem_subgroupOf.1 ht).1, t.2⟩ (fun u hu => by
    have := htc ⟨u, hu.2⟩ hu
    exact congrArg Subtype.val this)

end FoldData

end CFSG.GH74.GLS.SP
