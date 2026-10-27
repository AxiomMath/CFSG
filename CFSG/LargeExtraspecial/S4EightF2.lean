module

public import CFSG.LargeExtraspecial.S4EightF1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_ne_zero_mem_ker_inf {K W W' : Type*} [DivisionRing K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] [AddCommGroup W'] [Module K W']
    (δ₁ δ₂ : W →ₗ[K] W') (h₁ : finrank K (LinearMap.range δ₁) ≤ 1)
    (h₂ : finrank K (LinearMap.range δ₂) ≤ 1) (h3 : 3 ≤ finrank K W) :
    ∃ u : W, u ≠ 0 ∧ δ₁ u = 0 ∧ δ₂ u = 0 := by
  have k₁ := LinearMap.finrank_range_add_finrank_ker δ₁
  have k₂ := LinearMap.finrank_range_add_finrank_ker δ₂
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker δ₁) (LinearMap.ker δ₂)
  have hle := Submodule.finrank_le (LinearMap.ker δ₁ ⊔ LinearMap.ker δ₂)
  have hne : LinearMap.ker δ₁ ⊓ LinearMap.ker δ₂ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hs
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨u, hu0, LinearMap.mem_ker.mp hu.1, LinearMap.mem_ker.mp hu.2⟩

variable (H : Hyp4 S g) {t : S.O} {F : Subgroup S.O} (hFodd : Odd (Nat.card F))
  (hFR : F ≤ Rbar S g t) (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
  (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1)
  (hclosed : ∀ f₁ ∈ F, ∀ f₂ ∈ F, (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) →
      ∃ f ∈ F, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
include H hFodd hFR hLF hCF hclosed

theorem card_span_orbitF :
    Nat.card (Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) =
      Nat.card F + 1 := by
  classical
  set U := Submodule.span (ZMod 2)
    {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} with hU
  let Φ : Option F → U := fun o => match o with
    | none => 0
    | some f => ⟨(f : S.O) • S.cl (g * S.z * g⁻¹), Submodule.subset_span ⟨f, f.2, rfl⟩⟩
  have hne0 : ∀ f : S.O, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ 0 := fun f h0 => by
    have := congrArg ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
    rw [inv_apply_apply_O, map_zero] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro (_ | f₁) (_ | f₂) h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm (hne0 f₂)
      · exact absurd (congrArg Subtype.val h) (hne0 f₁)
      · have h1 : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
            (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := congrArg Subtype.val h
        exact congrArg some (Subtype.ext (eq_of_mem_of_apply_eq H hFodd hFR hLF hCF f₁.2 f₂.2 h1))
    · rintro ⟨u, hu⟩
      rcases (mem_span_orbitF_iff hclosed).mp hu with rfl | ⟨f, hf, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨f, hf⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Finite.card_option]

theorem finrank_span_orbitF_le_two (hF1 : F ≠ ⊥)
    (hact : ∀ l ∈ S.Lbar g, ∀ u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))},
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    finrank (ZMod 2) (Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) ≤ 2 := by
  set U := Submodule.span (ZMod 2)
    {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} with hU
  by_contra h3
  push Not at h3
  apply hF1
  rw [eq_bot_iff]
  intro f₀ hf₀
  rw [mem_bot]
  refine hCF f₀ hf₀ fun l hl => ?_
  set y := f₀ * l * f₀⁻¹ with hy
  have hz : l * f₀ * l⁻¹ * f₀⁻¹ ∈ F :=
    mul_mem ((mem_normalizer_iff.mp (hLF hl) f₀).mp hf₀) (inv_mem hf₀)
  let δ₁ : U →ₗ[ZMod 2] S.Qt := ((l : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id) ∘ₗ
    U.subtype
  let δ₂ : U →ₗ[ZMod 2] S.Qt := ((y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id) ∘ₗ
    U.subtype
  have hr₁ : LinearMap.range δ₁ ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨u, rfl⟩
    exact hact l hl u u.2
  have hr₂ : LinearMap.range δ₂ ≤
      (ZMod 2) ∙ (f₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    rintro _ ⟨u, rfl⟩
    have hu' := apply_mem_span_orbitF (inv_mem hf₀) u.2
    have h1 := hact l hl _ hu'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    change c • _ = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u
    rw [hy, coe_mul_apply, coe_mul_apply, ← map_smul, hc, map_sub, apply_inv_apply_O]
  have hd : ∀ {W : Submodule (ZMod 2) S.Qt} {w : S.Qt},
      W ≤ (ZMod 2) ∙ w → finrank (ZMod 2) W ≤ 1 := by
    intro W w hW
    refine (Submodule.finrank_mono hW).trans ?_
    have := finrank_span_le_card (R := ZMod 2) ({w} : Set S.Qt)
    simpa using this
  obtain ⟨u, hu0, hu1, hu2⟩ := exists_ne_zero_mem_ker_inf δ₁ δ₂ (hd hr₁) (hd hr₂) h3
  have hlu : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    have : δ₁ u = 0 := hu1
    simpa [δ₁, sub_eq_zero] using this
  have hyu : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    have : δ₂ u = 0 := hu2
    simpa [δ₂, sub_eq_zero] using this
  have hzu : ((l * f₀ * l⁻¹ * f₀⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    have hyi : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
      conv_lhs => rw [← hyu]
      exact inv_apply_apply_O _ _
    rw [show l * f₀ * l⁻¹ * f₀⁻¹ = l * y⁻¹ by rw [hy]; group, coe_mul_apply, hyi, hlu]
  rcases (mem_span_orbitF_iff hclosed).mp u.2 with h0 | ⟨f', hf', hu'⟩
  · exact absurd (Subtype.ext h0) hu0
  have hz1 := eq_one_of_mem_of_apply_eq H hFodd hFR hLF hCF
    (mul_mem (mul_mem (inv_mem hf') hz) hf') (by
      rw [coe_mul_apply, coe_mul_apply, ← hu', hzu, hu', inv_apply_apply_O])
  have : l * f₀ * l⁻¹ * f₀⁻¹ = 1 := by
    have := congrArg (fun x => f' * x * f'⁻¹) hz1
    simpa [mul_assoc] using this
  calc l * f₀ = l * f₀ * l⁻¹ * f₀⁻¹ * (f₀ * l) := by group
    _ = f₀ * l := by rw [this, one_mul]

theorem card_eq_three_of_closed (hF1 : F ≠ ⊥)
    (hact : ∀ l ∈ S.Lbar g, ∀ u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))},
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    Nat.card F = 3 := by
  have h1 := card_span_orbitF H hFodd hFR hLF hCF hclosed
  have h2 := finrank_span_orbitF_le_two H hFodd hFR hLF hCF hclosed hF1 hact
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h1
  have hF2 : Nat.card F ≠ 1 := fun h => hF1 (Subgroup.eq_bot_of_card_eq F h)
  have hpos : 0 < Nat.card F := Nat.card_pos
  interval_cases h : finrank (ZMod 2) (Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) <;> omega

end CFSG.LargeExtraspecial.S4
