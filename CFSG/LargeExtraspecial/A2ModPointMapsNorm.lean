module

public import CFSG.LargeExtraspecial.A2ModCfgSL
public import CFSG.ClassicalGroups.SpecialLinear.TvModGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix CFSG.ClassicalGroups.SpecialLinear.TvMod CFSG.RankThree.OrthogonalInvolutions

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}
  {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V}

private theorem apply_mem_commSpace_of_commute {f g : V ≃ₗ[ZMod 2] V} (hc : Commute f g) {x : V}
    (hx : x ∈ commSpace g) : f x ∈ commSpace g := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hx
  refine mem_commSpace.mpr ⟨f y, ?_⟩
  have h : f (g y) = g (f y) := by
    have := DFunLike.congr_fun hc.eq y
    rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
  rw [map_sub, h]

private theorem apply_eq_self_of_mem_span_pair {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {A B : N →ₗ[ZMod 2] V} (hA : Function.Injective A) (hB : Function.Injective B)
    (hAB : LinearMap.range A ⊓ LinearMap.range B = ⊥) {f : V ≃ₗ[ZMod 2] V} {a b₁ b₂ : N}
    (ha : a ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb : b₁ ≠ b₂)
    (h₁ : f (A a) ∈ Submodule.span (ZMod 2) {A a, B b₁})
    (h₂ : f (A a) ∈ Submodule.span (ZMod 2) {A a, B b₂}) : f (A a) = A a := by
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp h₁
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp h₂
  have key : A ((p - r) • a) = B (s • b₂ - q • b₁) := by
    rw [map_sub, map_smul, map_smul, map_smul, sub_smul]
    linear_combination (norm := module) hpq - hrs
  have hmem : A ((p - r) • a) ∈ LinearMap.range A ⊓ LinearMap.range B :=
    ⟨⟨_, rfl⟩, ⟨_, key.symm⟩⟩
  rw [hAB, Submodule.mem_bot] at hmem
  have hz : s • b₂ - q • b₁ = 0 := by
    apply hB
    rw [← key, hmem, map_zero]
  have hq : q = 0 ∧ s = 0 := by
    rcases zmodTwo_eq_zero_or_one q with rfl | rfl <;>
      rcases zmodTwo_eq_zero_or_one s with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [one_smul, zero_smul, sub_zero] at hz
      exact absurd hz hb₂
    · rw [zero_smul, one_smul, zero_sub, neg_eq_zero] at hz
      exact absurd hz hb₁
    · rw [one_smul, one_smul, sub_eq_zero] at hz
      exact absurd hz.symm hb
  obtain ⟨rfl, rfl⟩ := hq
  rw [zero_smul, add_zero] at hpq
  rcases zmodTwo_eq_zero_or_one p with rfl | rfl
  · rw [zero_smul] at hpq
    exact absurd (hA ((f.map_eq_zero_iff.mp hpq.symm).trans (map_zero A).symm)) ha
  · rw [one_smul] at hpq
    exact hpq.symm

theorem IsPointMaps.apply_eq_self_of_commute_tv (hP : IsPointMaps ρ' Q P Pd)
    {f : V ≃ₗ[ZMod 2] V} {v ψ₁ ψ₂ : Fin n → ZMod 2} (hv : v ≠ 0) (hψ₁ : ψ₁ ≠ 0) (hψ₂ : ψ₂ ≠ 0)
    (hψ : ψ₁ ≠ ψ₂) (h₁ : ψ₁ ⬝ᵥ v = 0) (h₂ : ψ₂ ⬝ᵥ v = 0)
    (hc₁ : Commute f (ρ' (tv v ψ₁))) (hc₂ : Commute f (ρ' (tv v ψ₂))) : f (P v) = P v := by
  have key : ∀ {ψ : Fin n → ZMod 2}, ψ ≠ 0 → ψ ⬝ᵥ v = 0 → Commute f (ρ' (tv v ψ)) →
      f (P v) ∈ Submodule.span (ZMod 2) {P v, Pd ψ} := fun hψ h hc => by
    rw [← hP.commSpace_tv v _ hv hψ h]
    refine apply_mem_commSpace_of_commute hc ?_
    rw [hP.commSpace_tv v _ hv hψ h]
    exact Submodule.subset_span (Set.mem_insert _ _)
  exact apply_eq_self_of_mem_span_pair hP.injective hP.injective_dual hP.range_inf_range hv hψ₁
    hψ₂ hψ (key hψ₁ h₁ hc₁) (key hψ₂ h₂ hc₂)

theorem IsPointMaps.apply_dual_eq_self_of_commute_tv (hP : IsPointMaps ρ' Q P Pd)
    {f : V ≃ₗ[ZMod 2] V} {φ w₁ w₂ : Fin n → ZMod 2} (hφ : φ ≠ 0) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hw : w₁ ≠ w₂) (h₁ : φ ⬝ᵥ w₁ = 0) (h₂ : φ ⬝ᵥ w₂ = 0)
    (hc₁ : Commute f (ρ' (tv w₁ φ))) (hc₂ : Commute f (ρ' (tv w₂ φ))) : f (Pd φ) = Pd φ := by
  have key : ∀ {w : Fin n → ZMod 2}, w ≠ 0 → φ ⬝ᵥ w = 0 → Commute f (ρ' (tv w φ)) →
      f (Pd φ) ∈ Submodule.span (ZMod 2) {Pd φ, P w} := fun {w} hw h hc => by
    have e := hP.commSpace_tv w φ hw hφ h
    rw [Set.pair_comm] at e
    rw [← e]
    refine apply_mem_commSpace_of_commute hc ?_
    rw [e]
    exact Submodule.subset_span (Set.mem_insert _ _)
  exact apply_eq_self_of_mem_span_pair hP.injective_dual hP.injective
    (by rw [inf_comm]; exact hP.range_inf_range) hφ hw₁ hw₂ hw (key hw₁ h₁ hc₁)
    (key hw₂ h₂ hc₂)

theorem IsPointMaps.apply_eq_self_of_mem_commSpaceOf_top (hP : IsPointMaps ρ' Q P Pd)
    (hn : 3 ≤ n) {f : V ≃ₗ[ZMod 2] V} (hf : ∀ g, Commute f (ρ' g)) {x : V}
    (hx : x ∈ commSpaceOf ρ' ⊤) : f x = x := by
  rw [hP.commSpaceOf_top] at hx
  obtain ⟨a, ⟨v, rfl⟩, b, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  have hv : f (P v) = P v := by
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, map_zero]
    obtain ⟨ψ₁, ψ₂, h₁, h₂, h₁₂, hv₁, hv₂⟩ :=
      exists_two_ne_zero_annihilator (k := 1) (by omega) ![v]
    exact hP.apply_eq_self_of_commute_tv hv0 h₁ h₂ h₁₂ (by simpa using hv₁ 0)
      (by simpa using hv₂ 0) (hf _) (hf _)
  have hφ : f (Pd φ) = Pd φ := by
    by_cases hφ0 : φ = 0
    · rw [hφ0, map_zero, map_zero]
    obtain ⟨w₁, w₂, h₁, h₂, h₁₂, hw₁, hw₂⟩ :=
      exists_two_ne_zero_annihilator (k := 1) (by omega) ![φ]
    exact hP.apply_dual_eq_self_of_commute_tv hφ0 h₁ h₂ h₁₂
      (by rw [dotProduct_comm]; simpa using hw₁ 0) (by rw [dotProduct_comm]; simpa using hw₂ 0)
      (hf _) (hf _)
  rw [map_add, hv, hφ]

theorem IsPointMaps.comp_invTranspose (hP : IsPointMaps ρ' Q P Pd) :
    IsPointMaps (ρ'.comp (invTranspose : SpecialLinearGroup (Fin n) (ZMod 2) ≃*
      SpecialLinearGroup (Fin n) (ZMod 2)).toMonoidHom) Q Pd P where
  injective := hP.injective_dual
  injective_dual := hP.injective
  map_mulVec g x := by
    change Pd _ = ρ' (invTranspose g) (Pd x)
    rw [← hP.map_contra, contra_def, ← map_inv, coe_invTranspose, inv_inv, vecMul_transpose]
  map_contra g φ := by
    change P _ = ρ' (invTranspose g) (P φ)
    rw [← hP.map_mulVec, coe_invTranspose, mulVec_transpose, contra_def]
  commSpace_tv v φ hv hφ h := by
    change commSpace (ρ' (invTranspose (tv v φ))) = _
    rw [invTranspose_tv, hP.commSpace_tv φ v hφ hv (by rwa [dotProduct_comm]), Set.pair_comm]
  range_inf_range := by rw [inf_comm]; exact hP.range_inf_range
  map_eq_zero := hP.map_eq_zero_dual
  map_eq_zero_dual := hP.map_eq_zero
  commSpaceOf_top := by
    rw [← commSpaceOf_range, MonoidHom.range_eq_top.mpr invTranspose.surjective,
      hP.commSpaceOf_top, sup_comm]

section Normalizer

variable {H : Type*} [Group H] {ρ : H →* (V ≃ₗ[ZMod 2] V)}
  {Ψ : SpecialLinearGroup (Fin n) (ZMod 2) →* H}

theorem IsPointMaps.exists_mul_commute_of_apply_eq (hP : IsPointMaps (ρ.comp Ψ) Q P Pd)
    {ℓ : H} (hℓ : ∀ g, ∃ g', ℓ * Ψ g * ℓ⁻¹ = Ψ g') {v₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    (hfix : ρ ℓ (P v₀) = P v₀) :
    ∃ g₁ : SpecialLinearGroup (Fin n) (ZMod 2), ∀ g, Commute ((Ψ g₁)⁻¹ * ℓ) (Ψ g) := by
  have hmv : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
      P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ (Ψ g) (P x) := hP.map_mulVec
  have hrange : ∀ x, ρ ℓ (P x) ∈ Set.range P := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
    obtain ⟨g, rfl⟩ := exists_mulVec_eq hv₀ hx
    obtain ⟨g', hg'⟩ := hℓ g
    refine ⟨(g' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀, ?_⟩
    calc P ((g' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀) = ρ (Ψ g') (P v₀) := hmv g' v₀
      _ = ρ (Ψ g') (ρ ℓ (P v₀)) := by rw [hfix]
      _ = ρ (Ψ g' * ℓ) (P v₀) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = ρ (ℓ * Ψ g) (P v₀) := by rw [mul_inv_eq_iff_eq_mul.mp hg']
      _ = ρ ℓ (ρ (Ψ g) (P v₀)) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = ρ ℓ (P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v₀)) := by rw [hmv g v₀]
  obtain ⟨F, hPF⟩ : ∃ F : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
      ∀ x, P (F x) = ρ ℓ (P x) :=
    ⟨((ρ ℓ).toLinearMap ∘ₗ P).codLift P hP.injective hrange, fun x =>
      DFunLike.congr_fun (LinearMap.comp_codLift ((ρ ℓ).toLinearMap ∘ₗ P) P hP.injective hrange) x⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hP.injective
    apply (ρ ℓ).injective
    rw [← hPF, ← hPF, hxy]
  have hdet : (LinearMap.toMatrix' F).det = 1 := by
    have hinj : Function.Injective (LinearMap.toMatrix' F).mulVec := by
      intro x y hxy
      apply hFinj
      rwa [← LinearMap.toMatrix'_mulVec, ← LinearMap.toMatrix'_mulVec]
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
    exact zmodTwo_eq_one_of_ne_zero hu.ne_zero
  let g₁ : SpecialLinearGroup (Fin n) (ZMod 2) := ⟨LinearMap.toMatrix' F, hdet⟩
  have hg₁ : ∀ x, P ((g₁ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ ℓ (P x) := by
    intro x
    show P ((LinearMap.toMatrix' F) *ᵥ x) = _
    rw [LinearMap.toMatrix'_mulVec, hPF]
  refine ⟨g₁, fun g => ?_⟩
  obtain ⟨g', hg'⟩ := hℓ g
  obtain ⟨c, hc⟩ : ∃ c : H, c = (Ψ g₁)⁻¹ * ℓ := ⟨_, rfl⟩
  rw [← hc]
  have hcfix : ∀ x, ρ c (P x) = P x := by
    intro x
    calc ρ c (P x) = ρ ((Ψ g₁)⁻¹) (ρ ℓ (P x)) := by rw [hc, map_mul, LinearEquiv.mul_apply]
      _ = ρ ((Ψ g₁)⁻¹) (ρ (Ψ g₁) (P x)) := by rw [← hg₁ x, hmv]
      _ = ρ ((Ψ g₁)⁻¹ * Ψ g₁) (P x) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = P x := by rw [inv_mul_cancel, map_one, LinearEquiv.coe_one, id_eq]
  have hcinv : ∀ x, ρ c⁻¹ (P x) = P x := by
    intro x
    calc ρ c⁻¹ (P x) = ρ c⁻¹ (ρ c (P x)) := by rw [hcfix x]
      _ = ρ (c⁻¹ * c) (P x) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = P x := by rw [inv_mul_cancel, map_one, LinearEquiv.coe_one, id_eq]
  have hcn : c * Ψ g * c⁻¹ = Ψ (g₁⁻¹ * g' * g₁) := by
    rw [hc, map_mul, map_mul, map_inv, ← hg']
    group
  have hsame : ∀ x, P (((g₁⁻¹ * g' * g₁ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) := by
    intro x
    calc P (((g₁⁻¹ * g' * g₁ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ (Ψ (g₁⁻¹ * g' * g₁)) (P x) := hmv _ x
      _ = ρ (c * Ψ g * c⁻¹) (P x) := by rw [hcn]
      _ = ρ c (ρ (Ψ g) (ρ c⁻¹ (P x))) := by
        rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = ρ c (ρ (Ψ g) (P x)) := by rw [hcinv]
      _ = ρ c (P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)) := by rw [hmv]
      _ = P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) := hcfix _
  have hgg : g₁⁻¹ * g' * g₁ = g :=
    Subtype.ext (Matrix.ext_iff_mulVec.mpr fun x => hP.injective (hsame x))
  rw [hgg] at hcn
  exact mul_inv_eq_iff_eq_mul.mp hcn

theorem IsPointMaps.exists_mul_commute_of_apply_dual_eq (hP : IsPointMaps (ρ.comp Ψ) Q P Pd)
    {ℓ : H} (hℓ : ∀ g, ∃ g', ℓ * Ψ g * ℓ⁻¹ = Ψ g') {φ₀ : Fin n → ZMod 2} (hφ₀ : φ₀ ≠ 0)
    (hfix : ρ ℓ (Pd φ₀) = Pd φ₀) :
    ∃ g₁ : SpecialLinearGroup (Fin n) (ZMod 2), ∀ g, Commute ((Ψ g₁)⁻¹ * ℓ) (Ψ g) := by
  let e : SpecialLinearGroup (Fin n) (ZMod 2) ≃* SpecialLinearGroup (Fin n) (ZMod 2) :=
    invTranspose
  have hP' : IsPointMaps (ρ.comp (Ψ.comp e.toMonoidHom)) Q Pd P := hP.comp_invTranspose
  obtain ⟨g₁, hg₁⟩ := hP'.exists_mul_commute_of_apply_eq (ℓ := ℓ) (fun g => by
      obtain ⟨g', hg'⟩ := hℓ (e g)
      exact ⟨e.symm g', by simpa using hg'⟩) hφ₀ hfix
  exact ⟨e g₁, fun g => by simpa using hg₁ (e.symm g)⟩

end Normalizer

end CFSG.LargeExtraspecial.A2Mod
