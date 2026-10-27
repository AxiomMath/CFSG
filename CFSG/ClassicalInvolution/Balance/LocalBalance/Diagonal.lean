module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ClassicalInvolution.Balance.LocalBalance

open CFSG CFSG.LocalCores CFSG.Open

section Comm

variable {X : Type*} [Group X]

@[expose] def commMul (A B : Subgroup X) (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : Subgroup X where
  carrier := {z | ∃ x ∈ A, ∃ y ∈ B, z = x * y}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    refine ⟨x₁ * x₂, A.mul_mem hx₁ hx₂, y₁ * y₂, B.mul_mem hy₁ hy₂, ?_⟩
    calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
      _ = x₁ * (x₂ * y₁) * y₂ := by rw [← h x₂ hx₂ y₁ hy₁]
      _ = x₁ * x₂ * (y₁ * y₂) := by group
  inv_mem' := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    refine ⟨x⁻¹, A.inv_mem hx, y⁻¹, B.inv_mem hy, ?_⟩
    have := h x hx y hy
    calc (x * y)⁻¹ = y⁻¹ * x⁻¹ := by group
      _ = x⁻¹ * y⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, this]

theorem mem_commMul {A B : Subgroup X} {h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x} {z : X} :
    z ∈ commMul A B h ↔ ∃ x ∈ A, ∃ y ∈ B, z = x * y := Iff.rfl

end Comm

section Diagonal

variable {X : Type*} [Group X] [Finite X]

theorem exists_diagonal_component {L : Subgroup X} (hL : IsComponent L) {f : X} (hf2 : f * f = 1)
    (hmoved : L.map (MulAut.conj f).toMonoidHom ≠ L) :
    ∃ Δ : Subgroup X, Δ ≤ Subgroup.centralizer ({f} : Set X) ∧
      IsComponent (Δ.subgroupOf (Subgroup.centralizer ({f} : Set X))) ∧
      ∀ x ∈ L, x * (f * x * f⁻¹) ∈ Δ := by
  set L' : Subgroup X := L.map (MulAut.conj f).toMonoidHom with hL'
  have hmem' : ∀ y, y ∈ L' ↔ ∃ x ∈ L, f * x * f⁻¹ = y := fun y => by
    simp [hL', Subgroup.mem_map, MulAut.conj_apply]
  have hf1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hL'c : IsComponent L' := isComponent_map_mulEquiv (MulAut.conj f) hL
  have hdist : ⁅L, L'⁆ = ⊥ :=
    (distinct_components_commute hL hL'c).resolve_left fun h => hmoved h.symm
  have hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hdist hx) y hy).symm
  have hconjL : ∀ x ∈ L, f * x * f⁻¹ ∈ L' := fun x hx => (hmem' _).mpr ⟨x, hx, rfl⟩
  have hswap : ∀ y ∈ L', f * y * f⁻¹ ∈ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmem' y).mp hy
    have : f * (f * x * f⁻¹) * f⁻¹ = x := by
      calc f * (f * x * f⁻¹) * f⁻¹ = (f * f) * x * (f * f)⁻¹ := by group
        _ = x := by rw [hf2]; group
    rw [this]
    exact hx
  let ψ : L →* X :=
    { toFun := fun x => (x : X) * (f * (x : X) * f⁻¹)
      map_one' := by simp
      map_mul' := by
        intro x y
        have h1 : (y : X) * (f * (x : X) * f⁻¹) = (f * (x : X) * f⁻¹) * y :=
          hcomm y y.2 _ (hconjL x x.2)
        change (x : X) * (y : X) * (f * ((x : X) * (y : X)) * f⁻¹) =
          (x : X) * (f * (x : X) * f⁻¹) * ((y : X) * (f * (y : X) * f⁻¹))
        calc (x : X) * (y : X) * (f * ((x : X) * (y : X)) * f⁻¹)
            = (x : X) * ((y : X) * (f * (x : X) * f⁻¹)) * (f * (y : X) * f⁻¹) := by group
          _ = (x : X) * ((f * (x : X) * f⁻¹) * y) * (f * (y : X) * f⁻¹) := by rw [h1]
          _ = (x : X) * (f * (x : X) * f⁻¹) * ((y : X) * (f * (y : X) * f⁻¹)) := by group }
  have hψ : ∀ x : L, ψ x = (x : X) * (f * (x : X) * f⁻¹) := fun x => rfl
  set Δ : Subgroup X := ψ.range with hΔ
  set C : Subgroup X := Subgroup.centralizer ({f} : Set X) with hC
  have hΔmem : ∀ x ∈ L, x * (f * x * f⁻¹) ∈ Δ := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hΔC : Δ ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, hψ]
    have h1 : (x : X) * (f * (x : X) * f⁻¹) = (f * (x : X) * f⁻¹) * x :=
      hcomm x x.2 _ (hconjL x x.2)
    have h2 : f * ((x : X) * (f * (x : X) * f⁻¹)) * f⁻¹ = (x : X) * (f * (x : X) * f⁻¹) := by
      calc f * ((x : X) * (f * (x : X) * f⁻¹)) * f⁻¹
          = (f * (x : X) * f⁻¹) * ((f * f) * (x : X) * (f * f)⁻¹) := by group
        _ = (f * (x : X) * f⁻¹) * x := by rw [hf2]; group
        _ = (x : X) * (f * (x : X) * f⁻¹) := h1.symm
    exact ((mul_inv_eq_iff_eq_mul).mp h2).symm
  refine ⟨Δ, hΔC, ⟨?_, ?_⟩, hΔmem⟩
  ·
    have hker : ψ.rangeRestrict.ker ≤ Subgroup.center L := by
      rw [MonoidHom.ker_rangeRestrict]
      intro x hx
      rw [MonoidHom.mem_ker, hψ] at hx
      have hxL' : (x : X) ∈ L' := by
        have : (x : X) = (f * (x : X) * f⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
        rw [this]
        exact L'.inv_mem (hconjL x x.2)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 _ hxL')
    have hq := isQuasisimple_of_surjective hL.1 ψ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ψ) hker
    exact isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΔC).symm hq
  ·
    set T : Subgroup X := commMul L L' hcomm with hT
    set E : Subgroup X := layer X with hE
    have hEnorm : E.Normal := by
      have : (layer X).Characteristic := layer_characteristic
      infer_instance
    have hLE : L ≤ E := component_le_layer hL
    have hL'E : L' ≤ E := component_le_layer hL'c
    have hTE : T ≤ E := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact E.mul_mem (hLE hx) (hL'E hy)
    have hΔT : Δ ≤ T := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, x.2, f * x * f⁻¹, hconjL x x.2, rfl⟩
    have hEn : E ≤ Subgroup.normalizer (L : Set X) := layer_le_normalizer hL
    have hEn' : E ≤ Subgroup.normalizer (L' : Set X) := layer_le_normalizer hL'c
    have hETn : ∀ k ∈ E, ∀ z ∈ T, k * z * k⁻¹ ∈ T := by
      rintro k hk _ ⟨x, hx, y, hy, rfl⟩
      refine ⟨k * x * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hEn hk) x).mp hx,
        k * y * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hEn' hk) y).mp hy, ?_⟩
      group
    have hcT : ∀ c ∈ L, c ∈ L' → ∀ z ∈ T, c * z = z * c := by
      rintro c hcL hcL' _ ⟨x, hx, y, hy, rfl⟩
      have h1 : c * x = x * c := (hcomm x hx c hcL').symm
      have h2 : c * y = y * c := hcomm c hcL y hy
      calc c * (x * y) = x * c * y := by rw [← mul_assoc, h1, mul_assoc]
        _ = x * (y * c) := by rw [mul_assoc, h2]
        _ = x * y * c := by rw [mul_assoc]
    have hfix : ∀ k ∈ T ⊓ C, ∃ x ∈ L, ∃ c ∈ L, c ∈ L' ∧
        k = c * (x * (f * x * f⁻¹)) := by
      rintro k ⟨⟨x, hx, y, hy, rfl⟩, hkC⟩
      have hkf : x * y * f = f * (x * y) := Subgroup.mem_centralizer_singleton_iff.mp hkC
      have hx'' : f * x * f⁻¹ ∈ L' := hconjL x hx
      have hy' : f * y * f⁻¹ ∈ L := hswap y hy
      have hconj : (f * x * f⁻¹) * (f * y * f⁻¹) = x * y := by
        calc (f * x * f⁻¹) * (f * y * f⁻¹) = f * (x * y) * f⁻¹ := by group
          _ = (x * y * f) * f⁻¹ := by rw [hkf]
          _ = x * y := by group
      have hyx : (f * y * f⁻¹) * (f * x * f⁻¹) = x * y := by
        rw [hcomm _ hy' _ hx'', hconj]
      have hceq : x⁻¹ * (f * y * f⁻¹) = y * (f * x * f⁻¹)⁻¹ := by
        calc x⁻¹ * (f * y * f⁻¹) = x⁻¹ * ((f * y * f⁻¹) * (f * x * f⁻¹)) * (f * x * f⁻¹)⁻¹ := by
              group
          _ = x⁻¹ * (x * y) * (f * x * f⁻¹)⁻¹ := by rw [hyx]
          _ = y * (f * x * f⁻¹)⁻¹ := by group
      refine ⟨x, hx, x⁻¹ * (f * y * f⁻¹), L.mul_mem (L.inv_mem hx) hy', ?_, ?_⟩
      · rw [hceq]
        exact L'.mul_mem hy (L'.inv_mem hx'')
      · have hcx : (x⁻¹ * (f * y * f⁻¹)) * x = x * (x⁻¹ * (f * y * f⁻¹)) :=
          (hcomm x hx _ (by rw [hceq]; exact L'.mul_mem hy (L'.inv_mem hx''))).symm
        calc x * y = x * (x⁻¹ * (f * y * f⁻¹)) * (f * x * f⁻¹) := by rw [hceq]; group
          _ = (x * (x⁻¹ * (f * y * f⁻¹))) * (f * x * f⁻¹) := rfl
          _ = ((x⁻¹ * (f * y * f⁻¹)) * x) * (f * x * f⁻¹) := by rw [hcx]
          _ = (x⁻¹ * (f * y * f⁻¹)) * (x * (f * x * f⁻¹)) := by group
    have hN1 : (Δ.subgroupOf (T ⊓ C)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (le_inf hΔT hΔC)]
      rintro _ k ⟨w, rfl⟩ hk
      obtain ⟨x, hx, c, hcL, hcL', rfl⟩ := hfix k hk
      have hcw : c * ψ w = ψ w * c := hcT c hcL hcL' _ (hΔT ⟨w, rfl⟩)
      have hxw : ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹ ∈ Δ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact ⟨_, rfl⟩
      have hcm : c * (ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹) =
          (ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹) * c := hcT c hcL hcL' _ (hΔT hxw)
      have hψx : ψ ⟨x, hx⟩ = x * (f * x * f⁻¹) := rfl
      rw [← hψx]
      have heq : c * ψ ⟨x, hx⟩ * ψ w * (c * ψ ⟨x, hx⟩)⁻¹ =
          ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹ := by
        calc c * ψ ⟨x, hx⟩ * ψ w * (c * ψ ⟨x, hx⟩)⁻¹
            = c * (ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹) * c⁻¹ := by group
          _ = (ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹) * c * c⁻¹ := by rw [hcm]
          _ = ψ ⟨x, hx⟩ * ψ w * (ψ ⟨x, hx⟩)⁻¹ := by group
      rw [heq]
      exact hxw
    have hN2 : ((T ⊓ C).subgroupOf (E ⊓ C)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right C hTE)]
      rintro h k ⟨hhT, hhC⟩ ⟨hkE, hkC⟩
      exact ⟨hETn k hkE h hhT, C.mul_mem (C.mul_mem hkC hhC) (C.inv_mem hkC)⟩
    have hN3 : ((E ⊓ C).subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      rintro h k ⟨hhE, hhC⟩ hkC
      exact ⟨hEnorm.conj_mem h hhE k, C.mul_mem (C.mul_mem hkC hhC) (C.inv_mem hkC)⟩
    have hchain : IsSubnormal Δ C :=
      IsSubnormal.step (le_inf hΔT hΔC) hN1
        (IsSubnormal.step (inf_le_inf_right C hTE) hN2
          (IsSubnormal.step inf_le_right hN3 (IsSubnormal.refl C)))
    have h1 : IsSubnormal (Δ.subgroupOf C) ⊤ :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hΔC).mpr hchain
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h1
      Subgroup.IsSubnormal.top

end Diagonal

end CFSG.ClassicalInvolution.Balance.LocalBalance
