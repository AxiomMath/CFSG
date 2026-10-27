module

public import CFSG.LargeExtraspecial.S8Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Group

variable {X : Type*} [Group X]

theorem conj_comm_eq_of_mem {C : Subgroup X} (hC : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    {a b n : X} (hca : ∀ c ∈ C, c * a = a * c) (hcb : ∀ c ∈ C, c * b = b * c)
    (ha : a * n * a⁻¹ * n⁻¹ ∈ C) (hb : b * n * b⁻¹ * n⁻¹ ∈ C) :
    (a * b * a⁻¹ * b⁻¹) * n * (a * b * a⁻¹ * b⁻¹)⁻¹ = n := by
  set ca := a * n * a⁻¹ * n⁻¹ with hca'
  set cb := b * n * b⁻¹ * n⁻¹ with hcb'
  have e1 : ∀ {x c : X}, c * x = x * c → ∀ m : X, x * (c * m) * x⁻¹ = c * (x * m * x⁻¹) := by
    intro x c hx m
    calc x * (c * m) * x⁻¹ = (x * c) * m * x⁻¹ := by group
      _ = (c * x) * m * x⁻¹ := by rw [hx]
      _ = c * (x * m * x⁻¹) := by group
  have e2 : ∀ {x c : X}, c * x = x * c → ∀ m : X, x⁻¹ * (c * m) * x = c * (x⁻¹ * m * x) := by
    intro x c hx m
    have hx' : c * x⁻¹ = x⁻¹ * c := by
      calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
        _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * c := by group
    calc x⁻¹ * (c * m) * x = (x⁻¹ * c) * m * x := by group
      _ = (c * x⁻¹) * m * x := by rw [hx']
      _ = c * (x⁻¹ * m * x) := by group
  have ea : a * n * a⁻¹ = ca * n := by rw [hca']; group
  have eb : b * n * b⁻¹ = cb * n := by rw [hcb']; group
  have ea' : a⁻¹ * n * a = ca⁻¹ * n := by
    have h1 : a⁻¹ * (ca * n) * a = n := by rw [← ea]; group
    rw [e2 (hca _ ha)] at h1
    calc a⁻¹ * n * a = ca⁻¹ * (ca * (a⁻¹ * n * a)) := by group
      _ = ca⁻¹ * n := by rw [h1]
  have eb' : b⁻¹ * n * b = cb⁻¹ * n := by
    have h1 : b⁻¹ * (cb * n) * b = n := by rw [← eb]; group
    rw [e2 (hcb _ hb)] at h1
    calc b⁻¹ * n * b = cb⁻¹ * (cb * (b⁻¹ * n * b)) := by group
      _ = cb⁻¹ * n := by rw [h1]
  have hcbi : cb⁻¹ ∈ C := C.inv_mem hb
  have hcai : ca⁻¹ ∈ C := C.inv_mem ha
  calc (a * b * a⁻¹ * b⁻¹) * n * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        a * (b * (a⁻¹ * (b⁻¹ * n * b) * a) * b⁻¹) * a⁻¹ := by group
    _ = a * (b * (a⁻¹ * (cb⁻¹ * n) * a) * b⁻¹) * a⁻¹ := by rw [eb']
    _ = a * (b * (cb⁻¹ * (ca⁻¹ * n)) * b⁻¹) * a⁻¹ := by rw [e2 (hca _ hcbi), ea']
    _ = a * (cb⁻¹ * (ca⁻¹ * (cb * n))) * a⁻¹ := by
        rw [e1 (hcb _ hcbi), e1 (hcb _ hcai), eb]
    _ = cb⁻¹ * (ca⁻¹ * (cb * (ca * n))) := by
        rw [e1 (hca _ hcbi), e1 (hca _ hcai), e1 (hca _ hb), ea]
    _ = n := by
        rw [← mul_assoc ca⁻¹ cb, hC _ hcai _ hb]
        group

end Group

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

omit [Finite G] in
theorem apply_comm_eq_of_mem_Wt {V W : Submodule (ZMod 2) S.Qt} {x y : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hxV : ∀ v ∈ V, x v = v) (hyV : ∀ v ∈ V, y v = v) (hxW : ∀ w ∈ W, x w - w ∈ V)
    (hyW : ∀ w ∈ W, y w - w ∈ V) (hyWW : ∀ w ∈ W, y w ∈ W) {w : S.Qt} (hw : w ∈ W) :
    x (y w) = y (x w) := by
  have h1 := hxW _ (hyWW w hw)
  have h2 := hyW w hw
  have h3 := hxW w hw
  have e1 : x (y w) = y w + (x (y w) - y w) := by abel
  have e2 : y (x w) = y w + y (x w - w) := by rw [map_sub]; abel
  rw [e1, e2, hyV _ h3]
  have e3 : x (y w) - y w = (x w - w) + (x (y w - w) - (y w - w)) := by rw [map_sub]; abel
  rw [e3, hxV _ h2, sub_self, add_zero]

theorem comm_apply_eq_of_comm {W : Submodule (ZMod 2) S.Qt} {x y : S.O}
    (hxW : ∀ w ∈ W, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hyW : ∀ w ∈ W, ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hc : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
    {w : S.Qt} (hw : w ∈ W) : ((x * y * x⁻¹ * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hu := hxW _ (hyW w hw)
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) = w
  rw [hc _ hu, apply_inv_apply_O, apply_inv_apply_O]

theorem apply_mem_Wt_of_commute (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O} (hxt : x * t = t * x) {w : S.Qt}
    (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := by
  have hW := (commSpace_t_eq H C ht ht1 hVQ).2
  rw [← hW] at hw ⊢
  rw [mem_fixSpace] at hw ⊢
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← hxt, Subgroup.coe_mul,
    LinearEquiv.mul_apply, hw]

section Five

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : PairGen S g t) (hN0 : Nbar S g t = N0bar S g t)
  (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t))
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
include H C ht ht1 hVQ hgen hN0 h3 hN

theorem comm_mem_zpowers_of_mem_Nbar {τ : S.O} (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτW : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {n : S.O} (hn : n ∈ Nbar S g t) : τ * n * τ⁻¹ * n⁻¹ ∈ zpowers t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hτM
  have hc : S.ρ k * n * (S.ρ k)⁻¹ * n⁻¹ ∈ Nbar S g t :=
    mul_mem (conj_mem_Nbar H.conj_mem hτt hn) (inv_mem hn)
  refine mem_zpowers_of_mem_Nbar_of_fix_Wt H C ht ht1 hVQ hgen hN0 h3 hc fun w hw => ?_
  have hτt' : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hτt]
      _ = t * (S.ρ k)⁻¹ := by group
  refine comm_apply_eq_of_comm (W := Wt S g t)
    (fun w hw => apply_mem_Wt_of_commute H C ht ht1 hVQ hτt' hw)
    (fun w hw => apply_mem_Wt H (inv_mem (Nbar_le_Rbar hn)) hw) (fun w hw => ?_) hw
  exact apply_comm_eq_of_mem_Wt hτV (mem_Nbar.mp hn).2 hτW (hN n hn)
    (fun w hw => apply_mem_Wt H (Nbar_le_Rbar hn) hw) hw

end Five

end CFSG.LargeExtraspecial.S8
