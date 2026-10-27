module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Leaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Notation3

variable {G : Type} [Group G]

@[expose] def zCenter (H : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ H ∧ ∀ h ∈ H, h * z = z * h}
  one_mem' := ⟨H.one_mem, fun h _ => by rw [mul_one, one_mul]⟩
  mul_mem' := by
    rintro a b ⟨haH, hac⟩ ⟨hbH, hbc⟩
    refine ⟨H.mul_mem haH hbH, fun h hh => ?_⟩
    rw [← mul_assoc, hac h hh, mul_assoc, hbc h hh, ← mul_assoc]
  inv_mem' := by
    rintro a ⟨haH, hac⟩
    refine ⟨H.inv_mem haH, fun h hh => ?_⟩
    have h1 := hac h hh
    calc h * a⁻¹ = a⁻¹ * (a * h) * a⁻¹ := by group
      _ = a⁻¹ * (h * a) * a⁻¹ := by rw [← h1]
      _ = a⁻¹ * h := by group

@[expose] def omega1 (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {u : G | u ∈ H ∧ u * u = 1}

@[expose] def thompsonJ2 (T : Subgroup G) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : A ≤ T ∧ CFSG.IsElementaryAbelian 2 ↥A ∧
    ∀ B : Subgroup G, B ≤ T → CFSG.IsElementaryAbelian 2 ↥B → Nat.card ↥B ≤ Nat.card ↥A), A

@[expose] def layerI (K : Subgroup G) (f : G) : Subgroup G :=
  pLayerOf 2 (K ⊓ centralizer ({f} : Set G))

@[expose] def pumpJ (K : Subgroup G) (f : G) : Subgroup G := pumpUp 2 K f

@[expose] def secD (K : Subgroup G) (f : G) (V : Subgroup G) : Subgroup G :=
  V ⊓ centralizerSection (layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)) (pPrimeCoreOf 2 (pumpJ K f))

@[expose] def IsDihedralMaxIn (P₀ P : Subgroup G) : Prop :=
  P₀ ≤ P ∧ Nat.card ↥P = 2 * Nat.card ↥P₀ ∧ IVK.IsDihedralOrder ↥P₀ (Nat.card ↥P₀)

structure Cfg3 (x y : G) (K T V W : Subgroup G) (f z : G) : Prop where
  fmax : FMax3 x y K f
  setup : Setup1D x K T
  mem : IsFMember x K T f
  z_mem : z ∈ T ⊓ K ∧ orderOf z = 2 ∧ ∀ t ∈ T, t * z = z * t
  sylowV : IsSylowOf 2 V (centralizer ({f} : Set G))
  CTf_le : ∀ t ∈ T, f * t = t * f → t ∈ V
  sylowW : IsSylowOf 2 W ⊤
  V_le_W : V ≤ W

end Notation3

end CFSG.GH74.GLS
