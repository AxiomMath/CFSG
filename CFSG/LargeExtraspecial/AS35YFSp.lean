module

public import CFSG.LargeExtraspecial.AS35YFSym
public import CFSG.LargeExtraspecial.S12InspFamESpCore
public import CFSG.LargeExtraspecial.S12InspFamESpOut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

namespace AS35YF

open S12InspSp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

theorem rad_comm (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {v : ι → ZMod 2}
    (hv : v ≠ 0) {k k' : SpG b} (hk : k ∈ rad b v) (hk' : k' ∈ rad b v) : k * k' = k' * k := by
  obtain ⟨y, hyv⟩ := exists_b_eq_one halt hnd hv
  have key : ∀ (k₁ k₂ : SpG b), k₁ ∈ rad b v → k₂ ∈ rad b v → ∀ (x₀ : ι → ZMod 2) (c : ZMod 2),
      b x₀ v = 0 → act (k₁ * k₂) (x₀ + c • y) = x₀ + c • y + c • (uvec b y k₁ + uvec b y k₂) +
        (b x₀ (uvec b y k₁) + b x₀ (uvec b y k₂) + c * b (uvec b y k₂) (uvec b y k₁)) • v := by
    intro k₁ k₂ hk₁ hk₂ x₀ c hx₀v
    have h₁v : act k₁ v = v := (mem_rad.1 hk₁).1
    have hu₂ : b (uvec b y k₂) v = 0 := b_uvec_v (mem_rad.1 hk₂).1
    have a2 : act k₂ (x₀ + c • y) =
        x₀ + b x₀ (uvec b y k₂) • v + c • (y + uvec b y k₂) := by
      rw [act_add, act_smul, act_eq_of_mem_rad halt hyv hk₂ hx₀v, act_y_eq (y := y) k₂]
    have a1 : act k₁ (x₀ + b x₀ (uvec b y k₂) • v + c • (y + uvec b y k₂)) =
        (x₀ + b x₀ (uvec b y k₁) • v) + b x₀ (uvec b y k₂) • v +
          c • ((y + uvec b y k₁) + (uvec b y k₂ + b (uvec b y k₂) (uvec b y k₁) • v)) := by
      rw [act_add, act_add, act_smul, act_smul, act_add, act_eq_of_mem_rad halt hyv hk₁ hx₀v,
        h₁v, act_y_eq (y := y) k₁, act_eq_of_mem_rad halt hyv hk₁ hu₂]
    rw [act_mul, a2, a1]
    module
  apply act_ext
  intro x
  set c := b x v with hc
  have hx₀v : b (x + c • y) v = 0 := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hyv, mul_one, ← hc,
      add_self_zmod2]
  have hx : x = (x + c • y) + c • y := by
    rw [add_assoc, ← add_smul, add_self_zmod2, zero_smul, add_zero]
  rw [hx, key k k' hk hk' _ c hx₀v, key k' k hk' hk _ c hx₀v,
    b_symm halt (uvec b y k') (uvec b y k)]
  module

theorem comm_of_normalized (h4 : 4 < Fintype.card ι) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {T : SpG b} {v : ι → ZMod 2} (hv : v ≠ 0)
    (hT : ∀ x, act T x = x + b x v • v) {N : Subgroup (SpG b)} (hN2 : IsPGroup 2 N)
    (hNC : ∀ x ∈ N, x * T = T * x)
    (hNn : ∀ c : SpG b, c * T = T * c → ∀ x ∈ N, c * x * c⁻¹ ∈ N) :
    ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hpair : ∀ a z, b a v = 0 → a ≠ 0 → a ≠ v → b z v = 0 → z ≠ 0 → z ≠ v →
      tr halt a * tr halt z ∈ Subgroup.normalizer (N : Set (SpG b)) := by
    intro a z ha _ _ hz _ _
    have hc : tr halt a * tr halt z ∈ Subgroup.centralizer {T} :=
      mul_mem (tr_mem_centralizer halt hT ha) (tr_mem_centralizer halt hT hz)
    have hc' := mem_centralizer_singleton_iff.mp hc
    have hci : (tr halt a * tr halt z)⁻¹ * T = T * (tr halt a * tr halt z)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc', mul_assoc, mul_inv_cancel, mul_one]
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hNn _ hc' n hn, fun hn => ?_⟩
    have := hNn _ hci _ hn
    rwa [show (tr halt a * tr halt z)⁻¹ * ((tr halt a * tr halt z) * n *
      (tr halt a * tr halt z)⁻¹) * (tr halt a * tr halt z)⁻¹⁻¹ = n by group] at this
  have hle := le_rad halt hnd h4 hv hT
    (fun x hx => mem_centralizer_singleton_iff.mpr (hNC x hx)) hN2 hpair
  intro x hx y hy
  exact rad_comm halt hnd hv (hle hx) (hle hy)

theorem mem_inner_of_card_outer {Y : Type*} [Group Y] (h : Nat.card (Outer Y) = 1)
    (α : MulAut Y) : α ∈ inner Y := by
  have : Subsingleton (Outer Y) := (Nat.card_eq_one_iff_unique.mp h).1
  rw [← QuotientGroup.eq_one_iff]
  exact Subsingleton.elim _ _

end AS35YF

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_sp (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (φ : S.LbarAsc ⧸ center S.LbarAsc ≃* S12InspSp.SpG b)
    {v : Fin (2 * m) → ZMod 2} (hv0 : v ≠ 0)
    (hT : ∀ x, S12InspSp.act (φ (QuotientGroup.mk (ascTL htD htM))) x = x + b x v • v) :
    False := by
  have hinn : ∀ α : MulAut (S.LbarAsc ⧸ center S.LbarAsc),
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ :=
    asc_mem_inner_of_equiv φ (AS35YF.mem_inner_of_card_outer
      (S12InspSp.card_outer_SpG hm halt hnd))
  have hle := asc_Pbar_le_Lbar_of_inner hst hP hS htD htM (fun p _ => hinn _)
  obtain ⟨a, ha, c, hc, hac⟩ := ascPhat_not_comm_of_le hst hP hS htD htM hle
  have hA := (ascImage_ascPhat hst hP hS htD htM).map φ
  have h4 : 4 < Fintype.card (Fin (2 * m)) := by rw [Fintype.card_fin]; omega
  have hcomm := AS35YF.comm_of_normalized h4 halt hnd hv0 hT hA.isPGroup hA.commute hA.normal
    (φ a) ⟨a, ha, rfl⟩ (φ c) ⟨c, hc, rfl⟩
  exact hac (φ.injective ((map_mul φ a c).trans (hcomm.trans (map_mul φ c a).symm)))

end Setting

end CFSG.LargeExtraspecial
