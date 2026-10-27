module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

structure SylowA {G : Type} [Group G] {A : Subgroup G} (d : Datum A) {F : Type} [Field F]
    [Finite F] [CharP F 2] (W S₁ S₀ W₀ : Subgroup G) (ι : G → F × F) (κ : G → F)
    (φ : G → RingAut F) : Prop where
  card_F : Nat.card F = 16
  sylow_S₁ : IsSylowOf 2 S₁ (normalizer (W : Set G))
  S₀_le_S₁ : S₀ ≤ S₁
  S₀_normal : ∀ s ∈ S₁, ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀
  W_le_S₀ : W ≤ S₀
  V_le_S₀ : d.P ⊓ A ≤ S₀
  t_mem_S₁ : d.t ∈ S₁
  t_not_mem_S₀ : d.t ∉ S₀
  ι_add : ∀ w ∈ W, ∀ w' ∈ W, ι (w * w') = ι w + ι w'
  ι_inj : ∀ w ∈ W, ∀ w' ∈ W, ι w = ι w' → w = w'
  ι_surj : ∀ p : F × F, ∃ w ∈ W, ι w = p
  κ_add : ∀ s ∈ S₀, ∀ s' ∈ S₀, κ (s * s') = κ s + κ s'
  κ_eq_zero_iff : ∀ s ∈ S₀, κ s = 0 ↔ s ∈ W
  κ_surj : ∀ b : F, ∃ s ∈ S₀, κ s = b
  conj_ι : ∀ s ∈ S₀, ∀ w ∈ W, ι (s * w * s⁻¹) = ((ι w).1 + κ s * (ι w).2, (ι w).2)
  φ_mul : ∀ x ∈ S₁, ∀ y ∈ S₁, φ (x * y) = φ x * φ y
  φ_eq_one_iff : ∀ x ∈ S₁, φ x = 1 ↔ x ∈ S₀
  conj_κ : ∀ x ∈ S₁, ∃ l : F, l ≠ 0 ∧ ∀ s ∈ S₀, κ (x * s * x⁻¹) = l * φ x (κ s)
  W₀_eq : W₀ = W ⊓ centralizer (S₀ : Set G)
  comm_mem_W₀ : ∀ s ∈ S₀, ∀ s' ∈ S₀, s * s' * s⁻¹ * s'⁻¹ ∈ W₀
  card_fix_le : ∀ s ∈ S₁, s ∉ S₀ → Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ 16
  free : FreeSeries (MulAut.conj d.t) S₀

end CFSG.OddStandard.Seitz77
