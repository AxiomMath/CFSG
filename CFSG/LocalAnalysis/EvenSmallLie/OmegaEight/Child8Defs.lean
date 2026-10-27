module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhCaseOne
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

structure Child8Weyl (W : Type) [Group W] [Finite W] where
  Wp : Subgroup W
  z : W
  s : W
  T : Subgroup W
  ιE : Multiplicative evenSub →* W
  ιE1 : Multiplicative FrameVec →* W
  x₀ : W
  s₁ : W
  s₂ : W
  normal : Wp.Normal
  perfect : commutator Wp = ⊤
  card_center : Nat.card (center Wp) = 2
  lieModel : CFSG.Blueprint.LieModel (Wp ⧸ center Wp) .POmegaPlus 4 2 1
  aut : ∀ φ : MulAut Wp, ∃ w : W, ∀ x : Wp, (φ x : W) = w * x * w⁻¹
  fours : FoursGroupCondition Wp
  z_mem : z ∈ Wp
  z_comm : ∀ w : W, w * z = z * w
  z_ne_one : z ≠ 1
  s_not_mem : s ∉ Wp
  s_mul_self : s * s = 1
  mem_or_mul_mem : ∀ w : W, w ∈ Wp ∨ w * s ∈ Wp
  mul_self_ne : ∀ w ∈ Wp, w * s * (w * s) ≠ z
  card_W : Nat.card W = 2 ^ 14 * 42525
  card_T : Nat.card T = 2 ^ 14
  card_Tp : Nat.card (T ⊓ Wp : Subgroup W) = 2 ^ 13
  center_T : ∀ t ∈ T, (∀ u ∈ T, t * u = u * t) → t = 1 ∨ t = z
  center_Tp : ∀ t ∈ T ⊓ Wp, (∀ u ∈ T ⊓ Wp, t * u = u * t) → t = 1 ∨ t = z
  ιE_injective : Function.Injective ιE
  ιE_evenZ : ιE (Multiplicative.ofAdd evenZ) = z
  ιE_mem : ∀ v, ιE v ∈ T ⊓ Wp
  E_up : ∀ w ∈ Wp, (∀ v, w * ιE v * w⁻¹ ∈ ιE.range) → ∃ σ ∈ alternatingGroup (Fin 8),
    ∀ v, w * ιE v * w⁻¹ = ιE (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v)))
  E_down : ∀ σ ∈ alternatingGroup (Fin 8), ∃ w ∈ Wp,
    ∀ v, w * ιE v * w⁻¹ = ιE (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v)))
  centralizer_E : ∀ w : W, (∀ v, w * ιE v = ιE v * w) → w ∈ ιE.range
  ιE1_injective : Function.Injective ιE1
  ιE1_frameZ : ιE1 (Multiplicative.ofAdd frameZ) = z
  ιE1_mem_T : ∀ v, ιE1 v ∈ T
  ιE1_mem_iff : ∀ v : FrameVec, ιE1 (Multiplicative.ofAdd v) ∈ Wp ↔ v ∈ evenSub
  s_mem : s ∈ ιE1.range
  frame_gens : ∀ σ ∈ frameGens, ∃ w ∈ Wp, ∀ v : FrameVec,
    w * ιE1 (Multiplicative.ofAdd v) * w⁻¹ = ιE1 (Multiplicative.ofAdd (permVec σ v))
  frame_up : ∀ w : W, (∀ v, w * ιE1 v * w⁻¹ ∈ ιE1.range) → ∃ σ ∈ frameAut, ∀ v : FrameVec,
    w * ιE1 (Multiplicative.ofAdd v) * w⁻¹ = ιE1 (Multiplicative.ofAdd (permVec σ v))
  centralizer_E1p : ∀ w : W,
    (∀ v ∈ evenSub, w * ιE1 (Multiplicative.ofAdd v) = ιE1 (Multiplicative.ofAdd v) * w) →
      w ∈ ιE1.range
  reps_mem : ∀ v ∈ ({frameE 0 + frameE 1, blockVec {0, 1, 2, 3},
    frameZ + frameE 0 + frameE 1} : Set FrameVec), ιE1 (Multiplicative.ofAdd v) ∈ ιE.range
  not_conj : ∀ w ∈ Wp, ¬ ∀ v, w * ιE v * w⁻¹ ∈ ιE1.range
  elem_Tp : ∀ B : Subgroup W, B ≤ T ⊓ Wp → (∀ b ∈ B, b * b = 1) → Nat.card B = 2 ^ 7 →
    B = ιE.range ∨ B = ιE1.range ⊓ Wp
  elem_T : ∀ B : Subgroup W, B ≤ T → (∀ b ∈ B, b * b = 1) → Nat.card B = 2 ^ 8 → B = ιE1.range
  inv_Wp : ∀ y ∈ Wp, y * y = 1 → ∃ w ∈ Wp, w * y * w⁻¹ ∈ ιE1.range
  inv_W : ∀ y : W, y * y = 1 → ∃ w : W, w * y * w⁻¹ ∈ ιE1.range
  x₀_eq : x₀ = ιE1 (Multiplicative.ofAdd (blockVec {0, 1, 2, 3}))
  normal_four : ∀ v ∈ T, v * v = 1 → (∀ t ∈ T, t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * z) →
    v = 1 ∨ v = x₀ ∨ v = z ∨ v = x₀ * z
  card_C : Nat.card (T ⊓ centralizer ({x₀} : Set W) : Subgroup W) = 2 ^ 13
  center_C : ∀ c ∈ T ⊓ centralizer ({x₀} : Set W),
    (∀ d ∈ T ⊓ centralizer ({x₀} : Set W), c * d = d * c) → c = 1 ∨ c = x₀ ∨ c = z ∨ c = x₀ * z
  s₁_mem : s₁ ∈ T ⊓ centralizer ({x₀} : Set W)
  s₂_mem : s₂ ∈ T ⊓ centralizer ({x₀} : Set W)
  zc_s₁ : ∀ d ∈ T ⊓ centralizer ({x₀} : Set W), s₁ * d * s₁⁻¹ * d⁻¹ ∈ ιE1.range
  zc_s₂ : ∀ d ∈ T ⊓ centralizer ({x₀} : Set W), s₂ * d * s₂⁻¹ * d⁻¹ ∈ ιE1.range
  zc : ∀ c ∈ T ⊓ centralizer ({x₀} : Set W),
    (∀ d ∈ T ⊓ centralizer ({x₀} : Set W), c * d * c⁻¹ * d⁻¹ ∈ ιE1.range) →
      c ∈ ιE1.range ∨ s₁⁻¹ * c ∈ ιE1.range ∨ s₂⁻¹ * c ∈ ιE1.range ∨
        (s₁ * s₂)⁻¹ * c ∈ ιE1.range
  s₁_not_mem : s₁ ∉ ιE1.range
  s₂_not_mem : s₂ ∉ ιE1.range
  inv_mul_not_mem : s₁⁻¹ * s₂ ∉ ιE1.range
  card_ne₁ : Nat.card (ιE1.range ⊓ centralizer ({s₁} : Set W) : Subgroup W) ≠
    Nat.card (ιE1.range ⊓ centralizer ({s₁ * s₂} : Set W) : Subgroup W)
  card_ne₂ : Nat.card (ιE1.range ⊓ centralizer ({s₂} : Set W) : Subgroup W) ≠
    Nat.card (ιE1.range ⊓ centralizer ({s₁ * s₂} : Set W) : Subgroup W)
  comm_eq : ∃ e ∈ ιE1.range, e * s₁ * e⁻¹ * s₁⁻¹ = x₀
  comm_ne : ∀ e ∈ ιE1.range, e * s₁ * e⁻¹ * s₁⁻¹ ≠ z ∧ e * s₁ * e⁻¹ * s₁⁻¹ ≠ x₀ * z

end CFSG.EvenSmallLie.OmegaEight.Child8
