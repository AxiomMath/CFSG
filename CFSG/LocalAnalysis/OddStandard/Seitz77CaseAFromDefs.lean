module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open Matrix MatrixGroups

structure ModInput {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)
    (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (ρ : ↥(normalizer (Wl : Set G)) →* GL (Fin 8) (ZMod 2))
    (Hgl Xgl : Subgroup (GL (Fin 8) (ZMod 2))) : Prop where
  elem : IsElemAbelian 2 Wl
  card : Nat.card Wl = 2 ^ 8
  sylow_C : CFSG.ABGLocalTools.IsSylowOf 2 Wl (centralizer (Wl : Set G))
  act : ∀ (n : ↥(normalizer (Wl : Set G))) (w w' : ↥Wl), (w' : G) = n * w * n⁻¹ →
    κ₀ w' = Multiplicative.ofAdd
      ((ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w)))
  Hgl_norm : ∀ n : ↥(normalizer (Wl : Set G)), ∀ g ∈ Hgl, ρ n * g * (ρ n)⁻¹ ∈ Hgl
  Hgl_le_range : Hgl ≤ ρ.range
  Hgl_iso : Nonempty (SL(2, GaloisField 2 4) ≃* ↥Hgl)
  Xgl_le : Xgl ≤ Hgl
  Xgl_card : Nat.card Xgl = 60
  Xgl_fpf : ∀ y ∈ Xgl, orderOf y = 3 → ∀ v : Fin 8 → ZMod 2,
    (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v → v = 0
  V_le : d.P ⊓ A ≤ normalizer (Wl : Set G)
  V_mem : ∀ (v : G) (hv : v ∈ d.P ⊓ A), ρ ⟨v, V_le hv⟩ ∈ Hgl
  t_mem : d.t ∈ normalizer (Wl : Set G)
  t_comm : ∀ y ∈ Xgl, y * ρ ⟨d.t, t_mem⟩ = ρ ⟨d.t, t_mem⟩ * y
  t_ne : ρ ⟨d.t, t_mem⟩ ≠ 1

end CFSG.OddStandard.Seitz77
