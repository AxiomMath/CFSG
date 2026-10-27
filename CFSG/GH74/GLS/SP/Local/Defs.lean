module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.LU.Compat
public import CFSG.GH74.GLS.LU.Local.Defs

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open CFSG.GH74.GLS.LU.Local

structure SPSyl (G : Type) [Group G] (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t : G) : Prop where
  z_inv : orderOf z = 2
  z_cen : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z
  t_mem : t ∈ (S : Subgroup G)
  t_ord : orderOf t = 2
  t_swap : K₁.map (MulAut.conj t).toMonoidHom = K₂
  t_nconj : ¬ IsConj z t
  tz_conj : IsConj z (t * z)
  K_one_class : ∀ x ∈ K₁ ⊔ K₂, ∀ y ∈ K₁ ⊔ K₂, orderOf x = 2 → orderOf y = 2 → x ≠ z → y ≠ z →
    ∃ k ∈ K₁ ⊔ K₂, k * x * k⁻¹ = y
  K_inv_t : ∃ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), orderOf x = 2 ∧ x ≠ z ∧ IsConj t x
  index : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂))

theorem SPSyl.inv_K {G : Type} [Group G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t : G}
    (h : SPSyl G z S K₁ K₂ t) {x : G} (hx : x ∈ K₁ ⊔ K₂) (hx2 : orderOf x = 2) (hxz : x ≠ z) :
    IsConj t x := by
  obtain ⟨x₀, hx₀, hx₀2, hx₀z, hx₀t⟩ := h.K_inv_t
  obtain ⟨k, hk, hkx⟩ := h.K_one_class x₀ hx₀.2 x hx hx₀2 hx2 hx₀z hxz
  exact hx₀t.trans (isConj_iff.mpr ⟨k, hkx⟩)

structure SPModelData (Gs : Type) [Group Gs] (q : ℕ) (z' : Gs) (S' : Sylow 2 Gs)
    (E₁ E₂ : Subgroup Gs) (t' : Gs) : Prop where
  comps : LUComps Gs q z' E₁ E₂
  syl : SPSyl Gs z' S' E₁ E₂ t'

@[expose] def SPModelLeaf : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (F : Type) [Field F] [Finite F], 4 ≤ Nat.card F →
    Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
    ∀ (S' : Sylow 2 Gs) (z' : Gs),
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      ∃ (E₁ E₂ : Subgroup Gs) (t' : Gs), SPModelData Gs (Nat.card F) z' S' E₁ E₂ t'

@[expose] def SPSetupLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (Gs : Type) [Group Gs] (F : Type) [Field F]
    [Finite F], 4 ≤ Nat.card F → Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
    LU.IsTwoCentralClassicalTypeCompat G Gs →
    ∃ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t : G),
      LUComps G (Nat.card F) z K₁ K₂ ∧ SPSyl G z S K₁ K₂ t ∧ pPrimeCoreOf 2 (Cz z) = ⊥

end CFSG.GH74.GLS.SP.Local
