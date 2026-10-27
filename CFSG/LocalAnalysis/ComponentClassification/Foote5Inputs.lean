module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.FooteLit

@[expose] def FooteSimpleType (𝕊 : Type) [Group 𝕊] : Prop :=
  Nonempty (𝕊 ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel 𝕊 .PSL 2 p f

abbrev innAut5 (𝕊 : Type) [Group 𝕊] : Subgroup (MulAut 𝕊) :=
  (MulAut.conj : 𝕊 →* MulAut 𝕊).range

structure Foote5AutData (𝕊 : Type) [Group 𝕊] [Finite 𝕊] (Lin : Subgroup (MulAut 𝕊)) :
    Prop where
  inn_le : innAut5 𝕊 ≤ Lin
  normal : Lin.Normal
  sq_mem : ∀ α ∈ Lin, α * α ∈ innAut5 𝕊
  commutator_mem : ∀ α β : MulAut 𝕊, α * β * α⁻¹ * β⁻¹ ∈ innAut5 𝕊
  conj_involution : ∀ x y : 𝕊, orderOf x = 2 → orderOf y = 2 → ∃ g : 𝕊, g⁻¹ * x * g = y
  centralizer_sylow : ∀ (R : Sylow 2 𝕊) (P : Subgroup (MulAut 𝕊)), IsPGroup 2 P →
    (∀ α ∈ P, ∀ r ∈ (R : Subgroup 𝕊), α r = r) → (∀ α ∈ P, α * α = 1) ∧ Nat.card P ≤ 4
  centralizer_sylow_lin : ∀ R : Sylow 2 𝕊, (∃ a ∈ (R : Subgroup 𝕊), ∃ b ∈ (R : Subgroup 𝕊),
      a * b ≠ b * a) → ∀ α ∈ Lin, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      (∀ r ∈ (R : Subgroup 𝕊), α r = r) →
        ∃ c ∈ (R : Subgroup 𝕊), (∀ r ∈ (R : Subgroup 𝕊), c * r = r * c) ∧ α = MulAut.conj c
  not_commute : ∀ α β : MulAut 𝕊, α ∈ Lin → α ∉ innAut5 𝕊 → α * α = 1 → β ∉ Lin →
    β * β = 1 → α * β ≠ β * α
  conj_centralizer : ∀ (R : Sylow 2 𝕊) (β : MulAut 𝕊), β ∉ Lin → β * β = 1 →
    ∃ g : 𝕊, ∀ r ∈ (R : Subgroup 𝕊), (MulAut.conj g * β * (MulAut.conj g)⁻¹) r = r
  pgl_fixed : ∀ (R : Sylow 2 𝕊) (α : MulAut 𝕊), α ∈ Lin → α ∉ innAut5 𝕊 → α * α = 1 →
    (R : Subgroup 𝕊).map α.toMonoidHom = R →
      Nat.card ↥((R : Subgroup 𝕊) ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id 𝕊)) ≤ 2
  field_inner : ∀ (R : Sylow 2 𝕊) (β : MulAut 𝕊), β ∉ Lin → β * β = 1 →
    (R : Subgroup 𝕊).map β.toMonoidHom = R →
      ∃ r₀ ∈ (R : Subgroup 𝕊), r₀ * r₀ = 1 ∧ ∀ r ∈ (R : Subgroup 𝕊), β r = r₀ * r * r₀⁻¹
  center_le : ∀ R : Sylow 2 𝕊, (∃ a ∈ (R : Subgroup 𝕊), ∃ b ∈ (R : Subgroup 𝕊), a * b ≠ b * a) →
    ∀ X : Subgroup (MulAut 𝕊), IsPGroup 2 X →
      (R : Subgroup 𝕊).map (MulAut.conj : 𝕊 →* MulAut 𝕊) ≤ X →
      ∀ R₁ : Subgroup (MulAut 𝕊), R₁ ≤ X → Nonempty (R₁ ≃* (R : Subgroup 𝕊)) →
        ∀ c ∈ R₁, (∀ d ∈ R₁, c * d = d * c) →
          ∃ r ∈ (R : Subgroup 𝕊), (∀ s ∈ (R : Subgroup 𝕊), r * s = s * r) ∧ c = MulAut.conj r
  two_generated : ∀ R : Sylow 2 𝕊, (∀ a ∈ (R : Subgroup 𝕊), ∀ b ∈ (R : Subgroup 𝕊),
      a * b = b * a) → ∀ P : Subgroup (MulAut 𝕊), IsPGroup 2 P →
        ∃ s : Finset (MulAut 𝕊), s.card ≤ 2 ∧ closure (s : Set (MulAut 𝕊)) = P

@[expose] def Foote5AutStructure : Prop :=
  ∀ (𝕊 : Type) [Group 𝕊] [Finite 𝕊], FooteSimpleType 𝕊 →
    ∃ Lin : Subgroup (MulAut 𝕊), Foote5AutData 𝕊 Lin

variable {G : Type} [Group G]

@[expose] def GoldschmidtCorB4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G), AschbacherTheorem3.IsDihedralTwoGroup D →
    (∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) →
    ∀ P : Subgroup G, ABGLocalTools.IsSylowOf 2 P (normalClosure (D : Set G)) →
      ∀ E : Subgroup G, E ≤ P → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4

@[expose] def IsFooteComponent (L : Subgroup G) [Finite G] : Prop :=
  (∃ t : G, IsTwoComponentAt t L) ∧ FooteFamilyType L ∧ CFSG.pRank 2 ↥L = 2

@[expose] def Foote5KnownGroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ L : Subgroup G, IsFooteComponent L →
    (Nonempty (G ≃* alternatingGroup (Fin 9)) →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) ∧
    (Nonempty (G ≃* alternatingGroup (Fin 10)) →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6))) ∧
    (Nonempty (G ≃* alternatingGroup (Fin 11)) →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))) ∧
    (Blueprint.NativeSporadic.IsSporadic G .J2 →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) ∧
    ((Blueprint.LieModel G .PSL 2 2 3 ∨ Blueprint.LieModel G .PSL 2 2 4 ∨
        Blueprint.LieModel G .PSL 3 2 2 ∨ Blueprint.LieModel G .twistedB2 0 2 3 ∨
        Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
        Blueprint.NativeSporadic.IsSporadic G .M12 ∨ Blueprint.NativeSporadic.IsSporadic G .M22 ∨
        Blueprint.NativeSporadic.IsSporadic G .M23 ∨ Blueprint.NativeSporadic.IsSporadic G .J1 ∨
        Blueprint.NativeSporadic.IsSporadic G .J3 ∨ Blueprint.NativeSporadic.IsSporadic G .McL ∨
        Blueprint.NativeSporadic.IsSporadic G .Ly) →
      CFSG.pRank 2 ↥(coreActionKernel L) ≤ 1)

end CFSG.ComponentClassification.Foote5
