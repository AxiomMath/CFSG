module

public import CFSG.GH74.GLS.IVK.Statements.Sec32
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def pull (z : G) (S : Subgroup G) (X : Subgroup (CentralizerBar z)) : Subgroup G :=
  S ⊓ (X.comap (toBar z)).map (Cen z).subtype

structure AbsData (z : G) (S K₁ K₂ : Subgroup G) (a : G) (haC : a ∈ Cen z)
    (Y A : Subgroup (CentralizerBar z)) (r : ℕ) : Prop where
  Ca : IVK.Prod3.Ca (barOf z S) (barOf z K₁) (barOf z K₂) (toBar z ⟨a, haC⟩)
  Y_le : Y ≤ IVK.Prod3.T1 (barOf z S) (barOf z K₁)
  A_le : A ≤ IVK.Prod3.T1 (barOf z S) (barOf z K₁)
  prod : Y ⊔ A = IVK.Prod3.T1 (barOf z S) (barOf z K₁)
  inter : IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂) = Y ⊓ A
  Cb : IVK.Prod3.Cb (barOf z K₁) (barOf z K₂) r
  Cc : IVK.Prod3.Cc (barOf z S) (barOf z K₁) (barOf z K₂) Y r
  Cd : IVK.Prod3.Cd (barOf z S) (barOf z K₁) (barOf z K₂) A (toBar z ⟨a, haC⟩)
  Ce : IVK.Prod3.Ce (barOf z S) (barOf z K₁) (barOf z K₂) Y A (toBar z ⟨a, haC⟩)
  Cf : IVK.Prod3.Cf (barOf z S) Y
  Cg : IVK.Prod3.Cg (barOf z K₁) (barOf z K₂) Y (zBar z) (toBar z ⟨a, haC⟩) (barOf z S)
  Ch : IVK.Prod3.Ch (barOf z K₁) (barOf z K₂) (toBar z ⟨a, haC⟩) r
  Ci : IVK.Prod3.Ci (barOf z S) (barOf z K₁) (barOf z K₂) (toBar z ⟨a, haC⟩)
  Cj : IVK.Prod3.Cj (barOf z S) (barOf z K₁) (zBar z) (toBar z ⟨a, haC⟩)

structure L53Lat (z : G) (S K₁ K₂ : Subgroup G) (a : G) (Y A : Subgroup G) : Prop where
  Y_le : Y ≤ S1 S K₁
  A_le : A ≤ S1 S K₁
  prod : Y ⊔ A = S1 S K₁
  inter : Y ⊓ A = Pz S z
  Y_normal : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y
  Y_index : (Pz S z).relIndex Y ≤ 2
  a_mem : a ∈ A
  A_cyclic : ∃ c ∈ A, A = Pz S z ⊔ zpowers c
  A_order : 4 ≤ (Pz S z).relIndex A
  YA_comm : ∀ y ∈ Y, ∀ b ∈ A, ⁅y, b⁆ ∈ Pz S z
  S_nonab : ∃ s ∈ S, ∃ s' ∈ S, ⁅s, s'⁆ ∉ Y
  field : ∃ r : ℕ, IsPrimePow r ∧ Odd r ∧ HasSL2Model (HatT K₁) (fun q => q = r ^ 4) ∧
    HasSL2Model (HatT K₂) (fun q => q = r ^ 4)
  swap : ∃ t ∈ S, t ∉ normalizer (K₁ : Set G)
  a_not_K : a ∉ K₁ ⊔ K₂

end CFSG.GH74.GLS.IVK.Lifted32
