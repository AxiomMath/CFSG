module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.Blueprint
open scoped commutatorElement

section Stages

variable {G : Type} [Group G]

@[expose] def L52 (S K₁ K₂ : Subgroup G) : Prop :=
  Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁

@[expose] def invCoset (K : Subgroup G) (a : G) : Set G :=
  {u | (∃ k ∈ K, u = k * a) ∧ u * u = 1}

structure L53Data (z : G) (S K₁ K₂ : Subgroup G) (a : G) (Y A : Subgroup G) : Prop where
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
  two_classes : ∃ b ∈ invCoset (K₁ ⊔ K₂) a, ¬ IVK.ConjUnder (K₁ ⊔ K₂) a b ∧
    ∀ u ∈ invCoset (K₁ ⊔ K₂) a, IVK.ConjUnder (K₁ ⊔ K₂) a u ∨ IVK.ConjUnder (K₁ ⊔ K₂) b u
  fused : Pz S z ≠ Y → ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ∀ v ∈ invCoset (K₁ ⊔ K₂) a,
    IVK.ConjUnder (K₁ ⊔ K₂ ⊔ Y) u v
  a_az : IVK.ConjUnder (K₁ ⊔ K₂) a (a * z)
  swap : ∃ t ∈ S, t ∉ normalizer (K₁ : Set G)
  a_not_K : a ∉ K₁ ⊔ K₂
  ZW : ∀ w ∈ Wof S a, (∀ v ∈ Wof S a, w * v = v * w) → w ∈ zpowers a ⊔ zpowers z

@[expose] def L53 (z : G) (S K₁ K₂ : Subgroup G) (a : G) : Prop :=
  ∃ Y A : Subgroup G, L53Data z S K₁ K₂ a Y A

@[expose] def JClassical4 (a : G) (q₀ : ℕ) : Prop :=
  ∃ p f : ℕ, p ^ f = q₀ ∧ (LieModel (HatT (Jof a)) .PSp 2 p f ∨ LieModel (HatT (Jof a)) .PSU 4 p f)

@[expose] def JG2 (a : G) (q₀ : ℕ) : Prop :=
  ∃ p f : ℕ, p ^ f = q₀ ∧ LieModel (HatT (Jof a)) .G2 0 p f

@[expose] def L54a (z : G) (S K₁ K₂ : Subgroup G) (a : G) : Prop :=
  ∀ r : ℕ, HasSL2Model (HatT K₁) (fun q => q = r ^ 4) → HasSL2Model (HatT K₂) (fun q => q = r ^ 4) →
    (z ∈ zStar (centralizer ({a} : Set G)) ∨
      (Iall z a ≤ Jof a ∧ (JClassical4 a (r ^ 2) ∨ JG2 a (r ^ 2)) ∧
        Wof S a ⊓ centralizer ((Jof a : Subgroup G) : Set G) = zpowers a))

@[expose] def L54b (S : Subgroup G) (a : G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 2 (Wof S a) (centralizer ({a} : Set G))

@[expose] def L54c (K₁ K₂ : Subgroup G) (a : G) : Prop :=
  (∃ q₀ : ℕ, Odd q₀ ∧ 3 < q₀ ∧ (JClassical4 a q₀ ∨ JG2 a q₀)) → ∀ g : G, g⁻¹ * a * g ∉ K₁ ⊔ K₂

@[expose] def L54 (z : G) (S K₁ K₂ : Subgroup G) (a : G) : Prop :=
  L54a z S K₁ K₂ a ∧ L54b S a ∧ L54c K₁ K₂ a

@[expose] def L55 (z : G) (a : G) : Prop :=
  ∀ r : ℕ, z ∉ zStar (centralizer ({a} : Set G)) → JClassical4 a (r ^ 2) ∨ JG2 a (r ^ 2) →
    JG2 a (r ^ 2)

@[expose] def L56 (z : G) (S : Subgroup G) (a : G) (Y : Subgroup G) : Prop :=
  ∀ r : ℕ, JG2 a (r ^ 2) → Y = Pz S z

@[expose] def L57 (z a x : G) : Prop :=
  ¬ IsConj z x ∧ z ∈ zStar (centralizer ({a} : Set G))

@[expose] def L58 (z : G) (K₁ K₂ : Subgroup G) (a : G) : Prop :=
  ∃ t : G, IsConj z t ∧ Interchanges t K₁ K₂ ∧ ¬ IsConj z (t * z) ∧ t * a = a * t ∧ t * z = z * t

end Stages

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
