module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Prod3

section Defs

variable {H : Type} [Group H]

abbrev T1 (T K₁ : Subgroup H) : Subgroup H := T ⊓ normalizer (K₁ : Set H)

abbrev P (T K₁ K₂ : Subgroup H) : Subgroup H := T ⊓ (K₁ ⊔ K₂)

@[expose] def invCoset (K : Subgroup H) (a : H) : Set H :=
  {u | (∃ k ∈ K, u = k * a) ∧ u * u = 1}

@[expose] def ELayer (X : Subgroup H) : Subgroup H := (layer ↥X).map X.subtype

@[expose] def IndFAut (K : Subgroup H) (a : H) : Prop :=
  (∀ x ∈ K, a * x * a⁻¹ ∈ K) ∧
  ((∃ (F : Type) (_ : Field F) (_ : Finite F) (e : ↥K ≃* SL2 F) (σ : F ≃+* F),
      ∀ (x : ↥K) (hx : a * (x : H) * a⁻¹ ∈ K),
        e ⟨a * x * a⁻¹, hx⟩ = stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (e x)) ∨
    (IsDoubleCoverOfAlt ↥K 7 ∧
      ((∀ x ∈ K, a * x * a⁻¹ = x) ∨ ¬ ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹)))

structure Setting (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H) (z : H) : Prop where
  fstar : generalizedFitting H = K₁ ⊔ K₂
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  type₁ : HasSL2Model ↥K₁ (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥K₁ 7
  type₂ : HasSL2Model ↥K₂ (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥K₂ 7
  z_ord : orderOf z = 2
  zK : (Subgroup.center ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype = zpowers z

structure Hyp (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H) (z : H) (T : Subgroup H) (a : H) :
    Prop where
  setting : Setting H K₁ K₂ z
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  a_mem : a ∈ T1 T K₁
  a_ord : orderOf a = 2
  f₁ : IndFAut K₁ a
  f₂ : IndFAut K₂ a
  a_comm : a ∈ commutator H
  a_ne_z : a ≠ z
  extr : CFSG.ABGLocalTools.IsSylowOf 2 (T1 T K₁ ⊓ centralizer ({a} : Set H))
    (centralizer ({a} : Set H) ⊓ (K₁ ⊔ K₂ ⊔ T1 T K₁))

@[expose] def Ca (T K₁ K₂ : Subgroup H) (a : H) : Prop :=
  T1 T K₁ < T ∧ (¬ ∀ x ∈ K₁, a * x * a⁻¹ = x) ∧ (¬ ∀ x ∈ K₂, a * x * a⁻¹ = x) ∧
    ∃ s ∈ T, ∃ s' ∈ T, ⁅s, s'⁆ ∉ P T K₁ K₂

@[expose] def Cb (K₁ K₂ : Subgroup H) (r : ℕ) : Prop :=
  IsPrimePow r ∧ Odd r ∧ HasSL2Model ↥K₁ (fun q => q = r ^ 4) ∧ HasSL2Model ↥K₂ (fun q => q = r ^ 4)

@[expose] def Cc (T K₁ K₂ Y : Subgroup H) (r : ℕ) : Prop :=
  (∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧ (P T K₁ K₂).relIndex Y ≤ 2 ∧
    ((P T K₁ K₂).relIndex Y = 2 → ∀ K ∈ ({K₁, K₂} : Set (Subgroup H)),
      ∃ _ : (K.subgroupOf (K₁ ⊔ K₂ ⊔ Y)).Normal,
        IsPGL2 (↥(K₁ ⊔ K₂ ⊔ Y) ⧸ K.subgroupOf (K₁ ⊔ K₂ ⊔ Y)) (fun q => q = r ^ 4))

@[expose] def Cd (T K₁ K₂ A : Subgroup H) (a : H) : Prop :=
  a ∈ A ∧ (∃ c ∈ A, A = P T K₁ K₂ ⊔ zpowers c) ∧ 4 ≤ (P T K₁ K₂).relIndex A

@[expose] def Ce (T K₁ K₂ Y A : Subgroup H) (a : H) : Prop :=
  (∀ y ∈ Y, ∀ b ∈ A, ⁅y, b⁆ ∈ P T K₁ K₂) ∧
    ∀ h : H, (∀ y ∈ Y, ⁅h, y⁆ ∈ K₁ ⊔ K₂) ∧ ⁅h, a⁆ ∈ K₁ ⊔ K₂

@[expose] def Cf (T Y : Subgroup H) : Prop := ∃ s ∈ T, ∃ s' ∈ T, ⁅s, s'⁆ ∉ Y

@[expose] def Cg (K₁ K₂ Y : Subgroup H) (z a : H) (T : Subgroup H) : Prop :=
  (∃ b ∈ invCoset (K₁ ⊔ K₂) a, ¬ ConjUnder (K₁ ⊔ K₂) a b ∧
      ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ConjUnder (K₁ ⊔ K₂) a u ∨ ConjUnder (K₁ ⊔ K₂) b u) ∧
    (P T K₁ K₂ ≠ Y → ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ∀ v ∈ invCoset (K₁ ⊔ K₂) a,
      ConjUnder (K₁ ⊔ K₂ ⊔ Y) u v) ∧
    ConjUnder (K₁ ⊔ K₂) a (a * z)

@[expose] def Ch (K₁ K₂ : Subgroup H) (a : H) (r : ℕ) : Prop :=
  ELayer ((K₁ ⊔ K₂) ⊓ centralizer ({a} : Set H)) =
      ELayer (K₁ ⊓ centralizer ({a} : Set H)) ⊔ ELayer (K₂ ⊓ centralizer ({a} : Set H)) ∧
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup H)),
      HasSL2Model ↥(ELayer (K ⊓ centralizer ({a} : Set H))) (fun q => q = r ^ 2) ∧
      ∃ _ : ((ELayer (K ⊓ centralizer ({a} : Set H))).subgroupOf
          ((K₁ ⊔ K₂) ⊓ centralizer ({a} : Set H))).Normal,
        IsPGL2 (↥((K₁ ⊔ K₂) ⊓ centralizer ({a} : Set H)) ⧸
          (ELayer (K ⊓ centralizer ({a} : Set H))).subgroupOf
            ((K₁ ⊔ K₂) ⊓ centralizer ({a} : Set H))) (fun q => q = r ^ 2)

@[expose] def Ci (T K₁ K₂ : Subgroup H) (a : H) : Prop :=
  (K₁ ⊔ K₂ ⊔ (T1 T K₁ ⊓ centralizer ({a} : Set H))).relIndex (K₁ ⊔ K₂ ⊔ T1 T K₁) ≤ 2

@[expose] def Cj (T K₁ : Subgroup H) (z a : H) : Prop :=
  (Subgroup.center ↥(T1 T K₁ ⊓ centralizer ({a} : Set H))).map
    (T1 T K₁ ⊓ centralizer ({a} : Set H)).subtype = zpowers a ⊔ zpowers z

end Defs

end Prod3

@[expose] def IVK_3_2_abstract : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H) (z : H) (T : Subgroup H) (a : H),
    Prod3.Hyp H K₁ K₂ z T a →
      Prod3.Ca T K₁ K₂ a ∧
      (CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₁) (centralizer (K₂ : Set H)) →
       CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)) →
        ∃ (Y A : Subgroup H) (r : ℕ), Y ≤ Prod3.T1 T K₁ ∧ A ≤ Prod3.T1 T K₁ ∧
          Y ⊔ A = Prod3.T1 T K₁ ∧ Prod3.P T K₁ K₂ = Y ⊓ A ∧
          Prod3.Cb K₁ K₂ r ∧ Prod3.Cc T K₁ K₂ Y r ∧ Prod3.Cd T K₁ K₂ A a ∧
          Prod3.Ce T K₁ K₂ Y A a ∧ Prod3.Cf T Y ∧ Prod3.Cg K₁ K₂ Y z a T ∧
          Prod3.Ch K₁ K₂ a r ∧ Prod3.Ci T K₁ K₂ a ∧ Prod3.Cj T K₁ z a)

end CFSG.GH74.GLS.IVK
