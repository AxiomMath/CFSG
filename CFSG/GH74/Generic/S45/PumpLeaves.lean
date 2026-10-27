module

public import CFSG.GH74.Generic.S45.Final

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def B_S45_pumpStruct : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K → IsJ1OrRee ↥K →
      xbar x ∉ K → ∀ T : Subgroup G, S45Conf x K T →
      ∀ v : G, v ∈ T → v ∈ Pre x K → v ≠ 1 →
        ∃ W J : Subgroup G,
          W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) ∧
          (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal ∧
          IsSimpleGroup ↥W ∧ (∃ a b : ↥W, a * b ≠ b * a) ∧ HasL2Model ↥W Odd ∧
          W ≤ J ∧ J ≤ centralizer ({v} : Set G) ∧
          (J.subgroupOf (centralizer ({v} : Set G))).IsSubnormal ∧ IsQuasisimple ↥J

@[expose] def IsPumpOutcome (K : Type) [Group K] : Prop :=
  IsL34Quotient K ∨ LieModel (K ⧸ center K) .PSU 3 2 2 ∨
    NativeSporadic.IsSporadic (K ⧸ center K) .M12 ∨ LieModel K .PSL 2 2 4 ∨
    NativeSporadic.IsSporadic K .J2

@[expose] def B_III11_13_10 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], InCalK2 K →
    ∀ y : MulAut K, orderOf y = 2 →
      ∀ L : Subgroup K, L ≤ fixSub (zpowers y) →
        (L.subgroupOf (fixSub (zpowers y))).IsSubnormal → HasL2Model ↥L Odd →
        (∀ P : Sylow 2 ↥(fixSub (zpowers y)), IsElementaryAbelian 2 ↥(P : Subgroup ↥(fixSub (zpowers y)))) →
        (¬ ∃ f : ℕ, LieModel K .twistedG2 0 3 f) →
        (HasL2Model ↥L (fun q => q = 5) → ¬ NativeSporadic.IsSporadic K .J1) →
        HasL2Model ↥L (fun q => q = 5) ∧ IsPumpOutcome K ∧
          (¬ NativeSporadic.IsSporadic K .J2 → y ∉ (MulAut.conj : K →* MulAut K).range)

@[expose] def B_III8_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ x : G, orderOf x = 2 → ∀ P : Subgroup G, IsSylowOf 2 P (centralizer ({x} : Set G)) →
      ∀ y : G, y ∈ P → (∀ p ∈ P, p * y = y * p) → orderOf y = 2 →
        (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ y ∈ S ∧ ∀ s ∈ S, s * y = y * s) →
        (∀ g : G, g * y * g⁻¹ ∈ P → (∀ p ∈ P, p * (g * y * g⁻¹) = (g * y * g⁻¹) * p) →
          ∃ c ∈ centralizer ({x} : Set G), c * y * c⁻¹ = g * y * g⁻¹) →
        ∃ hx : x ∈ centralizer ({y} : Set G),
          (⟨x, hx⟩ : ↥(centralizer ({y} : Set G))) ∈ commutator ↥(centralizer ({y} : Set G))

@[expose] def B_III11_2_1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], InCalK2 K → IsPumpOutcome K →
    Odd (Nat.card (commutator (Outer K)))

@[expose] def B_IA_5_3g : Prop :=
  ∀ (K : Type) [Group K] [Finite K], NativeSporadic.IsSporadic K .J2 →
    IsSimpleGroup K ∧
      ∃ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧ Nat.card ↥E = 16

end CFSG.GH74.Generic.S45
