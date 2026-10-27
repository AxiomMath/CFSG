module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Twin1711

variable {G : Type} [Group G]

@[expose] def xOrbit (X R : Subgroup G) : Set (Subgroup G) :=
  {J | ∃ x ∈ X, conjSub x R = J}

@[expose] def commNbrs (X R : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ xOrbit X R ∧ (J = R ∨ Commutes R J)}

@[expose] def centerSet (X : Subgroup G) : Set G :=
  {c | c ∈ X ∧ ∀ x ∈ X, x * c = c * x}

@[expose] def fixSet (X : Subgroup G) (B : Set (Subgroup G)) : Subgroup (MulAut ↥X) where
  carrier := {α | ∀ b ∈ B, ∀ y : ↥X, (y : G) ∈ b → α y = y}
  mul_mem' := by
    intro α β hα hβ b hb y hy
    rw [MulAut.mul_apply, hβ b hb y hy, hα b hb y hy]
  one_mem' := by
    intro b _ y _
    rfl
  inv_mem' := by
    intro α hα b hb y hy
    have h := hα b hb y hy
    calc α⁻¹ y = α⁻¹ (α y) := by rw [h]
      _ = y := α.symm_apply_apply y

@[expose] def QuasiE4 (X : Subgroup G) : Prop :=
  ⁅X, X⁆ = X ∧ ∃ (Q : Type) (_ : Group Q) (f : ↥X →* Q), Function.Surjective f ∧
    IsPGroup 2 ↥f.ker ∧ f.ker ≤ Subgroup.center ↥X ∧
    (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)

structure MemberData (X R : Subgroup G) (t : G) : Prop where
  quasi : QuasiE4 X
  le : R ≤ X
  q8 : Nonempty (↥R ≃* QuaternionGroup 2)
  inv : IsUniqueInvolution R t
  noncentral : ¬ ∀ x ∈ X, x * t = t * x
  inO2 : ∃ P : Subgroup G, P ≤ X ⊓ Subgroup.centralizer ({t} : Set G) ∧
    (∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    IsPGroup 2 ↥P ∧ R ≤ P
  twins : ∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G),
    conjSub s R = R ∨ Commutes R (conjSub s R)

structure SandwichData (X R : Subgroup G) (t : G) (B : Set (Subgroup G)) (N : Subgroup G) :
    Prop where
  mem : R ∈ B
  sub : B ⊆ xOrbit X R
  block : ∀ x ∈ X, conjSub x '' B = B ∨ Disjoint (conjSub x '' B) B
  proper : B ≠ xOrbit X R
  twins : ∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G), conjSub s R ∈ B
  le : N ≤ X ⊓ Subgroup.centralizer ({t} : Set G)
  normal : (N.subgroupOf (X ⊓ Subgroup.centralizer ({t} : Set G))).Normal
  t_mem : t ∈ N
  twins_le : ∀ s ∈ X ⊓ Subgroup.centralizer ({t} : Set G), conjSub s R ≤ N
  inv : ∀ x ∈ X, x * t * x⁻¹ ∈ N → ∃ J ∈ B, IsUniqueInvolution J (x * t * x⁻¹)
  index : N.relIndex (X ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card (fixSet X B)

end Twin1711

open Twin1711

@[expose] def Fin1711Sandwich : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G) (t : G) (B : Set (Subgroup G))
    (N : Subgroup G), MemberData X R t → SandwichData X R t B N →
      (centerSet X).ncard = 4 ∧ B.ncard = 2

@[expose] def Fin1711Pairing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G) (t : G), MemberData X R t →
    (centerSet X).ncard = 4 →
      (commNbrs X R).ncard = 4 ∧
      ∀ J ∈ commNbrs X R, ∀ J' ∈ commNbrs X R, J ≠ J' → ∀ u u' : G,
        IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ X, x * (u * u') = (u * u') * x

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
