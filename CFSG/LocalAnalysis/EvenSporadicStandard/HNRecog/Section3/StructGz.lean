module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

@[expose] def IsOrthModule (Y M : Subgroup G) : Prop :=
  IsElemTwo 4 M ∧ ∃ S : Fin 2 → Set G, IsOrbitPartition Y {x | x ∈ M ∧ x ≠ 1} S ∧
    Nat.card ↥(S 0) = 5 ∧ Nat.card ↥(S 1) = 10

structure Y4aStruct (a z a₁ : G) : Prop where
  shape : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a₁ z)
  card_Q : IsElemTwo 5 (Gxy a₁ z ⊓ Qz z)
  pCore : CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) =
    derivedOf (Gxy a₁ z) ⊓ Qz z ⊓ Qz (a₁ * z)
  orth : IsOrthModule (derivedOf (Gxy a₁ z)) (CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)))

structure Y4bStruct (a z a₁ : G) : Prop where
  orbit_2A : IsConjOrbit (derivedOf (Gxy a₁ z))
    {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t}
  cent_2A : ∀ t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)), IsConj a t →
    IsExtensionShape ↥(Gx t ⊓ derivedOf (Gxy a₁ z)) (Elem2 4) (Sym 3)
  no_2B_pair : ¬ ∃ E : Subgroup G, E ≤ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsElemTwo 2 E ∧
    ∀ t ∈ E, t ≠ 1 → IsConj z t

structure Y4aFacts (a z : G) : Prop where
  y4a : ∀ a₁ : G, a₁ ∈ Gx z → IsConj a a₁ → IsConj z (a₁ * z) → Y4aStruct a z a₁

structure StructGzFacts (a z : G) : Prop where
  three : (∀ σ : ↥(Gx z), orderOf σ = 3 →
        (IsShapeZpTimesA5 3 ↥(CbarCent z σ) ∧ Qz z ⊓ Gx (σ : G) = Subgroup.zpowers z) ∨
        (IsShapeZpWrTwo 3 ↥(CbarCent z σ) ∧ IsPlusExtraspecial 2 (Qz z ⊓ Gx (σ : G)))) ∧
      (∃ σ : ↥(Gx z), orderOf σ = 3 ∧ IsShapeZpTimesA5 3 ↥(CbarCent z σ)) ∧
      (∃ σ : ↥(Gx z), orderOf σ = 3 ∧ IsShapeZpWrTwo 3 ↥(CbarCent z σ))
  five : (∀ ρ : ↥(Gx z), orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(CbarCent z ρ) ∧ Qz z ⊓ Gx (ρ : G) = Subgroup.zpowers z) ∨
        (IsShapeZpTimesZp 5 ↥(CbarCent z ρ) ∧ IsMinusExtraspecial 2 (Qz z ⊓ Gx (ρ : G))) ∨
        (IsShapeZpWrTwo 5 ↥(CbarCent z ρ) ∧ Qz z ⊓ Gx (ρ : G) = Subgroup.zpowers z)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpTimesA5 5 ↥(CbarCent z ρ)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpTimesZp 5 ↥(CbarCent z ρ)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpWrTwo 5 ↥(CbarCent z ρ))
  centQ_inv : ∀ x : ↥(Gx z), (barOf z x) ^ 2 = 1 → barOf z x ≠ 1 →
    Nat.card (centQtilde z x) = 2 ^ 5
  y4b : ∀ a₁ : G, a₁ ∈ Gx z → IsConj a a₁ → IsConj z (a₁ * z) → Y4bStruct a z a₁

structure XStruct (a z a' : G) : Prop where
  shape : IsShapeTwoTwoSixS5 ↥(Gxy a' z)
  pCore : CFSG.Open.pCoreOf 2 (Gxy a' z) = Gxy a' z ⊓ Qz z
  pCore_derived : CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) = derivedOf (Gxy a' z) ⊓ Qz z ∧
    CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) =
      CFSG.Open.pCoreOf 2 (Gxy a' z ⊓ derivedOf (Gx a')) ∧
    CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) =
      CFSG.Open.pCoreOf 2 (Gxy a' z ⊓ derivedOf (Gx (a' * z)))
  shape_O2 : IsShapeZ2Z4StarExtra ↥(CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)))
  center : centerOf (derivedOf (Gxy a' z)) =
      centerOf (CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z))) ∧
    Nonempty (↥(centerOf (derivedOf (Gxy a' z))) ≃* Z 2 × Z 4)
  o1 : IsConjOrbitStab (Gxy a' z) (orb2A a a' ∩ orb2A a (a' * z)) (2 ^ 8 * 3)
  o1_mem : ∀ c ∈ orb2A a a' ∩ orb2A a (a' * z), c ∈ Qz z
  o1_cards : ∀ c ∈ orb2A a a' ∩ orb2A a (a' * z),
    Nat.card ↥(Gxyz a' z c ⊓ Qz z) = 2 ^ 7 ∧
    Nat.card ↥(Gxyz a' z c ⊓ Qz z ⊓ derivedOf (Gxy a' z)) = 2 ^ 6 ∧
    Nat.card ↥(Gxyz a' z c ⊓ derivedOf (Gxy a' z)) = 2 ^ 6 * 3 ∧
    QuotShape (Gxyz a' z c ⊓ derivedOf (Gxy a' z))
      (Gxyz a' z c ⊓ Qz z ⊓ derivedOf (Gxy a' z)) (Z 3)
  three_cent : ∀ σ ∈ Gxy a' z, orderOf σ = 3 → ∃ c ∈ orb2A a a' ∩ orb2A a (a' * z),
    CFSG.Open.pCoreOf 2 (Gxy a' z) ⊓ Gx σ =
        Subgroup.closure ((centerOf (derivedOf (Gxy a' z)) : Set G) ∪ {c}) ∧
      CFSG.Open.pCoreOf 2 (derivedOf (Gxy a' z)) ⊓ Gx σ = centerOf (derivedOf (Gxy a' z))
  o2 : IsConjOrbitStab (Gxy a' z) (orb2A a a' ∩ orb2B a z (a' * z)) (2 ^ 7 * 3)
  o2_cards : ∀ d ∈ orb2A a a' ∩ orb2B a z (a' * z),
    IsElemTwo 5 (Gxyz a' z d ⊓ Qz z) ∧
    IsElemTwo 4 (Gxyz a' z d ⊓ Qz z ⊓ derivedOf (Gxy a' z)) ∧
    Nat.card ↥(Gxyz a' z d ⊓ derivedOf (Gxy a' z)) = 2 ^ 5 * 3 ∧
    QuotShape (Gxyz a' z d ⊓ derivedOf (Gxy a' z))
      (Gxyz a' z d ⊓ Qz z ⊓ derivedOf (Gxy a' z)) (Sym 3)

structure StructXFacts (a z : G) : Prop where
  x_struct : ∀ a' ∈ Qz z, IsConj a a' → XStruct a z a'

@[expose] def tab3Base (a z a' : G) : Set G :=
  {c | c ∈ Qz z ∧ IsConj a c ∧ c ≠ a' ∧ c ≠ a' * z}

@[expose] def tab3Set (a z a' : G) : Fin 3 → Set G :=
  ![{c | c ∈ tab3Base a z a' ∧ IsConj a (a' * c)},
    {c | c ∈ tab3Base a z a' ∧ IsConj z (a' * c)},
    {c | c ∈ tab3Base a z a' ∧ (a' * c) ^ 2 = z}]

structure TableIIIFacts (a z : G) : Prop where
  card : ∀ a' ∈ Qz z, IsConj a a' → Nat.card ↥(tab3Base a z a') = 118
  partition : ∀ a' ∈ Qz z, IsConj a a' →
    IsOrbitPartition (Gxy a' z) (tab3Base a z a') (tab3Set a z a')
  card_stab : ∀ a' ∈ Qz z, IsConj a a' →
    StabCard (Gxy a' z) (tab3Set a z a') ![2 ^ 8 * 3, 2 ^ 10, 2 ^ 7 * 5]
  shape_4A : ∀ a' ∈ Qz z, IsConj a a' → ∀ c ∈ tab3Set a z a' 2,
    IsShapeTwoOneSixByFive ↥(Gxyz a' z c)

structure Gz9Facts (a z : G) : Prop where
  aschbacher : ∃ (Q : Subgroup ↥(Gx z)) (_ : Q.Normal), AschbacherHyp ↥(Gx z) Q

end CFSG.EvenSporadicStandard.HNRecog.Section3
