module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank

variable {G : Type*} [Group G]

structure StrongClosureComponent (H S U L : Subgroup G) : Prop where
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf S H
  le_S : U ≤ S
  elem : CFSG.Open.IsElemAbelian 2 U
  closed : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U
  le_H : L ≤ H
  perfect : ⁅L, L⁆ = L
  subnormal : (L.subgroupOf H).IsSubnormal
  normalizes : U ≤ Subgroup.normalizer (L : Set G)

@[expose] def K1FamilyRecognition (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S U L : Subgroup G), StrongClosureComponent H S U L →
    P (L ⧸ Subgroup.center L) →
    ∀ w ∈ U, w ∈ Subgroup.centralizer (S : Set G) →
      ¬ L ≤ Subgroup.centralizer ({w} : Set G) →
      CFSG.QuasithinUnique.CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G)) →
      CFSG.Open.fusionIsBenderGroup (L ⧸ Subgroup.center L)

@[expose] def AltFamily (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def OddClassicalFamily (X : Type) [Group X] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f) ∨
      StatedClassicalModel X .PSL 3 p 1 ∨ StatedClassicalModel X .PSU 3 p 1)

@[expose] def EvenClassicalFamily (X : Type) [Group X] : Prop :=
  ∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel X .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f)

@[expose] def ExceptionalFamily (X : Type) [Group X] : Prop :=
  CFSG.Open.SQTKTauCeti.SQTKExceptional X

@[expose] def SmallLinearFamily (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel X .PSL n 2 1

@[expose] def SporadicFamily (X : Type) [Group X] : Prop :=
  ∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (X ≃* s.Group)

@[expose] def ExceptionalFamilyCat (X : Type) [Group X] : Prop :=
  (∃ f : ℕ,
    (2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f) ∨
    (1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel X .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel X 2 f)) ∨
  CFSG.Blueprint.ReeTitsModel X .Tits 2 1

@[expose] def SporadicFamilyCat (X : Type) [Group X] : Prop :=
  ∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)

theorem sqtkSimpleList_iff (X : Type) [Group X] :
    CFSG.Open.SQTKTauCeti.SQTKSimpleList X ↔
      AltFamily X ∨ OddClassicalFamily X ∨ EvenClassicalFamily X ∨ ExceptionalFamily X ∨
        SmallLinearFamily X ∨ SporadicFamily X :=
  Iff.rfl

end CFSG.QuasithinUnique.K1
