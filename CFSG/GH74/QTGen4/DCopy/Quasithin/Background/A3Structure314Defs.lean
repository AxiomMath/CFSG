module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure A314Descriptors_F4 : Prop where

  lie : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L P : Subgroup G), IsRank2LieChar2 ↥L →
    IsMaxParabolic2 L P → IsAlt 5 (ModO2 (perfectCore P)) →
      CFSG.generalizedFitting ↥(perfectCore P) = CFSG.pCore 2 ↥(perfectCore P) ∧
      (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L)

  alt7 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) →
    IsAlt 5 ↥B → StabilizesFivePoints B L

  sl3five : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L) →
    IsSL2 5 ↥B → B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G))

  l3five : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L) →
    IsExt ↥B (fun V _ => IsElemAbelianOfRank 5 2 V) (fun Y _ => IsSL2 5 Y) →
    ∃ P, IsMaxParabolicOf 5 L P ∧ B = perfectCore P

  mathieu : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L →
    (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L) →
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) → IsShort2 B ∧ IsLin2Type B 2

  j1 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J1 ↥L → IsAlt 5 ↥B →
    ∃ z : G, z ∈ L ∧ orderOf z = 2 ∧ B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))

  j2 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J2 ↥L →
    IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y) →
    ∃ z : G, IsTwoCentralInvolution L z ∧ B = L ⊓ Subgroup.centralizer ({z} : Set G)

  j4 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J4 ↥L → IsAlt 5 (ModO2 B) →
    CFSG.generalizedFitting ↥B = CFSG.pCore 2 ↥B

  hs : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .HS ↥L →
    IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y) →
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))

  ru : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .Ru ↥L → IsAlt 5 (ModO2 B) →
    Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 →
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))

structure A314Facts_F4 : Prop where

  model : A314ModelFacts

  desc : A314Descriptors_F4

end CFSG.Quasithin
