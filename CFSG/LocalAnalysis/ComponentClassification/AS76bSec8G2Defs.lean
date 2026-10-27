module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def g2Centralizer (K : Type) [Field K] (S : Set (ModGL .G2 K)) :
    Subgroup (ModGL .G2 K) :=
  adjointGroup .G2 K ⊓ centralizer S

abbrev g2LongCent (K : Type)
    [Field K] : Subgroup (ModGL .G2 K) :=
  g2Centralizer K {pinnedX .G2 K g2c 1}

abbrev g2ShortCent (K : Type)
    [Field K] : Subgroup (ModGL .G2 K) :=
  g2Centralizer K {pinnedX .G2 K g2v 1}

@[expose] def G2Centr184 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ⁅g2LongCent K, g2LongCent K⁆ = g2LongCent K ∧
      g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) = rootSubgroup .G2 K g2c

@[expose] def G2Centr184s : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ⁅⁅g2ShortCent K, g2ShortCent K⁆, ⁅g2ShortCent K, g2ShortCent K⁆⁆ =
        ⁅g2ShortCent K, g2ShortCent K⁆ ∧
      rootSubgroup .G2 K g2v ≤ g2Centralizer K ((⁅g2ShortCent K, g2ShortCent K⁆ :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) ∧
      ∀ x ∈ g2Centralizer K ((⁅g2ShortCent K, g2ShortCent K⁆ : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)), x ^ 2 = 1 → x ∈ rootSubgroup .G2 K g2v

abbrev g2TorusR (K : Type)
    [Field K] : Subgroup (ModGL .G2 K) :=
  (LieType.Chevalley.torusEltHom .G2 K g2ir).range

@[expose] def G2Levi187 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ), Nat.card K = 2 ^ m → 2 ≤ m →
    ∃ L : Subgroup (ModGL .G2 K), L ≤ adjointGroup .G2 K ∧ rootSubgroup .G2 K g2c ≤ L ∧
      ⁅L, L⁆ = L ∧ L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)) ∧
      (∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K, h⁻¹ * x ∈ L) ∧
      Odd (Nat.card (center ↥L)) ∧
      (if m = 2 then StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 3 2 2
        else StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 2 2 m) ∧
      Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)))) ∧
      (∀ x ∈ L, x ^ 2 = 1 → x ≠ 1 →
        ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1) ∧
      (m = 2 → (center ↥L).map L.subtype = g2TorusR K)

@[expose] def G2TorusConj : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ S : Subgroup (ModGL .G2 K), S ≤ g2LongCent K → Nat.card S = Nat.card (g2TorusR K) →
      ∃ h ∈ g2LongCent K, S = (g2TorusR K).map (MulAut.conj h).toMonoidHom

end CFSG.ComponentClassification.RankTwoExceptional
