module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenCyclic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3 CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def GenNormality : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) →
    (J.subgroupOf (K ⊓ Subgroup.centralizer (E : Set Y))).Normal →
    CFSG.Open.IsQuasisimple ↥J → 3 ∣ Nat.card ↥J → ∀ b ∈ E, b ≠ 1 →
    ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
      (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal →
    (J.subgroupOf (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal

@[expose] def GenCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    (∀ b ∈ E, b ∈ Subgroup.centralizer (K : Set Y) → b = 1) →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) → CFSG.Open.IsQuasisimple ↥J → 3 ∣ Nat.card ↥J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    (∀ b ∈ E, b ≠ 1 → (J.subgroupOf (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal) → False

theorem genFaithful_of_parts (hN : GenNormality) (hC : GenCore) : GenFaithful := by
  intro Y _ _ K E J hKq hK3 hKc hEN hEel hE9 hfaith hEK hJle hJn hJq h3 hJL
  by_contra hcon
  push Not at hcon
  exact hC Y K E J hKq hK3 hKc hEN hEel hE9 hfaith hJle hJq h3 hJL fun b hb hb1 =>
    hN Y K E J hKq hK3 hKc hEN hEel hE9 hJle hJn hJq h3 b hb hb1 (hcon b hb hb1)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
