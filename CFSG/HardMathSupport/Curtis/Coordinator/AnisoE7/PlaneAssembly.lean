module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.FrameLines
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.CertCases

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


@[expose] def E7SixLinesKind (kinds : List ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)), 1 ≤ f → Nat.card K = ℓ ^ f → p.Prime → 3 < p →
    (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1 →
    ∀ (c : adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K)), IsElemAbelian p E →
      Nat.card E = p ^ 3 →
      (∀ x ∈ E, psiC F.g0 c x ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) →
      ∀ y ∈ E, y ≠ 1 → ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 b = psiC F.g0 c y →
      ∀ cert ∈ e7T3Certs, rootCharKernel b =
        {α | ∃ l ∈ cert.rootList, α = toVec Tag.E7.rank l} →
      cert.comps.map E7T3Comp.kind = kinds → sigma0 ∈ cert.rootList →
      ∀ k : adjointGroup .E7 K, k * y = y * k → k ∈ hyperClosure p ⊤ E

@[expose] def E7SixRSub : Prop :=
  ∀ (K : Type) [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)), Nat.card K = ℓ ^ f → ∀ c : adjointGroup .E7 K,
    ∃ R : Subgroup (adjointGroup .E7 K), R ≠ ⊥ ∧ IsPGroup ℓ R ∧
      ∀ e : adjointGroup .E7 K, (∃ b : Fin Tag.E7.rank → Lˣ,
        rootDiagUnit .E7 b = psiC F.g0 c e ∧ rootChar b (toVec Tag.E7.rank sigma0) = 1) →
      ∀ u ∈ R, e * u = u * e

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
