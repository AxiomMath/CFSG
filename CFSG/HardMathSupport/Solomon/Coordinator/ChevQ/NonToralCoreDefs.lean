module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


structure KernelBlocks (τ : Tag) (S : Set (Fin τ.rank → ℤ)) where
  blk : Fin 3 → Set (Fin τ.rank → ℤ)
  nonempty : ∀ j, (blk j).Nonempty
  sub : ∀ j, blk j ⊆ S
  cover : ∀ α ∈ S, ∃ j, α ∈ blk j
  neg : ∀ j, ∀ γ ∈ blk j, -γ ∈ blk j
  disj : ∀ j j', j ≠ j' → Disjoint (blk j) (blk j')
  orth : ∀ j j', j ≠ j' → ∀ γ ∈ blk j, ∀ δ ∈ blk j', iform γ δ = 0
  trans : ∀ j, ∀ γ ∈ blk j, ∀ δ ∈ blk j,
    ∃ x ∈ Subgroup.closure (rootReflection '' S), x • γ = δ
  perm : ∀ x : WeylGroup τ, (fun α => x • α) '' S = S →
    ∀ j, ∃ j', (fun α => x • α) '' blk j = blk j'

@[expose] def monomialElt (τ : Tag) (L : Type) [Field L] (b : Fin τ.rank → Lˣ) (ω : WeylGroup τ) :
    ModGL τ L :=
  rootDiagUnit τ b * canonicalRep (coxeterSystem τ) L ω

@[expose] def NonToralBlockCore : Prop :=
  ∀ (τ : Tag), (τ = Tag.E7 ∨ τ = Tag.E8) →
  ∀ (K : Type) [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
    (∀ c, Fr c = c ^ Nat.card K) →
    ∀ {ι : Type} (a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ)
      (B : KernelBlocks τ (familyKernel a)) (b : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (ω : WeylGroup τ), (∀ j : Fin 3, (fun α => ω • α) '' B.blk j = B.blk (j + 1)) →
    ∀ (m : ModGL τ (AlgebraicClosure K)) (x : WeylGroup τ),
      m ∈ familyGroup (K := AlgebraicClosure K) a →
      (fun α => x • α) '' familyKernel a = familyKernel a →
      ∃ (u₁ : ModGL τ (AlgebraicClosure K)) (k : ℕ),
        u₁ ∈ adjointGroup τ (AlgebraicClosure K) ∧
        u₁ ∈ familyGroup (K := AlgebraicClosure K) a ∧ u₁ ^ ringChar K = 1 ∧
        (m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x) *
            Units.map (entrywiseHom Fr) u₁ *
            (m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x)⁻¹ =
          (monomialElt τ (AlgebraicClosure K) b ω) ^ k * u₁ *
            ((monomialElt τ (AlgebraicClosure K) b ω) ^ k)⁻¹ ∧
        Commute u₁ ((monomialElt τ (AlgebraicClosure K) b ω) * u₁ *
            (monomialElt τ (AlgebraicClosure K) b ω)⁻¹) ∧
        u₁ * ((monomialElt τ (AlgebraicClosure K) b ω) * u₁ *
            (monomialElt τ (AlgebraicClosure K) b ω)⁻¹) *
          ((monomialElt τ (AlgebraicClosure K) b ω) ^ 2 * u₁ *
            ((monomialElt τ (AlgebraicClosure K) b ω) ^ 2)⁻¹) ≠ 1

@[expose] def E7ThreeKilledPlaneBlocks : Prop :=
  ∀ (L : Type) [Field L] (a : Fin 2 → Fin Tag.E7.rank → Lˣ),
    (∀ (s : Fin 2) (i : Fin Tag.E7.rank), a s i ^ 3 = 1) →
    (familyKernel (τ := Tag.E7) a).Nonempty →
    ∀ w : WeylGroup Tag.E7, (∀ s, w ∈ rootCharStabilizer (a s)) →
      w ∈ kernelWeylGroup (familyChar a) ∨
        ∃ B : KernelBlocks Tag.E7 (familyKernel a),
          ∀ j : Fin 3, (fun α => w • α) '' B.blk j = B.blk (j + 1)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
