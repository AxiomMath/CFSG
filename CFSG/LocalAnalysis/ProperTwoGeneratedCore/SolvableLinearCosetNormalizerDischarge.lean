module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairGenerationDischarge

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ProperTwoGeneratedCore.CosetNormalizer CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise

theorem linearSuzukiPointKernelRootProduct_holds
    (G : Type) [Group G] [Finite G] :
    LinearSuzukiPointKernelRootProduct G := by
  intro H z h beta hbeta t ht hrank w hwE hw hwz hwt i hi hfix
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  have key := fun (R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H))
      (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) =>
    RankOnePair.linear_Suzuki_pair_centralizer_point_kernel_is_root_product h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G)
      (pairCommutatorGenerationTheorem G) beta hbeta ht hrank hwE hw hwz hwt hi hfix R Rv T₁
  obtain ⟨-, -, -, -, -, -, -, -, hK, -⟩ := key R₀ T₀
  refine ⟨fun R => ?_, hK, fun R T₁ => ?_⟩
  · obtain ⟨-, -, -, -, hcard, -⟩ := key R T₀
    exact hcard
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, hBA⟩ := key R T₁
    exact ⟨he, hBA⟩

theorem solvableLinearCosetNormalizerTheorem_holds
    (G : Type) [Group G] [Finite G] :
    SolvableLinearCosetNormalizerTheorem G :=
  solvableLinearCosetNormalizerTheorem_of_parts (pairCommutatorGenerationTheorem G)
    (linearSuzukiPointKernelRootProduct_holds G) (linearSuzukiHullOddCoreTrivial_holds G)

theorem solvable_linear_coset_normalizer_produces_cyclic_sylow_quotient_holds
    {G : Type}
    [Group G] [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t)
    (hdeg : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) + 1)
    (hn : Nat.card (pointRightCosetSpace H) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) ^ 2 + 1)
    (hsolv : Group.IsSolvable (cosetNormalizerPerm (rootCoset H z u)).range) :
    let M := Subgroup.centralizer ({u} : Set G)
    let D := pairPointStabilizer H beta
    let q := Nat.card ({1} ∪ distinguishedRoots H z u : Set G)
    let Δ := rootCoset H z u
    let N := Subgroup.normalizer Δ
    let A := N ⊓ D
    (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f) ∧ ¬ IsConj u z ∧
    ∃ (U : Subgroup G) (_ : IsElementaryAbelian 2 U),
      (U : Set G) = {1} ∪ distinguishedRoots H z u ∧ (∀ x ∈ U, x ≠ 1 → IsConj z x) ∧
      ∃ j : Additive U ≃ Δ, (∀ v : U, (j (Additive.ofMul v) : G) = u * v) ∧
        (∀ g ∈ translationGroup (Additive U),
          j.permCongr g.toEquiv ∈ (cosetNormalizerPerm Δ).range) ∧
        let Q := N ⊓ Subgroup.centralizer (U : Set G)
        (∀ n : N, (∃ g ∈ translationGroup (Additive U),
            cosetNormalizerPerm Δ n = j.permCongr g.toEquiv) ↔ (n : G) ∈ Q) ∧
        (Q.subgroupOf N).Normal ∧ IsPGroup 2 Q ∧ Nat.card Q = 2 * q ^ 2 ∧
        U ≤ Q ∧ U.subgroupOf Q ≤ Subgroup.center Q ∧
        A = D ⊓ M ∧ (N : Set G) = (Q : Set G) * (A : Set G) ∧ Q ⊓ A = Subgroup.zpowers u ∧
        ∃ _ : (U.subgroupOf Q).Normal, IsElementaryAbelian 2 (Q ⧸ U.subgroupOf Q) ∧
          let W : Subgroup (Q ⧸ U.subgroupOf Q) :=
            Subgroup.closure {w : Q ⧸ U.subgroupOf Q | ∃ a ∈ A, ∃ x y : Q, (y : G) = a * x * a⁻¹ ∧
              w = (QuotientGroup.mk y : Q ⧸ U.subgroupOf Q) *
                (QuotientGroup.mk x : Q ⧸ U.subgroupOf Q)⁻¹}
          IsCompl (((Subgroup.zpowers u).subgroupOf Q).map
            (QuotientGroup.mk' (U.subgroupOf Q))) W ∧
          let V := (W.comap (QuotientGroup.mk' (U.subgroupOf Q))).map Q.subtype
          (V.subgroupOf N).Normal ∧ Nat.card V = q ^ (2 : ℕ) ∧ U ≤ V ∧
          U.subgroupOf V ≤ Subgroup.center V ∧ u ∉ V ∧
          (∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U) ∧
          (∀ P : Sylow 2 A,
            IsCyclic ((P : Subgroup A).map A.subtype) ∧ u ∈ (P : Subgroup A).map A.subtype ∧
            ∃ S : Sylow 2 G,
              (S : Set G) = (Q : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
              (S : Set G) = (V : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
              V ⊓ (P : Subgroup A).map A.subtype = ⊥ ∧
              ∃ _ : (V.subgroupOf (S : Subgroup G)).Normal,
                Nonempty (↥(S : Subgroup G) ⧸ V.subgroupOf (S : Subgroup G) ≃*
                  (P : Subgroup A).map A.subtype)) ∧
          (∃ x ∈ V, IsConj u x) ∧ (∀ x ∈ V, IsConj u x → ∀ y ∈ U, IsConj u (x * y)) ∧
          ∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y) :=
  solvable_linear_coset_normalizer_produces_cyclic_sylow_quotient (pairCommutatorGenerationTheorem G)
    (linearSuzukiPointKernelRootProduct_holds G) (linearSuzukiHullOddCoreTrivial_holds G) h hbeta ht
    hrank huD hu huz hut hdeg hn hsolv

theorem theoremTwo_of_unitaryMonomial
    (h : ∀ (G : Type) [Group G] [Finite G], UnitaryMonomialTheorem G) :
    Assembly.TheoremTwo :=
  theoremTwo_of_solvable_and_monomial fun G _ _ =>
    ⟨solvableLinearCosetNormalizerTheorem_holds G, h G⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
