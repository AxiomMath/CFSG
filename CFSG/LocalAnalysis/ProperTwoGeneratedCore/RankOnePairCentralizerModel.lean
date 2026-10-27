module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonical
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModelSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairHullRank

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
open scoped Pointwise LinearAlgebra.Projectivization

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank_one_pair_centralizer_model_and_two_global_involution_classes
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (R : Sylow 2 ↥(localInvolutionPointHull z u ⊓ H))
    (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) :
    let α := rightCosetMk H 1
    let M := Subgroup.centralizer ({u} : Set G)
    let D := involutionPointClass z
    let L := localInvolutionPointHull z u
    let P := L ⊓ H
    let Γ := elementFixedSet H u
    let π := QuotientGroup.mk' (CFSG.oddCore L)
    let K := M ⊓ Subgroup.centralizer (L : Set G)
    let ι := (H ⊓ M).subtype.comp (T₁ : Subgroup ↥(H ⊓ M)).subtype
    let A := (T₁ : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
    let T := (A : Set G) ∩ ((L : Set G) * (K : Set G))
    let Δ := involutionPointClass u ∩ T
    letI := hullFixedSetAction H z u
    letI := originalCentralizerFixedSetAction H u
    (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) ∧
      L = Subgroup.closure (conjugacyWithin M z) ∧ 2 ≤ twoRank L ∧
      CFSG.oddCore L ≤ Subgroup.center L ∧ Odd (Nat.card (CFSG.oddCore L)) ∧
      ∃ U : Subgroup G, (U : Set G) = {1} ∪ (D ∩ (M : Set G) ∩ (H : Set G)) ∧
        IsElementaryAbelian 2 U ∧ 4 ≤ Nat.card U ∧
        (CFSG.omega₁ (G := R) (p := 2)).map (P.subtype.comp (R : Subgroup P).subtype) = U ∧
        z ∈ (U : Set G) \ {1} ∧
        ((Nat.card Γ = Nat.card U + 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
            Nat.card (BinaryGaloisField f) = Nat.card U ∧
            ∃ (E : L ⧸ CFSG.oddCore L ≃* PSL2BinaryMatrixGroup f)
              (ψ : Γ ≃ ℙ (BinaryGaloisField f) (Fin 2 → BinaryGaloisField f)),
              (∀ γ : Γ, (γ : pointRightCosetSpace H) = α →
                ψ γ = Projectivization.mk (BinaryGaloisField f)
                  (![1, 0] : Fin 2 → BinaryGaloisField f) (by simp)) ∧
              ∀ (l : L) (γ : Γ), ψ (l • γ) = E (π l) • ψ γ) ∨
          (Nat.card Γ = Nat.card U ^ 2 + 1 ∧ ∃ m : ℕ, 1 ≤ m ∧
            Nat.card U = 2 ^ (2 * m + 1) ∧
            Nat.card (BinaryGaloisField (2 * m + 1)) = Nat.card U ∧
            letI := suzukiOvoidAction m
            ∃ (E : L ⧸ CFSG.oddCore L ≃* SuzukiMatrixGroup m)
              (ψ : Γ ≃ {p // p ∈ suzukiOvoidSet m}),
              (∀ γ : Γ, (γ : pointRightCosetSpace H) = α →
                (ψ γ : ℙ (BinaryGaloisField (2 * m + 1))
                  (Fin 4 → BinaryGaloisField (2 * m + 1))) = suzukiOvoidInfinity m) ∧
              ∀ (l : L) (γ : Γ), ψ (l • γ) = E (π l) • ψ γ) ∨
          (Nat.card Γ = Nat.card U ^ 3 + 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
            ∃ (k : Type) (_ : Field k) (_ : Finite k) (J : HermitianForm 3 k)
              (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
              Nat.card k = Nat.card U ^ 2 ∧
              Nat.card {x : k // J.conj x = x} = Nat.card U ∧
              ∃ ρ : ProjectiveSpecialUnitaryMatrixGroup J →*
                  Equiv.Perm (unitaryIsotropicPoints J),
                (∀ g p, ((ρ g p : unitaryIsotropicPoints J) : ℙ k (Fin 3 → k)) =
                  (g : Matrix.ProjGenLinGroup (Fin 3) k) • (p : ℙ k (Fin 3 → k))) ∧
                ∃ (E : L ⧸ CFSG.oddCore L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
                  (ψ : Γ ≃ unitaryIsotropicPoints J),
                  (∀ γ : Γ, (γ : pointRightCosetSpace H) = α →
                    ψ γ = unitaryOuterIsotropicPoint J hJ 0 (by decide)) ∧
                  ∀ (l : L) (γ : Γ), ψ (l • γ) = ρ (E (π l)) (ψ γ))) ∧
        MulAction.IsMultiplyPretransitive M Γ 2 ∧
        (∃ S : Sylow 2 M, (S : Subgroup M).map M.subtype = A) ∧
        u ∉ L ∧
        (CFSG.omega₁ (G := T₁) (p := 2)).map ι = Subgroup.zpowers u ⊔ U ∧
        Disjoint (Subgroup.zpowers u) U ∧
        (∀ a ∈ Subgroup.zpowers u, ∀ b ∈ U, Commute a b) ∧
        (∃ e : Subgroup.zpowers u × U ≃* CFSG.omega₁ (G := T₁) (p := 2),
          ∀ (a : Subgroup.zpowers u) (b : U), ι (e (a, b)) = (a : G) * b) ∧
        {x : G | x ∈ A ∧ orderOf x = 2} =
          ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪ ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
        Disjoint ({u} : Set G) ((U : Set G) \ {1}) ∧
        Disjoint ({u} : Set G) ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
        Disjoint ((U : Set G) \ {1}) ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
        (U : Set G) \ {1} ⊆ D ∧
        T = (A : Set G) ∩ ((L : Set G) * (Subgroup.centralizer (L : Set G) : Set G)) ∧
        u * z ∈ involutionPointClass u ∧
        involutionPointClass u ∩ (A : Set G) = (fun x : G => u * x) '' (U : Set G) ∧
        Δ = (fun x : G => u * x) '' (U : Set G) ∧
        Nat.card Δ = Nat.card U ∧
        {x : G | orderOf x = 2} = involutionPointClass u ∪ D ∧
        involutionPointClass u ≠ D ∧
        ConjClasses.mk '' {x : G | orderOf x = 2} = {ConjClasses.mk u, ConjClasses.mk z} ∧
        Nat.card (ConjClasses.mk '' {x : G | orderOf x = 2}) = 2 := by
  intro α M D L P Γ π K ι A T Δ
  classical
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have hz : orderOf z = 2 := h.local_datum.distinguished_order
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp hz).2
  have hzM : z ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq
  have hLM : L ≤ M := localInvolutionPointHull_le_centralizer z u
  have huclass : u ∉ D :=
    LocalCriterionDegreeIdentity.pair_stabilizer_not_distinguished h.local_datum beta hbeta u huB
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    huH hu huz hescape
  dsimp only at hhull
  obtain ⟨-, -, -, hclassM, -, hfixM, -, hxor⟩ := hhull
  have hLeq : L = Subgroup.closure (conjugacyWithin M z) := congrArg Subgroup.closure hclassM
  have hrank : 2 ≤ twoRank L := by
    rw [hLeq]
    exact minimalLocalFailure_pair_involution_hull_rank_at_least_two h hcomm hsmallerR1 beta
      hbeta hpairRank huB hu huz hescape
  obtain ⟨-, U', hU'set, -, -, -, -, -, -, hmodels, hdoubleM⟩ :=
    hxor.or.resolve_left fun h1 => (by omega : twoRank L ≠ 1) h1.1
  obtain ⟨hker, hroot, hsyl, horb, hlit⟩ :=
    unique_rank_two_centralizer_hull_involutions_and_local_orbits h hcomm hsmallerR1 beta hbeta
      hpairRank u huB hu huz hescape hrank
  dsimp only [rankTwoCentralizerKernelData] at hker
  dsimp only [rankTwoCentralizerRootData] at hroot
  dsimp only [rankTwoCentralizerSylowData] at hsyl
  dsimp only [rankTwoCentralizerOrbitData] at horb
  dsimp only [rankTwoCentralizerLiteralSylowData] at hlit
  obtain ⟨hRcenter, hRodd, -, -, -, -, huL, -⟩ := hker
  obtain ⟨hUelem, hUL, hUHM, hUnormal, hUset, hUset', hUfour, -⟩ := hroot
  obtain ⟨⟨S, hS⟩, hpart, hOmA, -, hdisj, hcommute, -⟩ := hsyl T₁
  obtain ⟨-, -, -, -, -, -, -, hUclass, hprodclass, -⟩ := horb
  obtain ⟨hOmT, -, -, he⟩ := hlit T₁
  have hUU : U' = originalPointRoot H z u :=
    SetLike.coe_injective (hU'set.trans (by rw [Set.inter_right_comm]; exact hUset.symm))
  subst hUU
  set U := originalPointRoot H z u
  have hzU : z ∈ U := by
    rw [← SetLike.mem_coe, hUset]
    exact Or.inr ⟨⟨distinguished_mem_pointClass z, hzM⟩, h.local_datum.distinguished_mem⟩
  have huU : u ∉ U := fun huU => huL (hUL huU)
  have hUbot : U ≠ ⊥ := fun hbot => hz1 (Subgroup.mem_bot.mp (hbot ▸ hzU))
  have hPHM : P ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans hLM)
  have hUP : U ≤ localInvolutionPointHull z u ⊓ H := le_inf hUL (hUHM.trans inf_le_left)
  have hUnormalP : (U.subgroupOf (localInvolutionPointHull z u ⊓ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mpr
      (hPHM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUHM).mp hUnormal))
  have hinvP : ∀ x ∈ localInvolutionPointHull z u ⊓ H, orderOf x = 2 → x ∈ U := by
    intro x hx hxo
    rw [← SetLike.mem_coe, hUset']
    exact Or.inr ⟨hx.1, ⟨hx.2, hLM hx.1⟩, hxo⟩
  have hAM : A ≤ M := (Subgroup.map_subtype_le _).trans inf_le_right
  have hsupA : Subgroup.zpowers u ⊔ U ≤ A := by
    rw [← hOmA]
    exact Subgroup.map_subtype_le _
  have hUA : U ≤ A := le_sup_right.trans hsupA
  have huA : u ∈ A := hsupA (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hAS : centralizerSylowImage u S = A := hS
  have hinto : ∀ x : G, orderOf x = 2 → ∃ g : G, g⁻¹ * x * g ∈ centralizerSylowImage u S := by
    intro x hx
    rw [hAS]
    exact involution_conjugate_into_point_centralizer_sylow h hcomm hbeta hpairRank huB hu hfixM
      T₁ hx
  have : IsSimpleGroup G := hsimple
  obtain ⟨hfused, hinter, -, -, -, hne, hglobal⟩ := three_local_involution_orbits_Zstar_fusion
    hnonab u hu S U hUelem hUbot (hAS ▸ hUA) z hzU hz1 huU (hAS ▸ hpart) hUclass hprodclass
    huclass
  obtain ⟨hallinv, hclassesEq, -, hcard2⟩ := hglobal hinto
  have hinterA : involutionPointClass u ∩ (A : Set G) = (fun x : G => u * x) '' (U : Set G) :=
    hAS ▸ hinter
  have huK : u ∈ K := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_centralizer_iff.mpr fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hLM hl)⟩
  have huUT : (fun x : G => u * x) '' (U : Set G) ⊆ T := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨A.mul_mem huA (hUA hw), Set.mem_mul.mpr ⟨w, hUL hw, u, huK, ?_⟩⟩
    exact (Subgroup.mem_centralizer_iff.mp huK.2) w (hUL hw)
  have hDelta : Δ = (fun x : G => u * x) '' (U : Set G) := by
    refine Set.Subset.antisymm (fun x hx => hinterA ▸ ⟨hx.1, hx.2.1⟩) fun x hx => ⟨?_, huUT hx⟩
    exact (hinterA.symm ▸ hx : x ∈ involutionPointClass u ∩ (A : Set G)).1
  have hd1 : Disjoint ({u} : Set G) ((U : Set G) \ {1}) :=
    Set.disjoint_singleton_left.mpr fun h => huU h.1
  have hd2 : Disjoint ({u} : Set G) ((fun x : G => u * x) '' ((U : Set G) \ {1})) := by
    refine Set.disjoint_singleton_left.mpr ?_
    rintro ⟨w, hw, hwu⟩
    exact hw.2 (mul_eq_left.mp hwu)
  have hd3 : Disjoint ((U : Set G) \ {1}) ((fun x : G => u * x) '' ((U : Set G) \ {1})) := by
    refine Set.disjoint_left.mpr ?_
    rintro x hx ⟨w, hw, rfl⟩
    exact huU (by simpa using U.mul_mem hx.1 (U.inv_mem hw.1))
  refine ⟨⟨hsimple, hnonab⟩, hLeq, hrank, hRcenter, hRodd, U, hUset,
    hUelem, hUfour, omega_one_sylow_eq_of_normal_elementary hUP hUnormalP hUelem hinvP R,
    ⟨hzU, hz1⟩, ?_, hdoubleM, ⟨S, hS⟩, huL, hOmT, hdisj, hcommute, he, hpart, hd1, hd2, hd3,
    hUclass, inter_mul_centralizer_inf_eq hAM hLM, hfused, hinterA, hDelta, ?_, hallinv, hne,
    hclassesEq, hcard2⟩
  · rcases hmodels with ⟨hΓ, f, hf, hq, hlin⟩ | ⟨hΓ, m, hm, hq, hsuz⟩ | hunit
    · exact Or.inl ⟨hΓ, f, hf, hq, by rw [hq]; exact GaloisField.card 2 f (by omega), hlin⟩
    · exact Or.inr (Or.inl ⟨hΓ, m, hm, hq, by rw [hq]; exact GaloisField.card 2 _ (by omega),
        hsuz⟩)
    · exact Or.inr (Or.inr hunit)
  · rw [hDelta, Nat.card_image_of_injective (mul_right_injective u)]
    rfl

end CFSG.ProperTwoGeneratedCore.RankOnePair
