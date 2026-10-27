module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHullModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped Pointwise LinearAlgebra.Projectivization

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_arbitrary_involution_centralizer_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    {u : G} (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let α := rightCosetMk H 1
    let D := involutionPointClass z
    let Y := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let R := (CFSG.oddCore Y).map Y.subtype
    let RL := (CFSG.oddCore L).map L.subtype
    let Δ := elementFixedSet H u
    let π := QuotientGroup.mk' (CFSG.oddCore L)
    letI := hullFixedSetAction H z u
    letI := originalCentralizerFixedSetAction H u
    Y < ⊤ ∧ (L.subgroupOf Y).Normal ∧ fusionStronglyEmbedded (H.subgroupOf L) ∧
      D ∩ (Y : Set G) = conjugacyWithin Y z ∧ conjugacyWithin Y z = conjugacyWithin L z ∧
      Δ = numeratorRightOrbit H Y α ∧ Δ = numeratorRightOrbit H L α ∧
      Xor
        (twoRank L = 1 ∧ D ∩ (H : Set G) ∩ (Y : Set G) = {z} ∧
          (QuotientGroup.mk (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩ : Y) :
              Y ⧸ CFSG.oddCore Y) ∈ Subgroup.center (Y ⧸ CFSG.oddCore Y) ∧
          (Y : Set G) = (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (R : Set G) ∧
          H ⊓ Y = Y ⊓ Subgroup.centralizer ({z} : Set G))
        (2 ≤ twoRank L ∧
          ∃ U : Subgroup G, (U : Set G) = {1} ∪ (D ∩ (H : Set G) ∩ (Y : Set G)) ∧
            IsElementaryAbelian 2 U ∧ 4 ≤ Nat.card U ∧
            (∀ x ∈ (U : Set G) \ {1}, ∀ y ∈ (U : Set G) \ {1},
              ∃ c ∈ H ⊓ Y, rightConjugateElem x c = y) ∧
            R ≤ H ∧ ⁅R, L⁆ = ⊥ ∧ RL ≤ R ⊓ (Subgroup.center L).map L.subtype ∧
            ((Nat.card Δ = Nat.card U + 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
                ∃ (E : L ⧸ CFSG.oddCore L ≃* PSL2BinaryMatrixGroup f)
                  (ψ : Δ ≃ ℙ (BinaryGaloisField f) (Fin 2 → BinaryGaloisField f)),
                  (∀ δ : Δ, (δ : pointRightCosetSpace H) = α →
                    ψ δ = Projectivization.mk (BinaryGaloisField f)
                      (![1, 0] : Fin 2 → BinaryGaloisField f) (by simp)) ∧
                  ∀ (l : L) (δ : Δ), ψ (l • δ) = E (π l) • ψ δ) ∨
              (Nat.card Δ = Nat.card U ^ 2 + 1 ∧ ∃ m : ℕ, 1 ≤ m ∧
                Nat.card U = 2 ^ (2 * m + 1) ∧
                letI := suzukiOvoidAction m
                ∃ (E : L ⧸ CFSG.oddCore L ≃* SuzukiMatrixGroup m)
                  (ψ : Δ ≃ {p // p ∈ suzukiOvoidSet m}),
                  (∀ δ : Δ, (δ : pointRightCosetSpace H) = α →
                    (ψ δ : ℙ (BinaryGaloisField (2 * m + 1))
                      (Fin 4 → BinaryGaloisField (2 * m + 1))) = suzukiOvoidInfinity m) ∧
                  ∀ (l : L) (δ : Δ), ψ (l • δ) = E (π l) • ψ δ) ∨
              (Nat.card Δ = Nat.card U ^ 3 + 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
                ∃ (K : Type) (_ : Field K) (_ : Finite K) (A : HermitianForm 3 K)
                  (hA : A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
                  Nat.card K = Nat.card U ^ 2 ∧
                  Nat.card {x : K // A.conj x = x} = Nat.card U ∧
                  ∃ ρ : ProjectiveSpecialUnitaryMatrixGroup A →*
                      Equiv.Perm (unitaryIsotropicPoints A),
                    (∀ g p, ((ρ g p : unitaryIsotropicPoints A) : ℙ K (Fin 3 → K)) =
                      (g : Matrix.ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K))) ∧
                    ∃ (E : L ⧸ CFSG.oddCore L ≃* ProjectiveSpecialUnitaryMatrixGroup A)
                      (ψ : Δ ≃ unitaryIsotropicPoints A),
                      (∀ δ : Δ, (δ : pointRightCosetSpace H) = α →
                        ψ δ = unitaryOuterIsotropicPoint A hA 0 (by decide)) ∧
                      ∀ (l : L) (δ : Δ), ψ (l • δ) = ρ (E (π l)) (ψ δ))) ∧
            MulAction.IsMultiplyPretransitive Y Δ 2) := by
  intro α D Y L R RL Δ π
  let := hullFixedSetAction H z u
  classical
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  obtain ⟨hYlt, hLnormal, hrank1, hP⟩ :=
    original_centralizer_hull_normal_rank_and_embedding h u hu huz hescape
  have hclassY : D ∩ (Y : Set G) = conjugacyWithin Y z := by
    rw [← original_centralizer_class_image h.local_datum u hu huz hescape]
    exact internal_pointClass_image Y hzY
  have hLeq : Subgroup.closure (conjugacyWithin Y z) = L :=
    original_centralizer_properHull_eq h.local_datum u hu huz hescape
  have hdich := minimalLocalFailure_proper_local_hull_dichotomy h hcomm hsmallerR1 hYlt hzY
    hescape
  dsimp only at hdich
  rw [hLeq] at hdich
  obtain ⟨-, hYL, hxor⟩ := hdich
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    apply point_centralizer_le h.local_datum
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨s, hs⟩)
  have hfusion := unique_central_sylow_involution_centralizers_transitive_fixed_set S H hSH z
    hzS hzcenter h.local_datum.distinguished_order h.local_datum.unique_containment
  have hfixY : Δ = numeratorRightOrbit H Y α := by
    change elementFixedSet H u =
      numeratorRightOrbit H (Subgroup.centralizer ({u} : Set G)) (rightCosetMk H 1)
    simpa only [elementFixedSet, numeratorRightOrbit, pointRightCosetMul_eq_translate]
      using (hfusion u huH hu).1
  have hfixL : Δ = numeratorRightOrbit H L α :=
    original_central_sylow_local_hull_full_fixed_set h.local_datum S hzS hzcenter u huH hu
      huz hescape
  refine ⟨hYlt, hLnormal, hP, hclassY, hYL, hfixY, hfixL, ?_⟩
  have hrank1' : 1 ≤ twoRank L := hrank1
  rcases Nat.lt_or_ge (twoRank L) 2 with hlt | hr2
  · have hr1 : twoRank L = 1 := by omega
    left
    obtain ⟨-, hzcenterY, hYfac, hHY, hclassH⟩ :=
      hxor.elim (fun h => h.1) (fun h => absurd h.1.1 (by omega))
    refine ⟨⟨hr1, ?_, hzcenterY, hYfac, hHY⟩, fun hii => by omega⟩
    change involutionPointClass z ∩ (H : Set G) ∩ (Y : Set G) = {z}
    rw [(hfusion z h.local_datum.distinguished_mem h.local_datum.distinguished_order).2.2]
    exact hclassH
  · right
    refine ⟨?_, fun hi => by omega⟩
    obtain ⟨helem, -, -, -, hUset, -, hfour, -, -, -, -, -, hcore, -, -, hdoubleM,
      a, i, ha, -, hcard, -, -, hfixcard, ⟨phi, hphi0, hphiEq⟩, hfamily⟩ :=
      original_rank_two_centralizer_root_data h hcomm hsmallerR1 u huH hu huz hescape hr2
    obtain ⟨hRH, hRL, hRLR, hRLcenter, -, -⟩ :=
      original_centralizer_rank_two_retained_odd_cores h hcomm hsmallerR1 u hu huz hescape hr2
    have hUset' : (originalPointRoot H z u : Set G) =
        {1} ∪ (D ∩ (H : Set G) ∩ (Y : Set G)) := by
      rw [hUset, Set.inter_right_comm]
    have hmemU : ∀ x ∈ (originalPointRoot H z u : Set G) \ {1}, x ∈ involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G) := by
      rintro x ⟨hxU, hx1⟩
      rw [hUset] at hxU
      exact hxU.resolve_left hx1
    refine ⟨hr2, originalPointRoot H z u, hUset', helem, hfour,
      fun x hx y hy => original_point_centralizer_transitive_distinguished_set h.local_datum u
        huz hP x y (hmemU x hx) (hmemU y hy),
      hRH, hRL, le_inf hRLR (Subgroup.map_mono hRLcenter), ?_, hdoubleM⟩
    let B := (H.subgroupOf L).map π
    have hBse : fusionStronglyEmbedded B := by
      have hsup : H.subgroupOf L ⊔ CFSG.oddCore L ≠ ⊤ := by
        rw [sup_eq_left.mpr hcore]
        exact hP.1
      exact (strongly_embedded_odd_quotient_and_proper_overgroups (H.subgroupOf L)
        (CFSG.oddCore L) hP (CFSG.ComponentClassification.OddCore.odd_card L) hsup).1
    rcases hfamily with ⟨rfl, ⟨E₀⟩⟩ | ⟨rfl, m, rfl, ⟨E₀⟩⟩ |
      ⟨rfl, K, hK, hKfin, A, hA, hKcard, hfixedK, ⟨E₀⟩⟩
    · left
      have : Finite (PSL2BinaryMatrixGroup a) := Finite.of_equiv _ E₀.toEquiv
      obtain ⟨hrankX, hstabX⟩ := linear_standard_point_model a ha
      obtain ⟨E, ψ₀, hψ₀, hψeq⟩ := exists_quotient_point_action_equiv hrankX B E₀
        (hBse.map_mulEquiv E₀) _ hstabX
      refine ⟨by simpa using hfixcard, a, ha, hcard, E, phi.trans ψ₀, fun δ hδ => ?_,
        fun l δ => ?_⟩
      · change ψ₀ (phi δ) = _
        rw [hphi0 δ hδ, hψ₀]
      · change ψ₀ (phi (l • δ)) = E (π l) • ψ₀ (phi δ)
        rw [hphiEq, hψeq]
    · right
      left
      have hm : 1 ≤ m := by omega
      let := suzukiOvoidAction m
      have : Finite (SuzukiMatrixGroup m) := Finite.of_equiv _ E₀.toEquiv
      obtain ⟨hrankX, htransX, hstabX⟩ := suzuki_standard_point_model m hm
      obtain ⟨E, ψ₀, hψ₀, hψeq⟩ := exists_quotient_point_action_equiv hrankX B E₀
        (hBse.map_mulEquiv E₀) _ hstabX
      refine ⟨hfixcard, m, hm, hcard, E, phi.trans ψ₀, fun δ hδ => ?_, fun l δ => ?_⟩
      · change ((ψ₀ (phi δ) : {p // p ∈ suzukiOvoidSet m}) :
          ℙ (BinaryGaloisField (2 * m + 1)) (Fin 4 → BinaryGaloisField (2 * m + 1))) = _
        rw [hphi0 δ hδ, hψ₀]
      · change ψ₀ (phi (l • δ)) = E (π l) • ψ₀ (phi δ)
        rw [hphiEq, hψeq]
    · right
      right
      obtain ⟨ρ, hρ, hrankX, htransX, hstabX⟩ :=
        unitary_standard_point_model A a ha hKcard hfixedK hA
      let := MulAction.compHom (unitaryIsotropicPoints A) ρ
      have : Finite (ProjectiveSpecialUnitaryMatrixGroup A) := Finite.of_equiv _ E₀.toEquiv
      obtain ⟨E, ψ₀, hψ₀, hψeq⟩ := exists_quotient_point_action_equiv hrankX B E₀
        (hBse.map_mulEquiv E₀) _ hstabX
      refine ⟨hfixcard, a, ha, hcard, K, hK, hKfin, A, hA, by rw [hcard]; exact hKcard,
        by rw [hcard]; exact hfixedK, ρ, hρ, E, phi.trans ψ₀, fun δ hδ => ?_,
        fun l δ => ?_⟩
      · change ψ₀ (phi δ) = _
        rw [hphi0 δ hδ, hψ₀]
      · change ψ₀ (phi (l • δ)) = E (π l) • ψ₀ (phi δ)
        rw [hphiEq, hψeq]

end CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
