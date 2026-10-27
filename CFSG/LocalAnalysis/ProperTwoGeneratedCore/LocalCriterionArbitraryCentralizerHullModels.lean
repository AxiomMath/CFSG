module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOvoid
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryPoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryRoot
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open scoped LinearAlgebra.Projectivization MatrixGroups

theorem fusionStronglyEmbedded_stabilizer_of_pretransitive
    {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω] [MulAction.IsPretransitive X Ω]
    {b : Ω} (hb : fusionStronglyEmbedded (MulAction.stabilizer X b)) (ω : Ω) :
    fusionStronglyEmbedded (MulAction.stabilizer X ω) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X b ω
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact hb.map_mulEquiv (MulAut.conj g)

theorem exists_quotient_point_action_equiv
    {J X Ω : Type*} [Group J] [Group X] [Finite X] [MulAction X Ω]
    [MulAction.IsPretransitive X Ω] (hrank : TwoRankAtLeastTwo X)
    (B : Subgroup J) (E₀ : J ≃* X) (hB : fusionStronglyEmbedded (B.map E₀.toMonoidHom))
    (ω₀ : Ω) (hω₀ : fusionStronglyEmbedded (MulAction.stabilizer X ω₀)) :
    ∃ (E : J ≃* X) (ψ : J ⧸ B ≃ Ω), ψ (QuotientGroup.mk 1) = ω₀ ∧
      ∀ (j : J) (c : J ⧸ B), ψ (j • c) = E j • ψ c := by
  obtain ⟨x, hx⟩ := rank_two_strongEmbedding_conjugate hrank _ _ hB hω₀
  let E : J ≃* X := E₀.trans (MulAut.conj x⁻¹)
  have hE : B.map E.toMonoidHom = MulAction.stabilizer X ω₀ := by
    rw [← hx, Subgroup.map_map]
    rfl
  have hmem : ∀ j : J, j ∈ B ↔ E j • ω₀ = ω₀ := by
    intro j
    rw [← MulAction.mem_stabilizer_iff, ← hE]
    constructor
    · intro hj
      exact Subgroup.mem_map_of_mem _ hj
    · rintro ⟨k, hk, hkj⟩
      rwa [E.injective hkj] at hk
  have hcoset : ∀ a b : J, E a • ω₀ = E b • ω₀ ↔ a⁻¹ * b ∈ B := by
    intro a b
    rw [hmem, map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]
  let ψf : J ⧸ B → Ω := Quotient.lift (fun j => E j • ω₀) fun a b hab =>
    (hcoset a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hψf : ∀ j : J, ψf (QuotientGroup.mk j) = E j • ω₀ := fun _ => rfl
  have hbij : Function.Bijective ψf := by
    constructor
    · intro c d hcd
      induction c using QuotientGroup.induction_on with
      | H a =>
      induction d using QuotientGroup.induction_on with
      | H b =>
      rw [hψf, hψf] at hcd
      exact QuotientGroup.eq.mpr ((hcoset a b).mp hcd)
    · intro ω
      obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X ω₀ ω
      exact ⟨QuotientGroup.mk (E.symm y), by rw [hψf, E.apply_symm_apply, hy]⟩
  refine ⟨E, Equiv.ofBijective ψf hbij, ?_, ?_⟩
  · change ψf (QuotientGroup.mk 1) = ω₀
    rw [hψf, map_one, one_smul]
  · intro j c
    induction c using QuotientGroup.induction_on with
    | H a =>
    change ψf (QuotientGroup.mk (j * a)) = E j • ψf (QuotientGroup.mk a)
    rw [hψf, hψf, map_mul, mul_smul]

theorem linear_standard_point_model (f : ℕ) (hf : 2 ≤ f) :
    TwoRankAtLeastTwo (PSL2BinaryMatrixGroup f) ∧
      fusionStronglyEmbedded (MulAction.stabilizer (PSL2BinaryMatrixGroup f)
        (Projectivization.mk (BinaryGaloisField f) (![1, 0] : Fin 2 → BinaryGaloisField f)
          (by simp))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hSE, -, hrank, -⟩ :=
    LinearModel.linear_rank_one_point_structure f hf (GaloisField.card 2 f (by omega))
  exact ⟨native_rank_two_of_two_le_twoRank hrank, hSE⟩

theorem suzuki_standard_point_model (m : ℕ) (hm : 1 ≤ m) :
    letI := suzukiOvoidAction m
    TwoRankAtLeastTwo (SuzukiMatrixGroup m) ∧
      MulAction.IsPretransitive (SuzukiMatrixGroup m) {p // p ∈ suzukiOvoidSet m} ∧
      fusionStronglyEmbedded (MulAction.stabilizer (SuzukiMatrixGroup m)
        (⟨suzukiOvoidInfinity m, Or.inl rfl⟩ : {p // p ∈ suzukiOvoidSet m})) := by
  let Ω := {p // p ∈ suzukiOvoidSet m}
  let : MulAction (SuzukiMatrixGroup m) Ω := suzukiOvoidAction m
  obtain ⟨rho, b, B, hrho, hB, hrank, hSE, -⟩ := suzuki_model_action_point_and_pair m hm
  change SuzukiMatrixGroup m →* Equiv.Perm Ω at rho
  change Ω at b
  have hrho' : ∀ (g : SuzukiMatrixGroup m) (z : Ω), rho g z = g • z :=
    fun g z => Subtype.ext (hrho g z)
  have hBX : B = MulAction.stabilizer (SuzukiMatrixGroup m) b := by
    rw [hB]
    ext g
    change rho g b = b ↔ g • b = b
    rw [hrho']
  have := suzuki_ovoid_two_transitive m
  have : MulAction.IsPretransitive (SuzukiMatrixGroup m) Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact ⟨hrank, this, fusionStronglyEmbedded_stabilizer_of_pretransitive (hBX ▸ hSE) _⟩

theorem unitary_standard_point_model {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ ρ : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (unitaryIsotropicPoints J),
      (∀ g p, ((ρ g p : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) =
        (g : Matrix.ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K))) ∧
      TwoRankAtLeastTwo (ProjectiveSpecialUnitaryMatrixGroup J) ∧
      letI := MulAction.compHom (unitaryIsotropicPoints J) ρ
      MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J)
          (unitaryIsotropicPoints J) ∧
        fusionStronglyEmbedded (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
          (unitaryOuterIsotropicPoint J hJ 0 (by decide))) := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun g : G => (g : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  obtain ⟨rho, S, D, -, hnat, hSR, -, hnorm, hstab, -, -, -, -, -, -, -, -, htwo⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  let := MulAction.compHom (unitaryIsotropicPoints J) rho
  have hdata := bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ S
  have hU : MulAction.stabilizer G (unitaryOuterIsotropicPoint J hJ 0 (by decide)) =
      Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hSR, hnorm, ← hstab]
    rfl
  have hfour : 4 ≤ Nat.card (Subgroup.center (S : Subgroup G)) := by
    rw [hdata.2.2.2.1]
    simpa using Nat.pow_le_pow_right (n := 2) (by omega) hf
  have : MulAction.IsMultiplyPretransitive G (unitaryIsotropicPoints J) 2 :=
    MulAction.is_two_pretransitive_iff.mpr fun hab hcd => htwo _ _ _ _ hab hcd
  refine ⟨rho, hnat, rank_two_of_sylow_center S hfour hdata.2.2.1,
    MulAction.isPretransitive_of_is_two_pretransitive, ?_⟩
  rw [hU]
  exact hdata.1

end CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
