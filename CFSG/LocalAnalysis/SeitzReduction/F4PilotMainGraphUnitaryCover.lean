module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesCovers
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank

theorem forall_exists_section_of_mulEquiv {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M'), Function.Surjective π' →
      π'.ker ≤ center E' → ∃ s : M' →* E', ∀ g, π' (s g) = g) :
    ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → ∃ s : M →* E', ∀ g, π' (s g) = g := by
  intro E' _ _ π' hπ' hcen
  have hker : (e.toMonoidHom.comp π').ker = π'.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  obtain ⟨s, hs⟩ := hsplit E' (e.toMonoidHom.comp π') (e.surjective.comp hπ') (hker ▸ hcen)
  refine ⟨s.comp e.toMonoidHom, fun g => e.injective ?_⟩
  exact hs (e g)

section Closed


theorem statedSU_even_split {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (he : Even n) (hn : 4 ≤ n) (hq : 4 ≤ 2 ^ f) :
    ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* StatedSU n (2 ^ f) F),
      Function.Surjective π' → π'.ker ≤ center E' → ∃ s : StatedSU n (2 ^ f) F →* E',
        ∀ g, π' (s g) = g :=
  fun _ _ _ _ hπ' hcen => statedSU_exists_section_of_central_two hF he hn hq hπ' hcen

theorem statedSU_odd_split {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n)
    (hq : 4 ≤ 2 ^ f) :
    ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* StatedSU n (2 ^ f) F),
      Function.Surjective π' → π'.ker ≤ center E' → ∃ s : StatedSU n (2 ^ f) F →* E',
        ∀ g, π' (s g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E' _ _ π' hπ' hcen
  exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
    (p := 2) hF hf hn ho (fun h32 => by
      have h2 : 2 ^ f = 2 := (Prod.mk_inj.1 h32).2
      omega) hπ' hcen

end Closed

section Neighbour


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_su7_cover_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .unitary7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 2 ∧
      ∃ Φ : StatedSU 7 (2 ^ f) F →* G, Φ.range = neighbourCore e N ∧
        Φ.ker ≤ center (StatedSU 7 (2 ^ f) F) := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨S, _, hS, ρ, hρ, hker⟩ := exists_surjective_neighbourCore_of_hr8Kind_graph hw hf e hN
    (by decide) (by decide) h
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (2 ^ f) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 7 (2 ^ f) F)) := by
    rcases hS with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * f) (by rw [hF, ← pow_mul,
    mul_comm])
  set M := StatedSU 7 (2 ^ f) F
  set π : M →* StatedProj M := QuotientGroup.mk' ((StatedScalars (Fin 7) F).subgroupOf M)
  set ρ' : neighbourCore e N →* StatedProj M := ε.toMonoidHom.comp ρ
  have hρ' : Function.Surjective ρ' := ε.surjective.comp hρ
  have hker' : ρ'.ker ≤ center (neighbourCore e N) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact ε.map_eq_one_iff.mp hx
  have : Group.IsPerfect (neighbourCore e N) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central π (QuotientGroup.mk'_surjective _)
    (statedSU_odd_split hF (by omega) (by norm_num) (by decide) hq4) ρ' hρ' hker'
  refine ⟨F, inferInstance, inferInstance, hF, (neighbourCore e N).subtype.comp Φ₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro g hg
    have hg₀ : Φ₀ g = 1 := (neighbourCore e N).subtype_injective (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact statedScalars_subgroupOf_le_center M h1

end Neighbour

end CFSG.SeitzReduction.F4Pilot
