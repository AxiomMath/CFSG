module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpSurvivor
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Glue
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_b_outer (hP : BlockIbParab Lb Pb) (hX : IsLieOf IdxB (↥Lb ⧸ Subgroup.center ↥Lb))
    (hD : BlockIbData Lb Pb D x) (U : Subgroup Y)
    (hUL : U ≤ Subgroup.normalizer (Lb : Set Y)) (hUP : U ≤ Subgroup.normalizer (Pb : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∃ (G : Type) (_ : Group G) (φ : ↥U →* G),
      (∀ u : ↥U, φ u = 1 → (u : Y) ∈ Subgroup.centralizer (Lb : Set Y)) ∧
      (∀ a b : ↥U, φ a * φ b = φ b * φ a) ∧ Nat.card φ.range ≤ 3 := by
  rcases isLieOf_idxB_cases hX with hc | hres
  · exact (blockIb_false_of_centPerfectNoncyc kFactCentNoncycThree_b hP hc hD).elim
  have hLperf : Group.IsPerfect ↥Lb := Group.isPerfect_def.mpr hP.comp.2.2.1
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hres
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd.1
    have hmodel : StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by rcases hPd.2 with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega) e
        rwa [hq2] at hm
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hcardK : Nat.card K = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hq2]
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcard
    have hr0 : 1 ≤ r := by rcases hPd.2 with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega
    have : NeZero r := ⟨by omega⟩
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcard).1
    let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    have hfin : Finite (StatedSp r K) := by
      have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv _ e'.toEquiv
      exact Finite.of_equiv _ π.toEquiv.symm
    let ee : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* StatedSp r K := e'.trans π.symm
    rcases hPd.2 with ⟨h4, hr2⟩ | ⟨h2, h34⟩
    · subst hr2
      obtain ⟨v, hbar⟩ := exists_blockBar hP hD ee
      exact (false_of_blockBar_sp_four (K := K) (by rw [hcardK]; exact h4) hbar).elim
    · obtain ⟨ψ'⟩ := nonempty_statedSp_mulEquiv_zmod_two (K := K) r (by rw [hcardK]; exact h2)
      let ee2 := ee.trans ψ'
      obtain ⟨v, hbar⟩ := exists_blockBar hP hD ee2
      obtain ⟨hr3, g, hg⟩ := blockBar_sp_cases (by omega) hbar
      subst hr3
      obtain ⟨T, hT, hNJ⟩ := hbar.parab
      obtain ⟨φ, hker, hcomm, hcard3⟩ := exists_outer_hom hLperf ee2 out_trivial_statedSp_three
        (J := (Pb.subgroupOf Lb).map
          (ee2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb)))) rfl
        (fun a ha => mem_of_normalizes_parabolic hT hNJ ha)
        (fun A hA hA3 => card_pGroup_le_three_conj hg A hA hA3) U hUL hUP hU3
      exact ⟨_, inferInstance, φ, hker, hcomm, hcard3⟩
  | _ => exact hPd.elim

theorem blockIbRankFam_b : BlockIbRankFam (IsLieOf IdxB) := by
  intro Y _ _ Lb Pb D x hP hX hD E hEL hEP hED hEab hE9 t ht htE htF
  have hE3 : IsPGroup 3 E := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 2) hE9
  obtain ⟨G, _, φ, hker, -, hcard⟩ := blockIb_b_outer hP hX hD E hEL hEP hE3
  intro hbot
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : (u : Y) ∈ E ⊓ Subgroup.centralizer (Lb : Set Y) := ⟨u.2, hker u hu⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have : Finite ↥φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h1 : Nat.card E ≤ Nat.card φ.range :=
    Nat.card_le_card_of_injective φ.rangeRestrict (by
      intro a b hab
      exact hinj (Subtype.ext_iff.1 hab))
  omega

theorem blockIbAbFam_b : BlockIbAbFam (IsLieOf IdxB) := by
  intro Y _ _ Lb Pb D x hP hX hD U hUL hUP hUD hU3 a ha b hb
  obtain ⟨G, _, φ, hker, hcomm, -⟩ := blockIb_b_outer hP hX hD U hUL hUP hU3
  have h1 : φ ⟨a * b * a⁻¹ * b⁻¹, U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha))
      (U.inv_mem hb)⟩ = 1 := by
    have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
    rw [show (⟨a * b * a⁻¹ * b⁻¹, U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha))
      (U.inv_mem hb)⟩ : ↥U) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ from rfl]
    simp only [map_mul, map_inv]
    rw [this]
    group
  exact hker _ h1

end CFSG.HardMathSupport.Curtis.UnitaryLevi
