module

public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreRee
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter

public section

namespace CFSG.AGLEmbedding.RankOneAut

open CFSG.Open CFSG.LieType.Ree CFSG.AGLEmbedding.KFactProofs.RankOneCore
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.ComponentClassification.LiteratureLocal.SmallRee (outer_reeGamma_cyclic)

open scoped commutatorElement Pointwise

theorem commutator_mem_of_borel_eq_torus_mul {G : Type*} [Group G] {B U H : Subgroup G}
    (hBHU : (B : Set G) = (H : Set G) * (U : Set G)) (hUn : (U.subgroupOf B).Normal)
    (hH : ∀ g ∈ H, ∀ g' ∈ H, g * g' = g' * g) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    ⁅x, y⁆ ∈ U := by
  have hHB : ∀ g ∈ H, g ∈ B := fun g hg => by
    have : g ∈ (B : Set G) := by rw [hBHU]; exact ⟨g, hg, 1, U.one_mem, mul_one g⟩
    exact this
  let π : B →* B ⧸ U.subgroupOf B := QuotientGroup.mk' _
  have key : ∀ z (hz : z ∈ B), ∃ g, ∃ hg : g ∈ H, π ⟨z, hz⟩ = π ⟨g, hHB g hg⟩ := by
    intro z hz
    have hz' : z ∈ (B : Set G) := hz
    rw [hBHU] at hz'
    obtain ⟨g, hg, u, hu, rfl⟩ := hz'
    refine ⟨g, hg, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (g * u)⁻¹ * g ∈ U
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem hu
  obtain ⟨g, hg, hxg⟩ := key x hx
  obtain ⟨g', hg', hyg⟩ := key y hy
  have h1 : π ⁅(⟨x, hx⟩ : B), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, hxg, hyg, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext (hH g hg g' hg')), map_one]
  have h2 : ⁅(⟨x, hx⟩ : B), ⟨y, hy⟩⁆ ∈ U.subgroupOf B := (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [commutatorElement_def] using h2

section Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem commutator_stdB_le_stdU :
    ⁅ReeModel.stdB a K, ReeModel.stdB a K⁆ ≤ ReeModel.stdU a K := by
  obtain ⟨hBHU, -, -, -, hUn, -, hHc, -⟩ := ReeTag.ree_fixed_Bruhat_decomposition ReeTag.G2 a K
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h := commutator_mem_of_borel_eq_torus_mul hBHU hUn hHc (Subgroup.mem_subgroupOf.1 hx)
    (Subgroup.mem_subgroupOf.1 hy)
  rw [ReeModel.stdU, Subgroup.mem_subgroupOf]
  simpa [commutatorElement_def] using h

theorem borelMetabelianAt_stdU (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    BorelMetabelianAt (ReeTag.G2.reeGamma K a) (ReeModel.stdU a K) := by
  obtain ⟨-, hNU, -, -⟩ := ReeModel.std_facts hK
  have hinj := mulAutConj_injective_of_center_eq_bot (ReeTag.center_reeGamma_G2_eq_bot hK)
  have hcyc := (outer_reeGamma_cyclic ha hK).1
  refine borelMetabelianAt_of_outer hinj (fun α β => ?_)
    (by rw [hNU]; exact commutator_stdB_le_stdU)
  have hc : (QuotientGroup.mk' (inner (ReeTag.G2.reeGamma K a))) ⁅α, β⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcyc.commGroup.mul_comm _ _
  exact (QuotientGroup.eq_one_iff _).1 hc

end Model

theorem rankOneLieAutFacts_ree {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* CatGroup d)) :
    RankOneLieAutFacts 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, -, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have : Finite (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) := Finite.of_equiv L e.toEquiv
  refine ⟨?_, kSylowTI_of_rankOneCoreData (rankOneCoreData_ree hd h), ?_⟩
  · exact kOutRankLeOne_of_outPChain Nat.prime_three
      (CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
        (CFSG.RankThree.PartOne.OutStructure.outPNice_of_isCyclic_outer Nat.prime_three
          (outer_reeGamma_cyclic ha hK).1)).toChain
  · intro U
    obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
    obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
    exact BorelMetabelianAt.of_equiv e' (he'.trans hP) (borelMetabelianAt_stdU ha hK)

end CFSG.AGLEmbedding.RankOneAut
