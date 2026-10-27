module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank
public import CFSG.GH74.Filter.Orthogonal.EvenEichler
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4InputsLinear
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.GH74.Filter CFSG.ClassicalGroups.Orthogonal CFSG.SectionRank
  CFSG.SectionRank.ClassicalOdd CFSG.Assembly.LowTwoRank QuadraticMap Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LieType.Universal.Spin

section EichlerChar

variable {ι : Type} {K : Type} [Field K] {Q : QuadraticForm K (ι → K)}

theorem d3_card_hypComplement_char [Fintype ι] [Finite K] {p f : ℕ} (hK : Nat.card K = p ^ f)
    (P : HypPair Q) :
    Nat.card (Multiplicative (hypComplement P)) = p ^ (f * (Fintype.card ι - 2)) := by
  rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := K),
    finrank_hypComplement, hK, ← pow_mul]

variable [Fintype ι] [DecidableEq ι]

theorem d3_le_pRank_statedProj_statedOmega_char [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (P : HypPair Q)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    f * (Fintype.card ι - 2) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) := by
  have hΩ := statedOmega_eq_map_elementaryGroup hQ hE
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (fun a => pow_char_eq_one (K := K) (p := p) a) (d3_card_hypComplement_char hK P)
    (eichlerRootHom P) (eichlerRootHom_injective P) (fun a => ?_) (v := P.e) P.e_ne_zero
    (eichlerRootHom_apply_e P)
  rw [hΩ]
  refine Subgroup.mem_map.2 ⟨eichler Q P.e (a.toAdd : ι → K), eichler_mem_elementaryGroup Q _ _, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, toLinEquiv_eichlerRootHom]

end EichlerChar

theorem d3AbelianSix_holds : D3AbelianSix := by
  intro K _ _ n hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 :=
    CFSG.Wreathed.OriginalAllPrime.V4InputsW.charP_of_card_eq_pow Nat.prime_three hK
  let e0 : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have h := d3_le_pRank_statedProj_statedOmega_char (p := 3) hK (coe_quadPlus 4 K)
    (plusPair K (⟨0, by norm_num⟩ : Fin 4)) (commutator_orthogonalGroup_quadPlus (by norm_num))
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e0] at h
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (D4Model K))
  refine ⟨E, hE, ?_⟩
  rw [hEcard]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GLTheoremA
