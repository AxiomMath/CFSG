module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogResidualNarrow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
public import Certificates.Certificate9419
import all CFSG.Blueprint.NativeSporadic
import CFSG.Assembly.OpenBridges
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSporOrder
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import Certificates.Data.CFSGNative.CTP.StrongP

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.Blueprint

theorem not_rankThreeUC_of_tcGenDatum {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (hS : Standing G) (e : G ≃* H) (h3 : 3 ∈ rankThreeSigmaA G) (hTC : TCGenDatum H 3) :
    ¬ rankThreeUC G := by
  intro hUC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC 3 h3
  let T : Sylow 3 H := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hT : (T : Subgroup H) = (P : Subgroup G).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hcore : GLBWeakCore 3 (T : Subgroup H) = ⊤ := weakCoreOfTC H 3 hTC T
  have hP : (P : Subgroup G) = (T : Subgroup H).map e.symm.toMonoidHom := by
    rw [hT, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [this, Subgroup.map_id]
  have hcoreG : GLBWeakCore 3 (P : Subgroup G) = ⊤ :=
    glbWeakCore_eq_top_of_mulEquiv Nat.prime_three e.symm hP hcore
  have hΓ : rankThreeGamma 2 3 (P : Subgroup G) = ⊤ :=
    top_le_iff.mp (hcoreG ▸ CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore 3 _)
  have hM : M = ⊤ := top_le_iff.mp (hΓ ▸ hw.u0)
  have := hS.simple
  exact twoLocal_ne_top hS.nonab M hw.maxLocal.1 hM

section SigmaA

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Census

theorem three_mem_rankThreeSigmaA_of_mulEquiv {G H : Type} [Group G] [Finite G] [Group H]
    (hS : Standing G) (e : G ≃* H) {N : ℕ} (hN : Nat.card H = N)
    (h5 : ∀ [Finite H], localRank 5 H ≤ 2)
    (hq : ∀ q : ℕ, q.Prime → 5 < q → ¬ q ^ 3 ∣ N) : 3 ∈ rankThreeSigmaA G := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  have hrank : CFSG.Assembly.evenRank G = 3 := (CFSG.Assembly.evenRank_eq_open G).trans hS.rank
  have hT : {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨hq1, hq2, hq3⟩
    have hle : localRank q H ≤ 2 := localRank_le_two_of_no_cube hq1 fun E _ hcardE =>
      hq q hq1 hq2 (hN ▸ hcardE ▸ Subgroup.card_subgroup_dvd_card E)
    rw [localRank_eq_of_mulEquiv e hq1] at hq3
    omega
  have h5' : localRank 5 G < 3 := by
    rw [localRank_eq_of_mulEquiv e Nat.prime_five]
    have := h5
    omega
  have hsig := (rank_three_selector_of_three hrank hT h5').1
  have h3 : (3 : ℕ) ∈ sigmaA G := by rw [hsig]; exact Set.mem_singleton 3
  exact h3

end SigmaA

theorem cube_free_co2 : ∀ q : ℕ, q.Prime → 5 < q → ¬ q ^ 3 ∣ 42305421312000 := by
  have h := not_pow_three_dvd_of_primeFactors (N := 42305421312000) (by norm_num)
    {2, 3, 5, 7, 11, 23} {3, 5} (by norm_num [Nat.primeFactors]) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  intro q hq hq5
  exact h q hq (by omega) (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)

theorem cube_free_th : ∀ q : ℕ, q.Prime → 5 < q → ¬ q ^ 3 ∣ 90745943887872000 := by
  have h := not_pow_three_dvd_of_primeFactors (N := 90745943887872000) (by norm_num)
    {2, 3, 5, 7, 13, 19, 31} {3, 5} (by norm_num [Nat.primeFactors]) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  intro q hq hq5
  exact h q hq (by omega) (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.Co2Three

theorem not_rankThreeUC_of_Co2
    {G : Type} [Group G] [Finite G] (hS : Standing G)
    (e : G ≃* NativeSporadic.Carrier .Co2) : ¬ rankThreeUC G := by
  have hcard : Nat.card NativeSporadic.Co2 = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have h5 : ∀ [Finite NativeSporadic.Co2],
      CFSG.Assembly.RankThreeEven.localRank 5 NativeSporadic.Co2 ≤ 2 := by
    intro _
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
      (spec2 22).cubic_of_check co2Sylow5Data co2_sylow5_check
    exact localRank_le_two_of_cubic Nat.prime_five (by rw [hcard]; norm_num) hz hc
  have h3 := three_mem_rankThreeSigmaA_of_mulEquiv hS e hcard h5 cube_free_co2
  have : Finite (NativeSporadic.Carrier .Co2) := Finite.of_equiv G e.toEquiv
  exact not_rankThreeUC_of_tcGenDatum hS e h3
    (tcGenDatum_of_check (spec2 22) (D := tcSpec) Nat.prime_three
      Certificates.certificate9419.1)

theorem not_rankThreeUC_of_Th
    {G : Type} [Group G] [Finite G] (hS : Standing G)
    (e : G ≃* NativeSporadic.Carrier .Th) : ¬ rankThreeUC G := by
  have hcard : Nat.card NativeSporadic.Th = 90745943887872000 := card_Th
  have h5 : ∀ [Finite NativeSporadic.Th],
      CFSG.Assembly.RankThreeEven.localRank 5 NativeSporadic.Th ≤ 2 := by
    intro _
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
      (spec2 248).cubic_of_check thSylow5Data th_sylow5_check
    exact localRank_le_two_of_cubic Nat.prime_five (by rw [hcard]; norm_num) hz hc
  have h3 := three_mem_rankThreeSigmaA_of_mulEquiv hS e hcard h5 cube_free_th
  have : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv G e.toEquiv
  exact not_rankThreeUC_of_tcGenDatum hS e h3 tcGenDatum_Th_three

theorem catalogNoUCSporadic_of_certificates
    (G : Type) [Group G] [Finite G] : CatalogNoUCSporadic G := by
  intro hS h
  rcases h with h | h
  · exact h.elim fun e => not_rankThreeUC_of_Co2 hS e
  · exact h.elim fun e => not_rankThreeUC_of_Th hS e

end CFSG.LocalAnalysis.RankThreeUC
