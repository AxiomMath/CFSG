module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutGen
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.AltSix
public import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
open CFSG.RankThree.PartOne.OutStructure

theorem outTwoCyclic_alt_five_eight {K : Type} [Group K] [Finite K] {n : ℕ}
    (hn : n = 5 ∨ n = 8) (e : K ≃* alternatingGroup (Fin n)) : OutTwoCyclic K := by
  have hdvd : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n))).index ∣ 2 :=
    CFSG.Quasithin.SteinbergCB.index_inner_dvd_two (by omega)
  have hA : OutTwoCyclic (alternatingGroup (Fin n)) := by
    refine outTwoCyclic_of_not_four_dvd_card_outer ?_
    have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (alternatingGroup (Fin n))) =
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (alternatingGroup (Fin n))).index := by
      rw [Subgroup.index_eq_card]
    rw [hcard]
    intro h4
    exact absurd (h4.trans hdvd) (by norm_num)
  exact outTwoCyclic_of_mulEquiv e hA

theorem outTwoCyclic_alt_six {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) : OutTwoCyclic K :=
  outTwoCyclic_of_mulEquiv e
    (outTwoCyclic_of_noKlein_of_card_outer_le_four
      CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.noKlein_alternatingGroup_six
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four)

section SmallPSL

open CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem card_outer_PSL2_prime_two {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hK : Nat.card K = r) (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSL2 K)) = 2 := by
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : Inn (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  have hidx : (Inn (PSL2 K)).index = 2 := by
    rw [hInn, h2, pgl2_psl2Range_index_eq_two K hodd]
  have hdef : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSL2 K)) =
      (Inn (PSL2 K)).index := by
    rw [Subgroup.index_eq_card]
  rw [hdef]
  exact hidx

theorem outTwoCyclic_A1_seven {Y : Type} [Group Y] [Finite Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : OutTwoCyclic Y := by
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  have hq' : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
  rw [hp7, he1] at h
  have h' : StatedClassicalModel Y .PSL 2 7 1 := h
  refine outTwoCyclic_of_not_four_dvd_card_outer ?_
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := h'
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : Y ≃* PSL2 K := e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv,
    card_outer_PSL2_prime_two hK7 hodd hcard]
  norm_num

end SmallPSL

section SmallPSU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

theorem outTwoCyclic_twistedA2_three {Y : Type} [Group Y] [Finite Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : OutTwoCyclic Y := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hq' : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
  rw [hp3, he1] at h
  have h' : StatedClassicalModel Y .PSU 3 3 1 := h
  apply outTwoCyclic_of_outPNice_two
  obtain ⟨⟨hℓ, hm, hn3, -⟩, K, _, _, hK, ⟨e0⟩⟩ := h'
  have hU : UnitaryFieldData 3 1 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq2 : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by decide
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) hn3 hq2
  have e' : Y ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e0.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact OutPNice.of_mulEquiv e' (outPNice_primeFormP hU hn3 hq2 Nat.prime_two (by norm_num))

end SmallPSU

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
