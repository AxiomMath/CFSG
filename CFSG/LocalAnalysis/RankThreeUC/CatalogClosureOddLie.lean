module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddLinTwo
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate8150
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticComponent
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearFourThree
import CFSG.RankThree.PartTwo.Census.OddClassical.Main
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
import CFSG.RankThree.PartTwo.Census.Carrier.ReeG2One
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.LinearCatalog
import CFSG.Adapters.TauCetiExceptional.BridgeG2
import CFSG.Adapters.TauCetiExceptional.ReeBridge
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.RankThree.PartOne.Census3 TauCeti Matrix
open scoped MatrixGroups

section Orders

theorem card_PSL_three_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 3) K) = 5616 := by
  have := Fintype.ofFinite K
  have hcard : Nat.card (SpecialLinearGroup (Fin 3) K) = 5616 := by
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
    simp [Fin.prod_univ_three]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 3) K))
  rw [center_SL_three_card_eq_one hK, mul_one, hcard] at h
  exact h.symm

theorem card_PSU_three_three {K : Type} [Field K] (hK : Nat.card K = 9) :
    Nat.card (StatedProj (StatedSU 3 3 K)) = 6048 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 3) (f := 1)
    (n := 3) Nat.prime_three le_rfl (by rw [hK]; norm_num) (by norm_num)
  rw [pow_one] at h
  rw [h]
  decide

theorem card_PSU_four_three {K : Type} [Field K] (hK : Nat.card K = 9) :
    Nat.card (StatedProj (StatedSU 4 3 K)) = 3265920 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 3) (f := 1)
    (n := 4) Nat.prime_three le_rfl (by rw [hK]; norm_num) (by norm_num)
  rw [pow_one] at h
  rw [h]
  decide

theorem cube_free_5616 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 5616 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 13} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem cube_free_6048 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 6048 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 7} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem cube_free_4245696 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 4245696 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 7, 13} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem cube_free_3265920 :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({3} : Finset ℕ) → ¬ p ^ 3 ∣ 3265920 := by
  refine not_pow_three_dvd_of_primeFactors (by norm_num) {2, 3, 5, 7} _
    (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Orders

section Items

variable {G : Type} [Group G] [Finite G]

theorem Standing.false_of_item1 (hS : Standing G) (h : ThmThreeItem1 G) : False := by
  obtain ⟨q, hq, -, hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
    rw [GaloisField.card q.p q.exponent hf]
    exact (Nat.Prime.odd_of_ne_two q.prime_p hq).pow
  exact hS.false_of_PSL_two (K := GaloisField q.p q.exponent) (p := q.p) hodd
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv))

end Items

section Certified

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem Standing.false_of_A_two (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.p ≠ 2)
    (e : G ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  by_cases h3 : q.p = 3 ∧ q.exponent = 1
  · have hK : Nat.card (GaloisField q.p q.exponent) = 3 := by
      rw [GaloisField.card _ _ hf, h3.1, h3.2]
      norm_num
    refine hS.false_of_card (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))
      (N := 5616) {3} (card_PSL_three_three hK) ?_ cube_free_5616
    intro _ r hr _ _
    obtain rfl : r = 3 := by simpa using hr
    exact localRank_three_PSL_three_le_of_card_eq_three hK
  · have h5 := five_le_card_of_odd q hq h3
    refine hS.false_of_not_isCharTwoType
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))
      (not_isCharTwoType_PSL_block (m := 1) ?_ (card_galoisField_odd _ _ hq hf) le_rfl)
    rw [GaloisField.card _ _ hf]
    simp only [PrimePower.card_def] at h5
    omega

theorem Standing.false_of_twistedA_two (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p ≠ 2)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : False := by
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have he : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  by_cases h3 : q.p = 3 ∧ q.exponent = 1
  · set K := GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)
    have hK : Nat.card K = 9 := by
      rw [GaloisField.card _ _ (by rw [he, h3.2]; norm_num), hc, he, h3.1, h3.2]
      norm_num
    have hq3 : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
        ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 3 := by
      rw [hc, he, h3.1, h3.2]
      rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
    rw [hq3] at e'
    refine hS.false_of_card e' (N := 6048) {3} (card_PSU_three_three hK) ?_ cube_free_6048
    intro _ r hr _ _
    obtain rfl : r = 3 := by simpa using hr
    exact localRank_three_PSU_three_le hK
  · have h5 := five_le_card_of_odd q hq h3
    have h := unitaryFieldData_galoisField
      (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩) _
      (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 2 q, hv⟩)
    refine hS.false_of_not_isCharTwoType
      ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)).trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := 2 + 1) (by omega)).symm)
      (not_isCharTwoType_unitaryPSU_block h (by rw [hc]; exact hq) ?_ le_rfl)
    rw [hc, he]
    simpa only [PrimePower.card_def] using h5

theorem Standing.false_of_item2 (hS : Standing G) (h : ThmThreeItem2 G) : False := by
  obtain ⟨q, hq, -, h⟩ := h
  rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
  · exact hS.false_of_A_two q hv hq e
  · exact hS.false_of_twistedA_two q hv hq e

theorem Standing.false_of_item3 (hS : Standing G) (h : ThmThreeItem3 G) : False := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hcard : Nat.card (GaloisField 3 (2 * 1 + 1)) = 3 ^ (2 * 1 + 1) :=
    GaloisField.card 3 (2 * 1 + 1) (by omega)
  obtain ⟨f⟩ := CFSG.TauCetiBridge.reeG2Bridge 1 hv (GaloisField 3 (2 * 1 + 1)) hcard
  exact hS.false_of_not_isCharTwoType (e.trans f.symm)
    (not_isCharTwoType_derivedCentralQuotient_reeG2 1 le_rfl _ hcard)

theorem Standing.false_of_G2 (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2) (he1 : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases h3 : q.p = 3
  · have hK : Nat.card (ZMod 3) = q.card := by
      rw [Nat.card_zmod, PrimePower.card_def, h3, he1, pow_one]
    obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (ZMod 3) hK
    refine hS.false_of_card (e.trans b.symm) (N := 4245696) {3} ?_ ?_ cube_free_4245696
    · rw [Nat.card_congr Carrier.G2Three.adjointQuotientEquivR3.toEquiv]
      exact Carrier.G2Three.card_R3
    · intro _ r hr _ _
      obtain rfl : r = 3 := by simpa using hr
      exact Carrier.G2Three.localRank_three_adjointQuotient
  · have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
    obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
    have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
      rw [hK, PrimePower.card_def]
      exact (q.prime_p.odd_of_ne_two hp2).pow
    have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
      rw [hK]
      exact le_trans (by norm_num) (five_le_card_of_odd q hp2 fun h => h3 h.1)
    exact hS.false_of_not_isCharTwoType (e.trans b.symm)
      (Carrier.not_isCharTwoType_adjointQuotient_G2 hodd h4)

theorem Standing.false_of_B_two (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p ≠ 2)
    (e : G ≃* (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) : False := by
  have hdup := (LieTypeIndex.isDuplicateRepresentative_iff _).not.mp
    ((LieTypeIndex.valid_iff _).1 hv).2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  have hcard :
      Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]
  have hodd : Odd (q.p ^ q.exponent) := (Nat.Prime.odd_of_ne_two q.prime_p hq).pow
  have h3 : q.p ^ q.exponent ≠ 3 := by
    intro h
    apply hdup
    simp [h]
  have h1 : 2 ≤ q.p ^ q.exponent := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  refine hS.false_of_not_isCharTwoType
    (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv))
    (not_isCharTwoType_PSp_two (by rw [hcard]; obtain ⟨k, hk⟩ := hodd; omega) (by rwa [hcard]))

theorem Standing.false_of_twistedA_three (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.p ≠ 2) (he1 : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) : False := by
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 3 q
  have he : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 3 q
  by_cases h3 : q.p = 3
  · set K := GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)
    have hK : Nat.card K = 9 := by
      rw [GaloisField.card _ _ (by rw [he, he1]; norm_num), hc, he, h3, he1]
      norm_num
    have hq3 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
        ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 3 := by
      rw [hc, he, h3, he1]
      rfl
    have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
    rw [hq3] at e'
    refine hS.false_of_card e' (N := 3265920) {3} (card_PSU_four_three hK) ?_ cube_free_3265920
    intro _ r hr _ _
    obtain rfl : r = 3 := by simpa using hr
    exact localRankThreeU43 _ hK
  · have h5 : 5 ≤ q.card := five_le_card_of_odd q hq fun h => h3 h.1
    have h := unitaryFieldData_galoisField
      (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩) _
      (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 3 q, hv⟩)
    refine hS.false_of_not_isCharTwoType
      ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)).trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := 2 + 2) (by omega)).symm)
      (not_isCharTwoType_unitaryPSU_block h (by rw [hc]; exact hq) ?_ (by norm_num))
    rw [hc, he]
    simpa only [PrimePower.card_def] using h5

theorem Standing.false_of_A_three (hS : Standing G) (q : PrimePower)
    (hv : (LieTypeIndex.A 3 q).Valid) (hq : q.p ≠ 2) (he1 : q.exponent = 1)
    (e : G ≃* (CFSGIndex.lie ⟨.A 3 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  by_cases h3 : q.p = 3
  · set F := GaloisField q.p q.exponent
    have := Fintype.ofFinite F
    have := Fintype.ofFinite nineBase
    have hF : Fintype.card F = 3 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card _ _ hf, h3, he1]
      norm_num
    have : CharP F 3 := h3 ▸ (inferInstance : CharP F q.p)
    let f : nineBase ≃+* F :=
      (ZMod.ringEquiv (n := 3) nineBase fintype_card_nineBase).symm.trans
        (ZMod.ringEquiv (n := 3) F hF)
    let ψ : ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase ≃*
        ProjectiveSpecialLinearGroup (Fin (3 + 1)) F :=
      pslCongr ((slRingEquiv f).trans (slReindexEquiv finProdFinEquiv))
    exact hS.false_of_not_isCharTwoType
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv))
      (fun h => not_isCharTwoType_PSL_four_three ((isCharTwoType_congr ψ).mpr h))
  · have h5 : 5 ≤ q.card := five_le_card_of_odd q hq fun h => h3 h.1
    refine hS.false_of_not_isCharTwoType
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv))
      (not_isCharTwoType_PSL_block (m := 2) ?_ (card_galoisField_odd _ _ hq hf) (by norm_num))
    rw [GaloisField.card _ _ hf]
    simp only [PrimePower.card_def] at h5
    omega

theorem Standing.false_of_item4 (hS : Standing G) (h : ThmThreeItem4 G) : False := by
  obtain ⟨q, hq, he1, h⟩ := h
  rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
  · exact hS.false_of_G2 q hv hq he1 e
  · exact hS.false_of_B_two q hv hq e
  · exact hS.false_of_twistedA_three q hv hq he1 e
  · exact hS.false_of_A_three q hv hq he1 e

end Certified

end CFSG.LocalAnalysis.RankThreeUC
