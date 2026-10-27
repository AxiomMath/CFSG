module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Certificate10019
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Inputs
public import Certificates.Certificate9308
public import Certificates.Certificate3139
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Data
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public meta import Mathlib

public section

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data

namespace J2Proof

theorem uChain_check :
    rawChainOK 315 (uStrong.extract 0 4) uStrong uBase uWords 4 = true ∧
      rawOrbitSizes 315 uStrong uBase = [32] := by
  exact Certificates.certificate9308.1

theorem nChain_check :
    rawChainOK 315 (nStrong.extract 0 3) nStrong nBase nWords 4 = true ∧
      rawOrbitSizes 315 nStrong nBase = [60, 2] := by
  exact Certificates.certificate9308.2.1

theorem cent2A_structure_check :
    (∀ k < 4, siftA 315 cent2ALevels cent2ABase 0 uStrong[k]! = true) ∧
    (∀ k < 2, ∀ i < 4,
      siftA 315 uLevels uBase 0 (conjA 315 cent2AStrong[k]! uStrong[i]!) = true) ∧
    all3 315 cent2ALevels selfCentTest = true := by
  exact Certificates.certificate9308.2.2.1

theorem cent2B_structure_check :
    (∀ k < 3, siftA 315 cent2BLevels cent2BBase 0 nStrong[k]! = true) ∧
    siftA 315 nLevels nBase 0 autStrong[0]! = false := by
  exact Certificates.certificate9308.2.2.2

@[expose] noncomputable def uChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) uStrong 4 (by simp [uStrong]) [0] (by decide)
    uWords

@[expose] noncomputable def nChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) nStrong 3 (by simp [nStrong]) [3, 0] (by decide)
    nWords

theorem uChain_ok : rawChainOK 315 (uStrong.extract 0 4) uStrong
    (([0] : List (Fin 315)).map Fin.val).toArray uWords 4 = true := uChain_check.1

theorem nChain_ok : rawChainOK 315 (nStrong.extract 0 3) nStrong
    (([3, 0] : List (Fin 315)).map Fin.val).toArray nWords 4 = true := nChain_check.1

theorem cent2A_ok :
    rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong
    (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray cent2AWords 4 = true := cent2A_check.1

theorem cent2B_ok :
    rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong
    (([0, 3] : List (Fin 315)).map Fin.val).toArray cent2BWords 4 = true := cent2B_check.1

theorem uStrong_size : uStrong.size = 4 := by simp [uStrong]

theorem nStrong_size : nStrong.size = 4 := by simp [nStrong]

theorem card_uChain : Nat.card uChain.originalSubgroup = 32 := by
  rw [uChain, ofArrays_card (by norm_num) uChain_ok]
  exact (congrArg List.prod uChain_check.2).trans (by norm_num)

theorem card_nChain : Nat.card nChain.originalSubgroup = 120 := by
  rw [nChain, ofArrays_card (by norm_num) nChain_ok]
  exact (congrArg List.prod nChain_check.2).trans (by norm_num)

theorem cent2A_structure :
    ∃ U : Subgroup (Equiv.Perm (Fin 315)), U ≤ cent2AChain.originalSubgroup ∧
      cent2AChain.originalSubgroup ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 315))) ∧
      IsPGroup 2 U ∧
      cent2AChain.originalSubgroup ⊓ Subgroup.centralizer (U : Set (Equiv.Perm (Fin 315))) ≤ U := by
  obtain ⟨hin, hnorm, hall⟩ := cent2A_structure_check
  have hUgen : ∀ i < 4, Rep 315 uStrong[i]! (permOfArr 315 uStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK uChain_ok (by rw [uStrong_size]; exact hi)
  have hKgen : ∀ i < 2, Rep 315 cent2AStrong[i]! (permOfArr 315 cent2AStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK cent2A_ok (by
      have : cent2AStrong.size = 5 := rfl
      omega)
  have hKinv : ∀ i < 2, Rep 315 (invCand 315 cent2AStrong[i]!) (permOfArr 315 cent2AStrong[i]!)⁻¹ :=
    fun i hi => rep_inv_of_chainOK cent2A_ok (by
      have : cent2AStrong.size = 5 := rfl
      omega)
  have hmemU : ∀ {t : Array ℕ} {g : Equiv.Perm (Fin 315)}, Rep 315 t g →
      (siftA 315 uLevels uBase 0 t = true ↔ g ∈ uChain.originalSubgroup) := fun {t g} h =>
    ofArrays_mem_iff (by norm_num) uChain_ok h
  have hmemK : ∀ {t : Array ℕ} {g : Equiv.Perm (Fin 315)}, Rep 315 t g →
      (siftA 315 cent2ALevels cent2ABase 0 t = true ↔ g ∈ cent2AChain.originalSubgroup) :=
    fun {t g} h => ofArrays_mem_iff (by norm_num) cent2A_ok h
  have hUc : uChain.originalSubgroup =
      Subgroup.closure {g | ∃ i < 4, permOfArr 315 uStrong[i]! = g} := ofArrays_originalSubgroup
  refine ⟨uChain.originalSubgroup, ?_, ?_, ?_, ?_⟩
  · rw [hUc, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    have := (hmemK (hUgen i hi)).1 (hin i hi)
    exact this
  · rw [cent2AChain, ofArrays_originalSubgroup, hUc]
    refine closure_le_normalizer_closure _ _ ?_
    rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
    have := (hmemU (rep_conjA (hKgen k hk) (hKinv k hk) (hUgen i hi))).1 (hnorm k hk i hi)
    rwa [hUc] at this
  · exact IsPGroup.of_card (n := 5) (by rw [card_uChain]; norm_num)
  · rintro g ⟨hgK, hgC⟩
    have hP : ∀ g ∈ cent2AChain.originalSubgroup,
        (∀ i < 4, g * permOfArr 315 uStrong[i]! = permOfArr 315 uStrong[i]! * g) →
          g ∈ uChain.originalSubgroup := by
      refine chain_forall_of_all3 (ofArrays_chainArrays cent2A_ok) (by norm_num) cent2A_ok
        (by show 3 ≤ 3; exact le_rfl) (fun i hi hi' => by
          have : i < 3 := hi'
          omega) ?_ hall
      intro t g ht hp hcomm
      simp only [selfCentTest, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false] at hp
      rcases hp with hp | hp
      · exfalso
        obtain ⟨i, hi, hne⟩ := hp
        have hi4 : i < 4 := List.mem_range.1 hi
        have := hcomm i hi4
        have hc : commA t uStrong[i]! = true := by
          unfold commA
          exact (eqA_iff (rep_compA ht (hUgen i hi4)) (rep_compA (hUgen i hi4) ht)).2 this
        rw [hc] at hne
        exact absurd hne (by simp)
      · exact (hmemU ht).1 hp
    refine hP g hgK fun i hi => ?_
    have := Subgroup.mem_centralizer_iff.1 hgC (permOfArr 315 uStrong[i]!) (by
      rw [uChain, ofArrays_originalSubgroup]
      exact Subgroup.subset_closure ⟨i, hi, rfl⟩)
    exact this.symm

theorem cent2B_structure :
    ∃ N : Subgroup (Equiv.Perm (Fin 315)), N ≤ cent2BChain.originalSubgroup ∧
      Nat.card cent2BChain.originalSubgroup = 2 * Nat.card N ∧ permA ∉ N := by
  obtain ⟨hin, hna⟩ := cent2B_structure_check
  have hNgen : ∀ i < 3, Rep 315 nStrong[i]! (permOfArr 315 nStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK nChain_ok (by rw [nStrong_size]; omega)
  refine ⟨nChain.originalSubgroup, ?_, ?_, ?_⟩
  · rw [nChain, ofArrays_originalSubgroup, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    exact (ofArrays_mem_iff (by norm_num) cent2B_ok (hNgen i hi)).1 (hin i hi)
  · rw [cent2B_facts.2.1, card_nChain]
  · intro hmem
    have h : siftA 315 nLevels nBase 0 autStrong[0]! = true :=
      (ofArrays_mem_iff (by norm_num) nChain_ok rep_permA).2 hmem
    rw [hna] at h
    exact Bool.noConfusion h

theorem noNonsolvableClassical_P :
    NoNonsolvableClassical P := by
  obtain ⟨hcov, -, he1, -, he2⟩ := inner_classes
  refine noNonsolvableClassical_of_reps P [permA, permTwoA] ?_ hcov ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact permA_mem
    · exact permTwoA_mem
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold CentralizerGood
      rw [he1]
      exact Or.inr cent2B_structure
    · unfold CentralizerGood
      rw [he2]
      exact Or.inl cent2A_structure

end J2Proof

theorem noNonsolvableClassical_J2 :
    NoNonsolvableClassical CFSG.Blueprint.NativeSporadic.J2 :=
  NoNonsolvableClassical.of_mulEquiv nativeEquivP J2Proof.noNonsolvableClassical_P

end CFSG.ClassicalInvolution
