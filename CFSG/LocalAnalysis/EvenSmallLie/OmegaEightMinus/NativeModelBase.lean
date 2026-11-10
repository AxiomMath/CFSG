
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!
  chain_strong_spec extract_getElem! mem_normalizer_of_conj_mem)

theorem genArrs_size : genArrs.size = 11 := by simp [genArrs, gPairs]

theorem omegaS_size : omegaS.size = 18 := by
  rw [omegaS, size_pushWords]
  simp [genArrs_size, omegaWords]

theorem autS_size : autS.size = 19 := by
  rw [autS, size_pushWords, genArrs_size]
  simp [autWords]

theorem sylowGens_size : sylowGens.size = 6 := by simp [sylowGens, sylowIdx]

theorem sylowS_size : sylowS.size = 9 := by
  rw [sylowS, size_pushWords, sylowGens_size]
  simp [sylowWords]

def omegaQ : RawSchreierDatum 136 :=
  RawSchreierDatum.ofArrays 136 (by norm_num) omegaS 10 (by rw [omegaS_size]; norm_num) omegaBase
    (by decide) (wordsOf 10 omegaWords)

def autQ : RawSchreierDatum 136 :=
  RawSchreierDatum.ofArrays 136 (by norm_num) autS 11 (by rw [autS_size]; norm_num) autBase
    (by decide) (wordsOf 11 autWords)

def sylowQ : RawSchreierDatum 136 :=
  RawSchreierDatum.ofArrays 136 (by norm_num) sylowS 6 (by rw [sylowS_size]; norm_num) sylowBase
    (by decide) (wordsOf 6 sylowWords)

def omegaT : Subgroup (Equiv.Perm (Fin 136)) := omegaQ.originalSubgroup

def autT : Subgroup (Equiv.Perm (Fin 136)) := autQ.originalSubgroup

def sylowT : Subgroup (Equiv.Perm (Fin 136)) := sylowQ.originalSubgroup

def gen (i : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 genArrs[i]!

theorem omegaS_getElem! {i : ℕ} (hi : i < 10) : omegaS[i]! = genArrs[i]! := by
  rw [omegaS, pushWords_getElem! _ _ (by simp [genArrs_size]; omega),
    extract_getElem! hi (by rw [genArrs_size]; norm_num)]

theorem autS_getElem! {i : ℕ} (hi : i < 11) : autS[i]! = genArrs[i]! := by
  rw [autS, pushWords_getElem! _ _ (by rw [genArrs_size]; omega)]

theorem sylowGens_getElem! {i : ℕ} (hi : i < 6) : sylowGens[i]! = genArrs[sylowIdx.getD i 0]! := by
  rw [sylowGens, getElem!_pos _ i (by simpa [sylowIdx] using hi), Array.getElem_map]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < sylowIdx.length by
    simpa [sylowIdx] using hi)]

theorem sylowS_getElem! {i : ℕ} (hi : i < 6) : sylowS[i]! = genArrs[sylowIdx.getD i 0]! := by
  rw [sylowS, pushWords_getElem! _ _ (by rw [sylowGens_size]; omega), sylowGens_getElem! hi]

theorem omegaT_eq : omegaT = Subgroup.closure {g | ∃ i < 10, gen i = g} := by
  rw [omegaT, omegaQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, omegaS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, omegaS_getElem! hi]⟩

theorem autT_eq : autT = Subgroup.closure {g | ∃ i < 11, gen i = g} := by
  rw [autT, autQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, autS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, autS_getElem! hi]⟩

theorem sylowT_eq : sylowT = Subgroup.closure {g | ∃ i < 6, gen (sylowIdx.getD i 0) = g} := by
  rw [sylowT, sylowQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, sylowS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, sylowS_getElem! hi]⟩

theorem gen_mem_omegaT {i : ℕ} (hi : i < 10) : gen i ∈ omegaT := by
  rw [omegaT_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem gen_mem_autT {i : ℕ} (hi : i < 11) : gen i ∈ autT := by
  rw [autT_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem omegaT_le_autT : omegaT ≤ autT := by
  rw [omegaT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact gen_mem_autT (by omega)

theorem sylowT_le_autT : sylowT ≤ autT := by
  rw [sylowT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  apply gen_mem_autT
  interval_cases i <;> decide

theorem rep_conjArr {t u : Array ℕ} {g h : Equiv.Perm (Fin 136)} (ht : Rep 136 t g)
    (hti : Rep 136 (invCand 136 t) g⁻¹) (hu : Rep 136 u h) :
    Rep 136 (conjArr t u) (g * h * g⁻¹) :=
  rep_compA (rep_compA ht hu) hti

theorem rvPerm_lt {i : ℕ} (hi : i < 10) : rvPerm.getD i 0 < 10 := by
  interval_cases i <;> decide

def sgen (j : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 omegaS[j]!

end CFSG.EvenSmallLie.OmegaEightMinus
