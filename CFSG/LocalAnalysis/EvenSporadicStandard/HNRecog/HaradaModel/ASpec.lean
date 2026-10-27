module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.IotaP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Coe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AParts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.ACheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA

private theorem uWords_length : uWords.length = 6 := by decide

private theorem uElem_mem_wordSubgroupP {i : ℕ} (hi : i < 6) :
    uElem i ∈ wordSubgroupP uWords := by
  rw [mem_wordSubgroupP]
  show elemW (uWords.getD i []) ∈ wordSubgroup uWords
  exact elemW_mem_wordSubgroup (by
    rw [List.getD_eq_getElem (l := uWords) (d := []) (by rw [uWords_length]; exact hi)]
    exact List.getElem_mem _)

theorem iotaFun_mem (v : V6) : iotaFun v ∈ wordSubgroupP uWords := by
  have h0 : uElem 0 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 0) (by norm_num)
  have h1 : uElem 1 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 1) (by norm_num)
  have h2 : uElem 2 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 2) (by norm_num)
  have h3 : uElem 3 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 3) (by norm_num)
  have h4 : uElem 4 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 4) (by norm_num)
  have h5 : uElem 5 ∈ wordSubgroupP uWords :=
    uElem_mem_wordSubgroupP (i := 5) (by norm_num)
  change uElem 0 ^ (v 0).val * uElem 1 ^ (v 1).val * uElem 2 ^ (v 2).val *
    uElem 3 ^ (v 3).val * uElem 4 ^ (v 4).val * uElem 5 ^ (v 5).val ∈
      wordSubgroupP uWords
  let K := wordSubgroupP uWords
  exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
    (K.mul_mem (K.pow_mem h0 (v 0).val) (K.pow_mem h1 (v 1).val))
    (K.pow_mem h2 (v 2).val)) (K.pow_mem h3 (v 3).val)) (K.pow_mem h4 (v 4).val))
    (K.pow_mem h5 (v 5).val)

theorem codeOfVec_vecOfCode : ∀ k < 64, codeOfVec (vecOfCode k) = k := by decide

section Cert

variable
  (ι : Multiplicative V6 →* ↥P1408) (hι : ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v)

include hι

private theorem iotaFun_single (i : ℕ) (hi : i < 6) :
    iotaFun (Pi.single (⟨i, hi⟩ : Fin 6) 1) = uElem i := by
  interval_cases i <;>
    simp [iotaFun, Pi.single_apply, ZMod.val_one]

private theorem uElem_mem_range {i : ℕ} (hi : i < 6) : uElem i ∈ ι.range :=
  MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (Pi.single (⟨i, hi⟩ : Fin 6) 1), by
    rw [hι, iotaFun_single (ι := ι) (hι := hι) i hi]⟩

theorem range_iota : ι.range = wordSubgroupP uWords := by
  apply le_antisymm
  · intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨v, rfl⟩ := hy
    change ι (Multiplicative.ofAdd (Multiplicative.toAdd v)) ∈ wordSubgroupP uWords
    rw [hι]
    exact iotaFun_mem (Multiplicative.toAdd v)
  · have hle : wordSubgroup uWords ≤ ι.range.map P1408.subtype := by
      rw [wordSubgroup, Subgroup.closure_le]
      rintro y ⟨w, hw, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
      have hi6 : i < 6 := by simpa [uWords_length] using hi
      refine Subgroup.mem_map.2 ⟨uElem i, ?_, ?_⟩
      · exact uElem_mem_range (ι := ι) (hι := hι) hi6
      · show elemW (uWords.getD i []) = elemW (uWords[i])
        rw [List.getD_eq_getElem (l := uWords) (d := []) hi]
        rfl
    intro x hx
    have hx' : (x : Equiv.Perm (Fin 1408)) ∈ wordSubgroup uWords := hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hle hx')
    rw [show x = z from Subtype.ext hzx.symm]
    exact hz

theorem injective_iota : Function.Injective ι := by
  refine (injective_iff_map_eq_one ι).2 fun v hv => ?_
  have h1 : iotaFun (vecOfCode (codeOfVec (Multiplicative.toAdd v))) = 1 := by
    rw [vecOfCode_codeOfVec, ← hι]
    exact hv
  by_contra hne
  refine aFacts.iota_ne_one _ (codeOfVec_lt _) (fun h0 => hne ?_) h1
  have e : Multiplicative.toAdd v = 0 := codeOfVec_injective (by rw [h0, codeOfVec_zero])
  exact e

theorem iota_tv : ι (Multiplicative.ofAdd tv) = pA := by
  rw [hι]
  rw [show tv = Pi.single (⟨4, by norm_num⟩ : Fin 6) 1 from rfl,
    iotaFun_single (ι := ι) (hι := hι) 4 (by norm_num)]
  apply Subtype.ext
  show elemW (uWords.getD 4 []) = elemA
  have e : uWords.getD 4 [] = wordA := by decide
  rw [e]
  rfl

theorem iota_zv : ι (Multiplicative.ofAdd (Pi.single 0 1 : V6)) = pZ := by
  rw [hι]
  change iotaFun (Pi.single (⟨0, by norm_num⟩ : Fin 6) 1) = pZ
  rw [iotaFun_single (ι := ι) (hι := hι) 0 (by norm_num)]
  apply Subtype.ext
  show elemW (uWords.getD 0 []) = elemZ
  have e : uWords.getD 0 [] = wordZ := by decide
  rw [e]
  rfl

theorem coords_z_A : ∃ v : V6, ι (Multiplicative.ofAdd v) = pZ ∧ lam v = 0 ∧ qm v = 0 := by
  refine ⟨Pi.single (0 : Fin 6) 1, ?_, ?_, ?_⟩
  · exact iota_zv (ι := ι) (hι := hι)
  · decide +kernel
  · decide +kernel

theorem coords_b_A : ∃ v : V6, ι (Multiplicative.ofAdd v) = pB ∧ lam v = 1 ∧ qm v = 1 := by
  refine ⟨Pi.single (5 : Fin 6) 1, ?_, ?_, ?_⟩
  · rw [hι]
    change iotaFun (Pi.single (⟨5, by norm_num⟩ : Fin 6) 1) = pB
    rw [iotaFun_single (ι := ι) (hι := hι) 5 (by norm_num)]
    apply Subtype.ext
    show elemW (uWords.getD 5 []) = elemB
    have e : uWords.getD 5 [] = wordB := by decide
    rw [e]
    rfl
  · decide +kernel
  · decide +kernel

theorem coords_z₁_A : ∃ v : V6, ι (Multiplicative.ofAdd v) = pZ₁ ∧ lam v = 1 ∧ qm v = 0 := by
  refine ⟨vecOfCode 45, ?_, ?_, ?_⟩
  · rw [hι]
    exact aFacts.iota_z₁
  · rw [lam_vecOfCode]
    decide +kernel
  · rw [qm_vecOfCode]
    decide +kernel

theorem mem_E_iff_A {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) (v : V6) :
    ι (Multiplicative.ofAdd v) ∈ Ep ↔ lam v = 0 := by
  rw [hι, hEp]
  set k := codeOfVec v with hk
  have hklt : k < 64 := codeOfVec_lt v
  have hv : vecOfCode k = v := vecOfCode_codeOfVec v
  rw [← hv, aFacts.halves k hklt, lam_vecOfCode]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    have hdvd : 2 ∣ lamC k := (ZMod.natCast_eq_zero_iff (lamC k) 2).1 h
    have hlt : lamC k < 2 := by
      have := Nat.mod_lt (k >>> 5) (by norm_num : 0 < 2)
      simpa [lamC, bitOf] using this
    exact Nat.eq_zero_of_dvd_of_lt hdvd hlt

theorem centralizer_le_A (hP : Nat.card ↥P1408 = 177408000) :
    centralizer (ι.range : Set ↥P1408) ≤ ι.range := by
  intro x hx
  have hc : ∀ i < 6, x * uElem i = uElem i * x := fun i hi =>
    (Subgroup.mem_centralizer_iff.1 hx (uElem i) (uElem_mem_range (ι := ι) (hι := hι) hi)).symm
  obtain ⟨k, -, e⟩ := aFacts.cent hP x hc
  rw [← e, ← hι]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
