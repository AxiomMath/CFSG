module

public import Certificates.Certificate27216
public import CFSG.Sporadic.SuzOddCore.OddCore

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

section Mem

theorem size_inner0 : (invInnerGenArrs 0).size = 22 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem xElt_mem (j : ℕ) (hj : j < 20) : xElt j ∈ invE 0 := by
  have h1 : invInnerGen 0 1 ∈ invE 0 :=
    invInnerGen_mem (by norm_num) (by rw [size_inner0]; norm_num)
  have h2 : invInnerGen 0 (j + 2) ∈ invE 0 :=
    invInnerGen_mem (by norm_num) (by rw [size_inner0]; omega)
  rw [xElt, commutatorElement_def]
  exact (invE 0).mul_mem ((invE 0).mul_mem ((invE 0).mul_mem h1 h2) ((invE 0).inv_mem h1))
    ((invE 0).inv_mem h2)

theorem letterElt_mem {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 5) : letterElt l ∈ invE 0 := by
  unfold letterElt
  by_cases hp : 0 < l
  · simp only [hp, ↓reduceIte]
    exact xElt_mem _ (by omega)
  · simp only [hp, ↓reduceIte]
    exact (invE 0).inv_mem (xElt_mem _ (by omega))

theorem wordElt_mem {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 5) : wordElt w ∈ invE 0 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact letterElt_mem (hw l hl)

end Mem

theorem oddWords_letters : ∀ p ∈ oddWords, ∀ l ∈ p.1, l ≠ 0 ∧ l.natAbs ≤ 5 := by decide

theorem mem_oddWords {k : ℕ} (hk : k < 9) : oddWords.getD k ([], 1) ∈ oddWords := by
  have : k < oddWords.length := by simpa [oddWords] using hk
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem this

theorem oddWords_exp_odd : ∀ p ∈ oddWords, p.2 % 2 = 1 := by decide

theorem odd_orderOf {k : ℕ} (hk : k < 9) :
    Odd (orderOf (oddElt k)) :=
  (Nat.odd_iff.2 (oddWords_exp_odd _ (mem_oddWords hk))).of_dvd_nat
    (orderOf_dvd_of_pow_eq_one (Certificates.certificate27216.1 k hk))

theorem oddElt_mem (k : ℕ) (hk : k < 9) : oddElt k ∈ invE 0 :=
  wordElt_mem fun l hl => oddWords_letters _ (mem_oddWords hk) l hl

theorem rElt_mem_RR {i : ℕ} (hi : i < 4) : rElt i ∈ RR :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem RR_le {S : Subgroup (Equiv.Perm (Fin 1782))} (h : ∀ i < 4, rElt i ∈ S) : RR ≤ S :=
  (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => h i i.2)

section R0

theorem card_RR : Nat.card RR = 64 := Certificates.certificate27216.2.1

theorem zElt_mem_RR : zElt ∈ RR := Certificates.certificate27216.2.2.1

theorem wElt_conj_RR {x : Equiv.Perm (Fin 1782)} (hx : x ∈ RR) : wElt * x * wElt⁻¹ ∈ RR := by
  have key : RR.map (MulAut.conj wElt).toMonoidHom ≤ RR := by
    refine Subgroup.map_le_iff_le_comap.2 (RR_le fun i hi => ?_)
    rw [Subgroup.mem_comap]
    simpa [MulAut.conj_apply] using Certificates.certificate27216.2.2.2.1 i hi
  exact key ⟨x, hx, by simp [MulAut.conj_apply]⟩

end R0

end CFSG.EvenSporadicStandard.SuzN0
