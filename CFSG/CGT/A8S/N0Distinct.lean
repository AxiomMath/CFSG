module

public import CFSG.CGT.A8S.N0Aff
public import CFSG.CGT.A8S.N0Words

public section

namespace CFSG.CGT.A8S.N0

@[expose] def affDistinct : Bool :=
  natEqB wordCodes.length 1344 &&
    bitsNodup 0 (wordCodes.map fun c => affCode (affEval (wordOfCode c)))

theorem affDistinct_eq_true : affDistinct = true := by decide +kernel

theorem length_wordCodes : wordCodes.length = 1344 := by
  have h := affDistinct_eq_true
  unfold affDistinct at h
  rw [Bool.and_eq_true] at h
  exact eq_of_natEqB h.1

theorem nodup_affCodes : (wordCodes.map fun c => affCode (affEval (wordOfCode c))).Nodup := by
  have h := affDistinct_eq_true
  unfold affDistinct at h
  rw [Bool.and_eq_true] at h
  exact (nodup_of_bitsNodup h.2).1

theorem n0Word_eq (k : Fin 1344) :
    n0Word k = wordOfCode (wordCodes[k.val]'(by rw [length_wordCodes]; exact k.isLt)) := by
  rw [n0Word, List.getD_eq_getElem]

theorem affEval_n0Word_injective :
    Function.Injective fun k : Fin 1344 => affEval (n0Word k) := by
  intro i j h
  have hl := length_wordCodes
  have hi : i.val < (wordCodes.map fun c => affCode (affEval (wordOfCode c))).length := by
    rw [List.length_map, hl]
    exact i.isLt
  have hj : j.val < (wordCodes.map fun c => affCode (affEval (wordOfCode c))).length := by
    rw [List.length_map, hl]
    exact j.isLt
  refine Fin.ext ((nodup_affCodes.getElem_inj_iff (hi := hi) (hj := hj)).1 ?_)
  rw [List.getElem_map, List.getElem_map]
  have h' : affCode (affEval (n0Word i)) = affCode (affEval (n0Word j)) :=
    congrArg affCode h
  rwa [n0Word_eq, n0Word_eq] at h'

end CFSG.CGT.A8S.N0
