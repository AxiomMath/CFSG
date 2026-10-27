module

public import Certificates.Data.Kernel.Misc.TitsPi
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.TitsPi

open CFSG.KC.Enum CFSG.KS

theorem cmpL_spec (n w P : Nat) : ∀ (k : Nat) (l : List Nat), cmpL n w P k l = true →
    k + l.length = n ∧ ∀ j (hj : j < l.length), l[j] = pg w (mask w) P (k + j)
  | k, [], h => by
    simp only [cmpL, beq_iff_eq] at h
    simp [h]
  | k, a :: t, h => by
    simp only [cmpL, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := cmpL_spec n w P (k + 1) t h.2
    refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
    cases j with
    | zero => simpa using h.1
    | succ j =>
      rw [List.getElem_cons_succ, h2 j (by simpa using hj)]
      congr 1
      omega

theorem cmpL_sound {n w P : Nat} {a : Array Nat} (h : cmpL n w P 0 a.toList = true) :
    a = CFSG.KS.Raw.unpack n w P := by
  obtain ⟨h1, h2⟩ := cmpL_spec n w P 0 a.toList h
  apply Array.ext
  · simp only [CFSG.KS.Raw.unpack, Array.size_ofFn]
    simpa using h1
  · intro i hi _
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    have := h2 i (by simpa using hi)
    simpa using this

end CFSG.KC.TitsPi

end
