module

public import Certificates.Data.Kernel.Misc.CentPt
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Quasithin.EmptyFaithfulMultiple.HeAutCentralizerData
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Misc.CentPt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Quasithin.EmptyFaithfulMultiple

theorem unpack_get! (n w P x : Nat) : (unpack n w P)[x]! = atU n w P x := by
  by_cases hx : x < n
  · have hb : Nat.blt x n = true := by simpa using hx
    rw [getElem!_pos _ x (by simpa [unpack] using hx)]
    simp [unpack, atU, hb]
  · have hb : Nat.blt x n = false := by
      cases hc : Nat.blt x n
      · rfl
      · rw [Nat.blt_eq] at hc
        exact absurd hc hx
    rw [getElem!_neg _ x (by simpa [unpack] using hx)]
    simp [atU, hb]

theorem compA_get! {n : Nat} {t u : Array Nat} {p : Nat} (hp : p < n) :
    (compA n t u)[p]! = t[u[p]!]! := by
  rw [getElem!_pos _ p (by simpa [compA] using hp)]
  simp [compA]

theorem sylCentCheck_of {n w N z : Nat} {Al : Array (Array Nat)} {E : Nat → Nat}
    {js ps : List Nat} (hAl : ∀ k < N, Al[k]! = unpack n w (E k)) (hjs : ∀ j ∈ js, j < N)
    (hps : ∀ p ∈ ps, p < n) (h : centPtK n w N E js ps z = true) :
    sylCentCheck n N Al js z = true := by
  unfold sylCentCheck
  rw [allLt_iff]
  intro i hi
  have hc := allN_spec h i hi
  by_cases hcomm : sylCommAll n Al js i = true
  · have hall : (js.all fun j => ps.all fun p => commAt n w (E i) (E j) p) = true := by
      rw [List.all_eq_true]
      intro j hj
      rw [List.all_eq_true]
      intro p hp
      have e := allLt_iff.1 ((List.all_eq_true.1 hcomm) j hj) p (hps p hp)
      rw [beq_iff_eq, compA_get! (hps p hp), compA_get! (hps p hp), hAl i hi, hAl j (hjs j hj),
        unpack_get!, unpack_get!, unpack_get!, unpack_get!] at e
      unfold commAt
      rw [e]
      exact Nat.beq_refl _
    rw [hall] at hc
    have h0 : i = 0 ∨ i = z := by simpa using hc
    rw [hcomm]
    rcases h0 with rfl | rfl <;> simp
  · simp [hcomm]

end CFSG.KC.Misc.CentPt

end
