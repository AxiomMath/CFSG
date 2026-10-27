module

public import Certificates.Data.Kernel.LocalComp.ElemParts
public import CFSG.Certificates.Kernel.LocalQT.Steps
import all CFSG.Certificates.Kernel.LocalQT.Steps
import CFSG.Certificates.Kernel.LocalCompOps3Snd.Steps

public section

namespace CFSG.KC.LocalComp.ElemParts

open CFSG.KC.LQT

section Aux

open CFSG.KC.Ord

private theorem andB_of {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

private theorem andB_left {a b : Bool} (h : andB a b = true) : a = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem andB_right {a b : Bool} (h : andB a b = true) : b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem allLt_of {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) :
    allLt m f = true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e : allLt (m + 1) f = andB (f m) (allLt m f) := rfl
    rw [e, h m (Nat.lt_succ_self m), ih fun i hi => h i (by omega)]
    rfl

private theorem allLt_to {m : Nat} {f : Nat → Bool} (h : allLt m f = true) :
    ∀ i < m, f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    have e : allLt (m + 1) f = andB (f m) (allLt m f) := rfl
    rw [e] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih (andB_right h) i hi
    · exact andB_left h

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem stepIs_spec {P : Nat → Nat} {N t a b : Nat} (h : stepIs P N t a b = true) :
    3 ≤ t ∧ t < N ∧ P t = a + 1048576 * b := by
  unfold stepIs at h
  have h1 := andB_left h
  have h2 := andB_left (andB_right h)
  have h3 := andB_right (andB_right h)
  refine ⟨Nat.ble_eq.mp h1, Nat.blt_eq.mp h2, ?_⟩
  have := Nat.eq_of_beq_eq_true h3
  rw [this]
  change a + (b <<< 20) = a + 1048576 * b
  rw [Nat.shiftLeft_eq]
  omega

private theorem stepIs_val {c : Lay} {V P : Nat → Nat} {N : Nat} (hN : N ≤ 1048576)
    (hs : StepsTo (stepOK c V P) N) {t a b : Nat} (h : stepIs P N t a b = true) (ha : a < N) :
    V t = c.mul (V a) (V b) := by
  obtain ⟨h3, htN, hP⟩ := stepIs_spec h
  exact (CFSG.KC.LocalComp.Ops3Snd.stepOK_of_pair (hs t h3 htN) hP (by omega)).2.2

end Aux

theorem elemOK_of_parts {c : Lay} {V P O W SQ CU : Nat → Nat} {PP : Nat → Nat → Nat}
    {N r NS CH : Nat} (hN : N ≤ 1048576) (hs : StepsTo (stepOK c V P) N)
    (hc : ∀ i < r, cubeK c V P N (O i) (SQ i) (CU i) = true)
    (hp : ∀ i < r, ∀ j < i, pairK V P N (O i) (O j) (PP i j) (PP j i) = true)
    (hk : ∀ s < NS, kerK c V O W r (CH * s) CH = true) (hNS : 3 ^ r - 1 ≤ NS * CH) :
    elemOK c V N O W r = true := by
  have hO : ∀ i < r, O i < N := fun i hi => Nat.blt_eq.mp (andB_left (hc i hi))
  unfold elemOK
  refine andB_of (allLt_of fun i hi => ?_) (andB_of (allLt_of fun i hi => ?_)
    (andB_of (allLt_of fun i hi => allLt_of fun j hj => ?_) (allLt_of fun n hn => ?_)))
  · exact andB_left (hc i hi)
  · have hci := hc i hi
    have h1 := andB_left (andB_right hci)
    have h2 := andB_left (andB_right (andB_right hci))
    have h3 := andB_right (andB_right (andB_right hci))
    have e1 := stepIs_val hN hs h1 (hO i hi)
    have hsq : SQ i < N := (stepIs_spec h1).2.1
    have e2 := stepIs_val hN hs h2 hsq
    have e3 := Nat.eq_of_beq_eq_true h3
    rw [← e1, ← e2, e3]
    exact Nat.beq_refl _
  · have hpij := hp i hi j hj
    have h1 := andB_left hpij
    have h2 := andB_left (andB_right hpij)
    have h3 := andB_right (andB_right hpij)
    have e1 := stepIs_val hN hs h1 (hO i hi)
    have e2 := stepIs_val hN hs h2 (hO j (by omega))
    have e3 := Nat.eq_of_beq_eq_true h3
    rw [← e1, ← e2, e3]
    exact Nat.beq_refl _
  · have hn1 : n < 3 ^ r - 1 := hn
    have hn' : n < NS * CH := Nat.lt_of_lt_of_le hn1 hNS
    have hCH : 0 < CH := by
      rcases Nat.eq_zero_or_pos CH with h | h
      · rw [h, Nat.mul_zero] at hn'
        omega
      · exact h
    have hs' : n / CH < NS := (Nat.div_lt_iff_lt_mul hCH).2 hn'
    have hkk := allLt_to (hk (n / CH) hs') (n % CH) (Nat.mod_lt _ hCH)
    have e : Nat.add (CH * (n / CH)) (n % CH) = n := Nat.div_add_mod n CH
    have hb : Nat.blt n (Nat.sub (Nat.pow 3 r) 1) = true := Nat.blt_eq.mpr hn1
    simp only [strictB_eq', e, hb] at hkk
    simp only [strictB_eq']
    exact hkk

end CFSG.KC.LocalComp.ElemParts

end
