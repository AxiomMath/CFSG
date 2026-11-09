module

public import Certificates.Data.Kernel.Spor.MulH
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def hsWalkK (n w m cnt : Nat) (T HS HSI : Nat → Nat) :
    Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih i h => strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        strictB (hkeyK n w m (T (r32 HS (Nat.succ i)))) (fun h' =>
          bAnd(Nat.blt h h', ih (Nat.succ i) h')), true)))))

@[expose] noncomputable def hsSlK (n w m cnt : Nat) (T HS HSI : Nat → Nat) (lo len : Nat) : Bool :=
  strictB (hkeyK n w m (T (r32 HS lo))) (fun h => hsWalkK n w m cnt T HS HSI len lo h)

theorem hsW_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hsW_and (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem hsW_if (c t : Bool) : bIf(c, t, true) = true ↔ (c = true → t = true) := by
  cases c <;> simp

theorem hsWalkK_succ {n w m cnt : Nat} {T HS HSI : Nat → Nat} (r i h : Nat) :
    hsWalkK n w m cnt T HS HSI (Nat.succ r) i h = strictB (r32 HS i) (fun s =>
      bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 HSI s) i, bIf(Nat.blt (Nat.succ i) cnt,
        strictB (hkeyK n w m (T (r32 HS (Nat.succ i)))) (fun h' =>
          bAnd(Nat.blt h h', hsWalkK n w m cnt T HS HSI r (Nat.succ i) h')), true)))) :=
  rfl

theorem hsWalkK_spec {n w m cnt : Nat} {T HS HSI : Nat → Nat} : ∀ rem i,
    hsWalkK n w m cnt T HS HSI rem i (hkeyK n w m (T (r32 HS i))) = true →
      ∀ d < rem, i + d < cnt → hsortPtK n w m cnt T HS HSI (i + d) = true := by
  intro rem
  induction rem with
  | zero => intro i _ d hd; omega
  | succ r ih =>
    intro i hw d hd hc
    simp only [hsWalkK_succ, hsW_strictB, hsW_and, hsW_if] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    rcases d with _ | d
    · unfold hsortPtK
      simp only [Nat.add_zero, hsW_strictB, hsW_and, hsW_if]
      exact ⟨h1, h2, fun hs => (h3 hs).1⟩
    · have hs : Nat.blt (Nat.succ i) cnt = true := Nat.blt_eq.mpr (by omega)
      have e : i + (d + 1) = Nat.succ i + d := by omega
      rw [e]
      exact ih (Nat.succ i) (h3 hs).2 d (by omega) (by omega)

theorem hsSlK_spec {n w m cnt : Nat} {T HS HSI : Nat → Nat} {lo len : Nat}
    (h : hsSlK n w m cnt T HS HSI lo len = true) :
    slK cnt (hsortPtK n w m cnt T HS HSI) lo len = true := by
  unfold hsSlK at h
  rw [hsW_strictB] at h
  unfold slK
  refine CFSG.KC.BfsPin.allN_intro fun d hd => ?_
  rw [hsW_strictB]
  rcases Nat.lt_or_ge (Nat.add lo d) cnt with hc | hc
  · have hb : Nat.blt (Nat.add lo d) cnt = true := Nat.blt_eq.mpr hc
    rw [hb]
    exact hsWalkK_spec len lo h d hd hc
  · have hb : Nat.blt (Nat.add lo d) cnt = false := by
      cases e : Nat.blt (Nat.add lo d) cnt
      · rfl
      · exact absurd (Nat.blt_eq.mp e) (by omega)
    rw [hb]

end CFSG.KS.MulH

end
