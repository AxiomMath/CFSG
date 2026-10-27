module

public import CFSG.LieType.SeitzGeneration.OuterSmallData8
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

open CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def cq (x : Q8) : ℕ := x.re.val.val + 8 * x.im.val.val

theorem cq_inj {x y : Q8} (h : cq x = cq y) : x = y := by
  obtain ⟨⟨⟨a, ha⟩⟩, ⟨⟨b, hb⟩⟩⟩ := x
  obtain ⟨⟨⟨c, hc⟩⟩, ⟨⟨d, hd⟩⟩⟩ := y
  simp only [cq] at h
  obtain rfl : a = c := by omega
  obtain rfl : b = d := by omega
  rfl

@[expose] def cm (A : M3 Q8) : List ℕ :=
  [cq A.a00, cq A.a01, cq A.a02, cq A.a10, cq A.a11, cq A.a12, cq A.a20, cq A.a21, cq A.a22]

theorem cm_inj {A B : M3 Q8} (h : cm A = cm B) : A = B := by
  simp only [cm, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact M3.ext (cq_inj h1) (cq_inj h2) (cq_inj h3) (cq_inj h4) (cq_inj h5) (cq_inj h6)
    (cq_inj h7) (cq_inj h8) (cq_inj h9)

@[expose] def q4 (x : Q8) : Q8 := (x * x) * (x * x)

@[expose] def q8p (x : Q8) : Q8 := q4 x * q4 x

theorem q4_eq (x : Q8) : q4 x = x ^ 4 := by
  simp only [q4]
  ring

theorem q8p_eq (x : Q8) : q8p x = x ^ 8 := by
  simp only [q8p, q4]
  ring

@[expose] def mstar (A : M3 Q8) : M3 Q8 := (A.map q8p).transpose

@[expose] def msig (A : M3 Q8) : M3 Q8 := A.map q4

@[expose] def mu3 : List Q8 := [1, QExt.omega, QExt.omega * QExt.omega]

@[expose] def mpow (Y : M3 Q8) : ℕ → M3 Q8
  | 0 => 1
  | n + 1 => mpow Y n * Y

@[expose] def suOk (A : M3 Q8) : Bool :=
  decide (cq A.det = cq 1) && decide (cm (mstar A * A) = cm 1)

@[expose] def fixOk (Y : M3 Q8) (t : ℕ) (A : M3 Q8) : Bool :=
  mu3.any fun l => decide (cm (mpow Y t * msig A) = cm (M3.smul l (A * mpow Y t)))

@[expose] def comm (A B : M3 Q8) : M3 Q8 := A * B * mstar A * mstar B

structure LiftData where
  Y : M3 Q8
  pairs : List (ℕ × M3 Q8 × M3 Q8)
  ws : List (List ℕ × Q8)

@[expose] def LiftData.gens (D : LiftData) : List (M3 Q8) :=
  D.pairs.flatMap fun p => [comm p.2.1 p.2.2, comm p.2.2 p.2.1]

@[expose] def targets : List (M3 Q8) := outerLetters8 ++ [sM3]

@[expose] def inMu3 (l : Q8) : Bool := mu3.any fun m => decide (cq l = cq m)

@[expose] def LiftData.check (D : LiftData) : Bool :=
  decide (cm (mstar D.Y * D.Y) = cm 1) && decide (cm (msig D.Y) = cm D.Y) &&
    D.pairs.all (fun p => decide (p.1 < 3) && suOk p.2.1 && suOk p.2.2 && fixOk D.Y p.1 p.2.1 &&
      fixOk D.Y p.1 p.2.2) &&
    targets.all fun T => D.ws.any fun wl => inMu3 wl.2 &&
      decide (cm (evalW D.gens wl.1) = cm (M3.smul wl.2 T))

theorem suOk_spec {A : M3 Q8} (h : suOk A = true) : A.det = 1 ∧ mstar A * A = 1 := by
  simp only [suOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨cq_inj h.1, cm_inj h.2⟩

theorem fixOk_spec {Y A : M3 Q8} {t : ℕ} (h : fixOk Y t A = true) :
    ∃ l ∈ mu3, mpow Y t * msig A = M3.smul l (A * mpow Y t) := by
  simp only [fixOk, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨l, hl, he⟩ := h
  exact ⟨l, hl, cm_inj he⟩

theorem inMu3_spec {l : Q8} (h : inMu3 l = true) : l ∈ mu3 := by
  simp only [inMu3, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨m, hm, he⟩ := h
  rwa [cq_inj he]

theorem LiftData.check_spec {D : LiftData} (h : D.check = true) :
    mstar D.Y * D.Y = 1 ∧ msig D.Y = D.Y ∧
      (∀ p ∈ D.pairs, p.1 < 3 ∧ (p.2.1.det = 1 ∧ mstar p.2.1 * p.2.1 = 1) ∧
        (p.2.2.det = 1 ∧ mstar p.2.2 * p.2.2 = 1) ∧
        (∃ l ∈ mu3, mpow D.Y p.1 * msig p.2.1 = M3.smul l (p.2.1 * mpow D.Y p.1)) ∧
        (∃ l ∈ mu3, mpow D.Y p.1 * msig p.2.2 = M3.smul l (p.2.2 * mpow D.Y p.1))) ∧
      ∀ T ∈ targets, ∃ wl ∈ D.ws, wl.2 ∈ mu3 ∧ evalW D.gens wl.1 = M3.smul wl.2 T := by
  simp only [LiftData.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at h
  obtain ⟨⟨⟨hY, hYs⟩, hp⟩, hT⟩ := h
  refine ⟨cm_inj hY, cm_inj hYs, fun p hp' => ?_, fun T hT' => ?_⟩
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp p hp'
    exact ⟨h1, suOk_spec h2, suOk_spec h3, fixOk_spec h4, fixOk_spec h5⟩
  · obtain ⟨wl, hwl, h1, h2⟩ := hT T hT'
    exact ⟨wl, hwl, inMu3_spec h1, cm_inj h2⟩

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38
