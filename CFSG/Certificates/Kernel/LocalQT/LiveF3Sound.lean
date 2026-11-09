module

public import CFSG.Certificates.Kernel.LocalQT.RunF3Sound
public import Certificates.Data.Kernel.NC2L

public section

namespace CFSG.KC.OpsLayF3

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KC.OpsLayK CFSG.KS.F3L CFSG.F3.Native CFSG.SectionRank.Native

@[expose] noncomputable def liveL3 (c : Lay) (K : Nat) (C : CFSG.KC.NC2L.LiveChunk)
    (S S' : List Nat) : Bool :=
  allValid c S && allValid c S' &&
    runV (ctxOf c K) C.prog (gL c K (padR c S C.n)) fun R =>
      eqVL (C.out.map (getV (ctxOf c K) R)) (gL c K S')

theorem liveL_of_F3 {c : Lay} {K : Nat} (hg : Good c K) {C : CFSG.KC.NC2L.LiveChunk}
    {S S' : List Nat} (h : liveL3 c K C S S' = true) : CFSG.KC.NC2L.liveL c C S S' = true := by
  unfold liveL3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hS, hS'⟩, h⟩ := h
  have cS := canon_of_allValid hg hS
  have cS' := canon_of_allValid hg hS'
  have h0 := forall2_gL hg (canon_padR hg cS C.n)
  have e : CFSG.KC.NC2L.padR c S C.n = padR c S C.n := rfl
  unfold CFSG.KC.NC2L.liveL
  rw [e, runC_eq]
  rw [runV_eq] at h
  exact eqL_of_eqVL hg (forall2_map (rel_fold hg C.prog h0) hg _) cS' h

@[expose] noncomputable def getVK (x : Ctx) (R : List V) (i : Nat) : V :=
  List.rec (motive := fun _ => Nat → V) (fun _ => x.I)
    (fun a _ ih i => Nat.rec (motive := fun _ => V) a (fun i' _ => ih i') i) R i
@[expose] noncomputable def setVK (R : List V) (t : Nat) (a : V) : List V :=
  List.rec (motive := fun _ => Nat → List V) (fun _ => [])
    (fun b bs ih t => Nat.rec (motive := fun _ => List V) (a :: bs) (fun t' _ => b :: ih t') t) R t
@[expose] noncomputable def stepV3K (x : Ctx) (R : List V) (o : Op) : V :=
  Op.rec (motive := fun _ => V) (fun i j _ => mulV x (getVK x R i) (getVK x R j))
    (fun e i _ => powV x 17 (getVK x R i) e) o
@[expose] noncomputable def runVK (x : Ctx) (prog : List Op) : List V → (List V → Bool) → Bool :=
  List.rec (motive := fun _ => List V → (List V → Bool) → Bool) (fun R k => k R)
    (fun o _ ih R k => strictV (stepV3K x R o) fun v => ih (setVK R (Op.tgt o) v) k) prog
theorem getVK_eq (x : Ctx) : ∀ (R : List V) (i : Nat), getVK x R i = getV x R i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: R, i + 1 => by
    show getVK x R i = getV x (a :: R) (i + 1)
    rw [getVK_eq x R i]
    rfl
theorem setVK_eq : ∀ (R : List V) (t : Nat) (a : V), setVK R t a = R.set t a
  | [], t, _ => by cases t <;> rfl
  | _ :: _, 0, _ => rfl
  | b :: R, t + 1, a => by
    show b :: setVK R t a = (b :: R).set (t + 1) a
    rw [setVK_eq R t a]
    rfl
theorem stepV3K_eq (x : Ctx) (R : List V) (o : Op) : stepV3K x R o = stepV3 x R o := by
  cases o with
  | mul i j t =>
    show mulV x (getVK x R i) (getVK x R j) = stepV3 x R (.mul i j t)
    rw [getVK_eq, getVK_eq]
    rfl
  | pow e i t =>
    show powV x 17 (getVK x R i) e = stepV3 x R (.pow e i t)
    rw [getVK_eq]
    rfl
theorem runV_eqK (x : Ctx) : ∀ (prog : List Op) (R : List V) (k : List V → Bool),
    runVK x prog R k = runV x prog R k
  | [], _, _ => rfl
  | o :: P, R, k => by
    show strictV (stepV3K x R o) (fun v => runVK x P (setVK R (Op.tgt o) v) k) =
      strictV (stepV3 x R o) (fun v => runV x P (R.set (Op.tgt o) v) k)
    rw [stepV3K_eq]
    congr 1
    funext v
    rw [setVK_eq, runV_eqK x P]
@[expose] noncomputable def liveL3K (c : Lay) (K : Nat) (C : CFSG.KC.NC2L.LiveChunk)
    (S S' : List Nat) : Bool :=
  allValid c S && allValid c S' &&
    runVK (ctxOf c K) C.prog (gL c K (padR c S C.n)) fun R =>
      eqVL (C.out.map (getV (ctxOf c K) R)) (gL c K S')

theorem liveL3_eqK (c : Lay) (K : Nat) (C : CFSG.KC.NC2L.LiveChunk) (S S' : List Nat) :
    liveL3 c K C S S' = liveL3K c K C S S' := by
  unfold liveL3 liveL3K
  rw [runV_eqK]

theorem runVK_split {x : Ctx} {P : List Op} {R M : List V} {k : List V → Bool} {a b : Nat}
    (hab : a ≤ b) (h1 : runVK x ((P.drop a).take (b - a)) R (fun R' => eqVL R' M) = true)
    (h2 : runVK x (P.drop b) M k = true) : runVK x (P.drop a) R k = true := by
  rw [runV_eqK] at h1 h2 ⊢
  exact runV_split hab h1 h2

theorem liveL3K_intro {c : Lay} {K : Nat} {C : CFSG.KC.NC2L.LiveChunk} {S S' : List Nat}
    (hv : (allValid c S && allValid c S') = true)
    (h : runVK (ctxOf c K) (C.prog.drop 0) (gL c K (padR c S C.n))
      (fun R => eqVL (C.out.map (getVK (ctxOf c K) R)) (gL c K S')) = true) :
    liveL3K c K C S S' = true := by
  have e : (fun R : List V => eqVL (C.out.map (getVK (ctxOf c K) R)) (gL c K S')) =
      (fun R => eqVL (C.out.map (getV (ctxOf c K) R)) (gL c K S')) := by
    funext R
    congr 2
    funext i
    exact getVK_eq _ R i
  rw [e, List.drop_zero] at h
  unfold liveL3K
  rw [hv, Bool.true_and]
  exact h

theorem liveL_of_F3K {c : Lay} {K : Nat} (hg : Good c K) {C : CFSG.KC.NC2L.LiveChunk}
    {S S' : List Nat} (h : liveL3K c K C S S' = true) : CFSG.KC.NC2L.liveL c C S S' = true :=
  liveL_of_F3 hg (by rw [liveL3_eqK]; exact h)

end CFSG.KC.OpsLayF3

end
