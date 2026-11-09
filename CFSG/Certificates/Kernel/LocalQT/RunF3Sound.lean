module

public import Certificates.Data.Kernel.OpsLayF3
public import CFSG.Certificates.Kernel.LocalQT.StepsF3Sound
public import CFSG.Certificates.Kernel.Spor.ConjIndexSound
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KC.OpsLayF3

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KC.OpsLayK CFSG.KS.F3L CFSG.F3.Native CFSG.SectionRank.Native
open CFSG.KS.Ord (Canon validM_canon)
open CFSG.KC.LQT.F3S (toMat_gath gath_wf canon_inj)
open CFSG.KS.SporSch.LyM (cfacts andB_true')
open CFSG.KC.LocalComp.Ops3Snd (mat3 mat3_mul mat3_one)

structure Good (c : Lay) (K : Nat) : Prop where
  ok : c.ok = true
  p3 : c.p = 3
  dK : c.d * c.d ≤ 2 ^ K
  d0 : 0 < c.d

theorem strictV_eq {α : Type} (v : V) (k : V → α) : strictV v k = k v := by
  cases v
  simp only [strictV, strictT_eq]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.LQT.strictB y k = k y := by
  cases y <;> rfl

section

variable {c : Lay} {K : Nat}

theorem Good.w2 (hg : Good c K) : 2 ≤ c.w := by
  obtain ⟨-, -, -, hpw⟩ := cfacts hg.ok
  have hpw' : 3 ≤ 2 ^ c.w := by rw [← hg.p3]; exact hpw
  rcases Nat.lt_or_ge c.w 2 with h2 | h2
  · interval_cases hcw : c.w <;> simp at hpw'
  · exact h2

theorem Good.hS (hg : Good c K) : c.S = c.d * c.w := (cfacts hg.ok).2.1

def Rel (c : Lay) (X : Nat) (v : V) : Prop :=
  Canon 3 c.d c.w X ∧ canonM c.d (unlane c.d v) = true ∧ toMat c.d (unlane c.d v) = mat3 c X

theorem canon_of_valid (hg : Good c K) {X : Nat}
    (h : validM c.p (Nat.mul c.d c.S) c.L c.H X = true) : Canon 3 c.d c.w X := by
  have := validM_canon hg.ok h
  rwa [hg.p3] at this

theorem toMat_gath' (hg : Good c K) {X : Nat} (hX : Canon 3 c.d c.w X) :
    toMat c.d (unlane c.d (gath3 c.w K X)) = mat3 c X := by
  rw [toMat_gath hg.w2 hg.dK hX]
  unfold mat3
  rw [hg.hS]

theorem rel_gath (hg : Good c K) {X : Nat} (hX : Canon 3 c.d c.w X) :
    Rel c X (gath3 c.w K X) :=
  ⟨hX, canonM_unlane c.d (gath_wf hg.w2 hX), toMat_gath' hg hX⟩

theorem canon_one (hg : Good c K) : Canon 3 c.d c.w c.ONE := by
  have := (mat3_one c hg.ok hg.p3).1
  rwa [hg.p3] at this

theorem rel_one (hg : Good c K) : Rel c c.ONE (ctxOf c K).I := rel_gath hg (canon_one hg)

theorem rel_mul (hg : Good c K) {X Y : Nat} {v u : V} (hX : Rel c X v) (hY : Rel c Y u) :
    Rel c (c.mul X Y) (mulV (ctxOf c K) v u) := by
  have hX1 : Canon c.p c.d c.w X := by rw [hg.p3]; exact hX.1
  have hY1 : Canon c.p c.d c.w Y := by rw [hg.p3]; exact hY.1
  obtain ⟨hm1, hm2⟩ := mat3_mul c hg.ok hg.p3 hX1 hY1
  have e : unlane c.d (mulV (ctxOf c K) v u) = mul c.d (unlane c.d v) (unlane c.d u) :=
    (mul_unlane hg.d0 v u).symm
  refine ⟨by rw [hg.p3] at hm1; exact hm1, ?_, ?_⟩
  · rw [e]
    exact canonM_mul (unlane_size _ _) (RowsWF.of_canonM hX.2.1) hY.2.1
  · rw [e, toMat_mul (unlane_size _ _) (RowsWF.of_canonM hX.2.1) (RowsWF.of_canonM hY.2.1),
      hX.2.2, hY.2.2, hm2]

theorem rel_pow (hg : Good c K) :
    ∀ (f : Nat) (X : Nat) (v : V) (e : Nat), Rel c X v →
      Rel c (powN c f X e) (powV (ctxOf c K) f v e) := by
  intro f
  induction f with
  | zero => intro X v e _; exact rel_one hg
  | succ f ih =>
    intro X v e hX
    have h2 := ih (c.mul X X) (mulV (ctxOf c K) v v) (Nat.div e 2) (rel_mul hg hX hX)
    have h3 := rel_mul hg hX h2
    have key : ∀ b1 b2 b3 : Bool, Rel c
        (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
          (CFSG.KC.Loop.strictN (c.mul X X) fun X2 =>
            CFSG.KC.Loop.strictN (powN c f X2 (Nat.div e 2)) fun Y =>
              Bool.rec (motive := fun _ => Nat) Y (c.mul X Y) b3) X b2) c.ONE b1)
        (Bool.rec (motive := fun _ => V) (Bool.rec (motive := fun _ => V)
          (strictV (mulV (ctxOf c K) v v) fun X2 =>
            strictV (powV (ctxOf c K) f X2 (Nat.div e 2)) fun Y =>
              Bool.rec (motive := fun _ => V) Y (mulV (ctxOf c K) v Y) b3) v b2)
          (ctxOf c K).I b1) := by
      intro b1 b2 b3
      simp only [strictN_eq', strictV_eq]
      cases b1 <;> cases b2 <;> cases b3
      all_goals first | exact h2 | exact h3 | exact hX | exact rel_one hg
    exact key _ _ _

theorem rel_getD (hg : Good c K) {R : List Nat} {R3 : List V} (h : List.Forall₂ (Rel c) R R3)
    (i : Nat) : Rel c (getR c R i) (getV (ctxOf c K) R3 i) := by
  induction h generalizing i with
  | nil =>
    have e1 : getR c [] i = c.ONE := by simp [getR]
    have e2 : getV (ctxOf c K) [] i = (ctxOf c K).I := by simp [getV]
    rw [e1, e2]
    exact rel_one hg
  | @cons a b l1 l2 hxy _ ih =>
    cases i with
    | zero =>
      have e1 : getR c (a :: l1) 0 = a := by simp [getR]
      have e2 : getV (ctxOf c K) (b :: l2) 0 = b := by simp [getV]
      rw [e1, e2]
      exact hxy
    | succ i =>
      have e1 : getR c (a :: l1) (i + 1) = getR c l1 i := by simp [getR]
      have e2 : getV (ctxOf c K) (b :: l2) (i + 1) = getV (ctxOf c K) l2 i := by simp [getV]
      rw [e1, e2]
      exact ih i

theorem forall2_set {R : List Nat} {R3 : List V} (h : List.Forall₂ (Rel c) R R3) (t : Nat)
    {X : Nat} {v : V} (hX : Rel c X v) : List.Forall₂ (Rel c) (R.set t X) (R3.set t v) := by
  induction h generalizing t with
  | nil =>
    simp only [List.set_nil]
    exact List.Forall₂.nil
  | cons hxy hr ih =>
    cases t with
    | zero =>
      simp only [List.set_cons_zero]
      exact List.Forall₂.cons hX hr
    | succ t =>
      simp only [List.set_cons_succ]
      exact List.Forall₂.cons hxy (ih t)

theorem rel_step (hg : Good c K) {R : List Nat} {R3 : List V} (h : List.Forall₂ (Rel c) R R3)
    (o : Op) : Rel c (stepV c R o) (stepV3 (ctxOf c K) R3 o) := by
  cases o with
  | mul i j k => exact rel_mul hg (rel_getD hg h i) (rel_getD hg h j)
  | pow e i k => exact rel_pow hg 17 _ _ e (rel_getD hg h i)

theorem runC_eq (prog : List Op) (R : List Nat) (k : List Nat → Bool) :
    runC c prog R k = k (prog.foldl (fun R o => R.set (Op.tgt o) (stepV c R o)) R) := by
  induction prog generalizing R with
  | nil => rfl
  | cons o P ih =>
    show CFSG.KC.LQT.strictB (stepV c R o) (fun v => runC c P (R.set (Op.tgt o) v) k) = _
    rw [strictB_eq', ih]
    rfl

theorem runV_eq (x : Ctx) (prog : List Op) (R : List V) (k : List V → Bool) :
    runV x prog R k = k (prog.foldl (fun R o => R.set (Op.tgt o) (stepV3 x R o)) R) := by
  induction prog generalizing R with
  | nil => rfl
  | cons o P ih =>
    show strictV (stepV3 x R o) (fun v => runV x P (R.set (Op.tgt o) v) k) = _
    rw [strictV_eq, ih]
    rfl

theorem rel_fold (hg : Good c K) (prog : List Op) {R : List Nat} {R3 : List V}
    (h : List.Forall₂ (Rel c) R R3) :
    List.Forall₂ (Rel c) (prog.foldl (fun R o => R.set (Op.tgt o) (stepV c R o)) R)
      (prog.foldl (fun R o => R.set (Op.tgt o) (stepV3 (ctxOf c K) R o)) R3) := by
  induction prog generalizing R R3 with
  | nil => exact h
  | cons o P ih => exact ih (forall2_set h _ (rel_step hg h o))

theorem forall2_gL (hg : Good c K) {S : List Nat} (h : ∀ X ∈ S, Canon 3 c.d c.w X) :
    List.Forall₂ (Rel c) S (gL c K S) := by
  induction S with
  | nil => exact List.Forall₂.nil
  | cons X S ih =>
    exact List.Forall₂.cons (rel_gath hg (h X (List.mem_cons_self ..)))
      (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY))

theorem canon_of_allValid (hg : Good c K) {S : List Nat} (h : allValid c S = true) :
    ∀ X ∈ S, Canon 3 c.d c.w X := by
  intro X hX
  unfold allValid at h
  exact canon_of_valid hg (List.all_eq_true.1 h X hX)

theorem eqV_eq {a b : V} (h : eqV a b = true) : a = b := by
  unfold eqV at h
  obtain ⟨h1, h2⟩ := andB_true' h
  exact V.ext' (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

theorem eq_of_rel (hg : Good c K) {X Y : Nat} (hX : Rel c X (gath3 c.w K Y))
    (hY : Canon 3 c.d c.w Y) : X = Y := by
  have e : mat3 c X = mat3 c Y := by rw [← hX.2.2, toMat_gath' hg hY]
  unfold mat3 at e
  rw [hg.hS] at e
  exact canon_inj hX.1 hY e

theorem eqL_of_eqVL (hg : Good c K) :
    ∀ {L : List Nat} {L3 : List V} {S : List Nat}, List.Forall₂ (Rel c) L L3 →
      (∀ X ∈ S, Canon 3 c.d c.w X) → eqVL L3 (gL c K S) = true → eqL L S = true := by
  intro L L3 S h
  induction h generalizing S with
  | nil =>
    intro _ hS
    cases S with
    | nil => rfl
    | cons _ _ => simp [gL, eqVL] at hS
  | @cons a b l1 l2 hxy _ ih =>
    intro hc hS
    cases S with
    | nil => simp [gL, eqVL] at hS
    | cons s S =>
      simp only [gL, List.map_cons, eqVL, Bool.and_eq_true] at hS
      have e := eqV_eq hS.1
      rw [e] at hxy
      have hs := eq_of_rel hg hxy (hc s (List.mem_cons_self ..))
      simp only [eqL, Bool.and_eq_true]
      refine ⟨by rw [hs]; exact Nat.beq_refl s, ?_⟩
      exact ih (fun Y hY => hc Y (List.mem_cons_of_mem _ hY)) hS.2

theorem forall2_map {L : List Nat} {L3 : List V} (h : List.Forall₂ (Rel c) L L3)
    (hg : Good c K) (out : List Nat) :
    List.Forall₂ (Rel c) (out.map (getR c L)) (out.map (getV (ctxOf c K) L3)) := by
  induction out with
  | nil => exact List.Forall₂.nil
  | cons o out ih => exact List.Forall₂.cons (rel_getD hg h o) ih

theorem canon_padR (hg : Good c K) {S : List Nat} (h : ∀ X ∈ S, Canon 3 c.d c.w X) (n : Nat) :
    ∀ X ∈ padR c S n, Canon 3 c.d c.w X := by
  intro X hX
  unfold padR at hX
  rcases List.mem_append.1 hX with hX | hX
  · exact h X hX
  · rw [List.eq_of_mem_replicate hX]
    exact canon_one hg

theorem chunkV_of_F3 (hg : Good c K) {ch : RChunk} {S S' : List Nat}
    (h : chunkV3 c K ch S S' = true) : chunkV c ch S S' = true := by
  unfold chunkV3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hS, hS'⟩, h⟩ := h
  have cS := canon_of_allValid hg hS
  have cS' := canon_of_allValid hg hS'
  have h0 := forall2_gL hg (canon_padR hg cS ch.1)
  unfold chunkV
  rw [runV_eq] at h
  rw [runC_eq]
  exact eqL_of_eqVL hg (forall2_map (rel_fold hg (ch.2.1.map opOf) h0) hg _) cS' h

theorem chunkL_of_F3 (hg : Good c K) {prog : List Op} {k i : Nat} {R S : List Nat}
    (h : chunkL3 c K prog k i R S = true) : chunkL c prog k i R S = true := by
  unfold chunkL3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hR, hS⟩, h⟩ := h
  have h0 := forall2_gL hg (canon_of_allValid hg hR)
  unfold chunkL
  rw [runV_eq] at h
  rw [runC_eq]
  exact eqL_of_eqVL hg (rel_fold hg ((prog.drop (i * k)).take k) h0) (canon_of_allValid hg hS) h

theorem eqVL_eq : ∀ (L M : List V), eqVL L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqVL] at h
  | _ :: _, [], h => by simp [eqVL] at h
  | a :: L, b :: M, h => by
    simp only [eqVL, Bool.and_eq_true] at h
    rw [eqV_eq h.1, eqVL_eq _ _ h.2]

theorem runV_append (x : Ctx) (P Q : List Op) (R : List V) (k : List V → Bool) :
    runV x (P ++ Q) R k = runV x P R (fun R' => runV x Q R' k) := by
  simp only [runV_eq, List.foldl_append]

theorem runV_split {x : Ctx} {P : List Op} {R M : List V} {k : List V → Bool} {a b : Nat}
    (hab : a ≤ b) (h1 : runV x ((P.drop a).take (b - a)) R (fun R' => eqVL R' M) = true)
    (h2 : runV x (P.drop b) M k = true) : runV x (P.drop a) R k = true := by
  have e2 : (P.drop a).drop (b - a) = P.drop b := by
    rw [List.drop_drop]
    congr 1
    omega
  have e : P.drop a = (P.drop a).take (b - a) ++ P.drop b := by
    rw [← e2]
    exact (List.take_append_drop _ _).symm
  rw [e, runV_append, runV_eq]
  rw [runV_eq] at h1
  have hM := eqVL_eq _ _ h1
  rw [hM]
  exact h2

theorem chunkV3_intro {c : Lay} {K : Nat} {ch : RChunk} {S S' : List Nat}
    (hv : (allValid c S && allValid c S') = true)
    (h : runV (ctxOf c K) ((ch.2.1.map opOf).drop 0) (gL c K (padR c S ch.1))
      (fun R => eqVL (ch.2.2.map (getV (ctxOf c K) R)) (gL c K S')) = true) :
    chunkV3 c K ch S S' = true := by
  unfold chunkV3
  rw [hv, Bool.true_and]
  rw [List.drop_zero] at h
  exact h

theorem chunkL3_intro {c : Lay} {K : Nat} {prog : List Op} {k i : Nat} {R S : List Nat}
    (hv : (allValid c R && allValid c S) = true)
    (h : runV (ctxOf c K) (((prog.drop (i * k)).take k).drop 0) (gL c K R)
      (fun R' => eqVL R' (gL c K S)) = true) :
    chunkL3 c K prog k i R S = true := by
  unfold chunkL3
  rw [hv, Bool.true_and]
  rw [List.drop_zero] at h
  exact h

end

theorem rel_prod {c : Lay} {K : Nat} (hg : Good c K) {X Y : Nat} {u v w : V} (hX : Rel c X u)
    (hY : Rel c Y v) (h : eqV (mulV (ctxOf c K) u v) w = true) : Rel c (c.mul X Y) w := by
  rw [← eqV_eq h]
  exact rel_mul hg hX hY

theorem eq_of_rel_same {c : Lay} {K : Nat} (hg : Good c K) {A B : Nat} {u : V} (hA : Rel c A u)
    (hB : Rel c B u) : A = B := by
  have e : mat3 c A = mat3 c B := by rw [← hA.2.2, hB.2.2]
  unfold mat3 at e
  rw [hg.hS] at e
  exact canon_inj hA.1 hB.1 e

theorem beq_of_rel {c : Lay} {K : Nat} (hg : Good c K) {A B : Nat} {u v : V} (hA : Rel c A u)
    (hB : Rel c B v) (h : eqV u v = true) : Nat.beq A B = true := by
  rw [eqV_eq h] at hA
  rw [eq_of_rel_same hg hA hB]
  exact Nat.beq_refl B

theorem rel_congr {c : Lay} {A B : Nat} {u : V} (h : A = B) (hA : Rel c A u) : Rel c B u := h ▸ hA

end CFSG.KC.OpsLayF3

end
