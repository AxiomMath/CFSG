module

public import CFSG.Certificates.Kernel.TabPackM22
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck

public section

namespace CFSG.KTabPack.Out

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck

@[expose] noncomputable def dedupN : List Nat → List Nat :=
  List.rec [] fun x l ih => Bool.rec (x :: ih) ih (memN x l)

@[expose] noncomputable def classN (TP : List (Nat × Nat)) (x : Nat) : List Nat :=
  dedupN (TP.map fun p => pmK (pmK p.1 22 x) 22 p.2)

@[expose] noncomputable def uniqN (T : List Nat) (TP : List (Nat × Nat)) (F : List Nat) : Bool :=
  allR (fun a =>
    !(allR (fun x => allR (fun y => commN 22 x y) (classN TP a)) (classN TP a)) ||
    !(Nat.beq (List.length (filterR (fun l => allR (fun x => commN 22 l x) (classN TP a)) T)) 16) ||
    allR (fun x => memN x F) (classN TP a))
  (filterR (fun x => Nat.beq (List.length (classN TP x)) 8) (filterR (isInvN 22) T))

theorem dedupN_enc {n : Nat} : ∀ {l : List (List Nat)}, (∀ x ∈ l, W n x) → l.dedup.map enc = dedupN (l.map enc)
  | [], _ => by simp [dedupN]
  | x :: l, h => by
    have hl : ∀ y ∈ l, W n y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hm := decide_mem_enc (h x (List.mem_cons_self ..)) hl
    change _ = @Bool.rec (fun _ => List Nat) (enc x :: dedupN (l.map enc)) (dedupN (l.map enc))
      (memN (enc x) (l.map enc))
    rw [← hm, ← dedupN_enc hl]
    by_cases hx : x ∈ l
    · simp only [List.dedup_cons_of_mem hx, decide_eq_true hx]
    · simp only [List.dedup_cons_of_notMem hx, decide_eq_false hx, List.map_cons]

theorem tinv_W {t : List Nat} (ht : W 22 t) : W 22 (tinv t) := by
  refine ⟨by simp [tinv], fun j hj => ?_⟩
  simp only [tinv, List.mem_map] at hj
  obtain ⟨i, -, rfl⟩ := hj
  have := List.idxOf_le_length (l := t) (a := i)
  rw [ht.1] at this
  omega

theorem tmul_eq : tmul = tm := rfl

theorem isInv_eq : isInv = isInvT 22 := rfl

theorem comm_eq : comm = commT := rfl

theorem class_W {T : List (List Nat)} (hT : ∀ x ∈ T, W 22 x) {x : List Nat} (hx : W 22 x) :
    ∀ y ∈ classTabs T x, W 22 y := by
  intro y hy
  simp only [classTabs, List.mem_dedup, List.mem_map] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  rw [tmul_eq]
  exact W_tm (W_tm (hT a ha) hx) (tinv_W (hT a ha))

theorem class_enc {T : List (List Nat)} (hT : ∀ x ∈ T, W 22 x) {x : List Nat} (hx : W 22 x) :
    (classTabs T x).map enc = classN (T.map fun a => (enc a, enc (tinv a))) (enc x) := by
  have hm : ∀ y ∈ T.map (fun a => tmul (tmul a x) (tinv a)), W 22 y := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
    rw [tmul_eq]
    exact W_tm (W_tm (hT a ha) hx) (tinv_W (hT a ha))
  rw [classTabs, dedupN_enc hm, classN, List.map_map, List.map_map]
  refine congrArg dedupN (List.map_congr_left fun a ha => ?_)
  simp only [Function.comp_apply, tmul_eq]
  rw [enc_tm (W_tm (hT a ha) hx) (tinv_W (hT a ha)), enc_tm (hT a ha) hx]

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  simp [Nat.beq_eq]

theorem uniqOK_eq {T F : List (List Nat)} (hT : ∀ x ∈ T, W 22 x) (hF : ∀ x ∈ F, W 22 x) :
    uniqOK T F = uniqN (T.map enc) (T.map fun a => (enc a, enc (tinv a))) (F.map enc) := by
  have hI := filter_W (f := isInvT 22) hT
  have hI8 := filter_W (f := fun x => (classTabs T x).length == 8) hI
  simp only [uniqOK, cls8Invs, uniqN, isInv_eq, comm_eq]
  rw [← filter_enc (fun x hx => isInv_enc (by decide) (hT x hx)),
    ← filter_enc (I := T.filter (isInvT 22)) (f := fun x => (classTabs T x).length == 8)
      (g := fun y => Nat.beq (classN (T.map fun a => (enc a, enc (tinv a))) y).length 8)
      (fun x hx => by beta_reduce; rw [← class_enc hT (hI x hx), List.length_map, beq_nat])]
  refine all_enc hI8 fun a ha => ?_
  have hC := class_W hT (hI8 a ha)
  rw [← class_enc hT (hI8 a ha)]
  have p1 : ((classTabs T a).all fun x => (classTabs T a).all fun y => commT x y) =
      allR (fun x => allR (fun y => commN 22 x y) ((classTabs T a).map enc))
        ((classTabs T a).map enc) :=
    all_enc (g := fun x' => allR (fun y => commN 22 x' y) ((classTabs T a).map enc)) hC
      fun x hx => all_enc (g := fun y => commN 22 (enc x) y) hC
        fun y hy => comm_enc (hC x hx) (hC y hy)
  have p2 : ((T.filter fun l => (classTabs T a).all fun x => commT l x).length == 16) =
      Nat.beq (filterR (fun l => allR (fun x => commN 22 l x) ((classTabs T a).map enc))
        (T.map enc)).length 16 := by
    rw [← filter_enc (g := fun l' => allR (fun x => commN 22 l' x) ((classTabs T a).map enc))
      (fun l hl => all_enc (g := fun x => commN 22 (enc l) x) hC
      fun x hx => comm_enc (hT l hl) (hC x hx)), List.length_map, beq_nat]
  have p3 : ((classTabs T a).all fun x => decide (x ∈ F)) =
      allR (fun x => memN x (F.map enc)) ((classTabs T a).map enc) :=
    all_enc (g := fun x' => memN x' (F.map enc)) hC fun x hx => decide_mem_enc (hC x hx) hF
  rw [p1, p2, p3]

theorem s0_W : ∀ x ∈ s0Tabs, W 22 x := by
  rw [s0Tabs, M22.span_eq]
  exact spanT_W (by decide) (by unfold W; decide +kernel)

theorem f1_W : ∀ x ∈ f1Tabs, W 22 x := by
  unfold W; decide +kernel

end CFSG.KTabPack.Out
