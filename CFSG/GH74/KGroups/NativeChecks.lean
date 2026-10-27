module

public import CFSG.GH74.KGroups.Checks2
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.KGroups.Perm

public section

namespace CFSG.GH74.KGroups.NativeChecks

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

theorem all_congr' {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

@[expose] def toA (σ : Equiv.Perm (Fin n)) : Array ℕ := Array.ofFn fun i : Fin n => (σ i : ℕ)

theorem rep_toA (σ : Equiv.Perm (Fin n)) : Rep n (toA σ) σ := fun x => by
  rw [toA, getElem!_ofFn_nat _ x.2]

theorem rep_powA {a : Array ℕ} {σ : Equiv.Perm (Fin n)} (h : Rep n a σ) (k : ℕ) :
    Rep n (powA n a k) (σ ^ k) := by
  induction k with
  | zero => simpa [powA] using (rep_idA (n := n))
  | succ k ih =>
    rw [pow_succ']
    exact rep_compA h ih

theorem rep_evalWA {a b : Array ℕ} {σ τ : Equiv.Perm (Fin n)} (ha : Rep n a σ) (hb : Rep n b τ)
    (w : List Bool) : Rep n (evalWA n a b w) (evalW σ τ w) := by
  induction w with
  | nil => simpa [evalWA, evalW] using (rep_idA (n := n))
  | cons c w ih =>
    cases c
    · exact rep_compA ha ih
    · exact rep_compA hb ih

theorem eqA_eq_decide {s t : Array ℕ} {g h : Equiv.Perm (Fin n)} (hs : Rep n s g)
    (ht : Rep n t h) : eqA n s t = decide (g = h) :=
  Bool.eq_iff_iff.2 (by simpa using eqA_iff hs ht)

theorem orderIsA_rep {a : Array ℕ} {σ : Equiv.Perm (Fin n)} (h : Rep n a σ) (m : ℕ) :
    orderIsA n a m = orderIs σ m := by
  have hp : ∀ k, eqA n (powA n a k) (idA n) = decide (σ ^ k = 1) := fun k =>
    eqA_eq_decide (rep_powA h k) (rep_idA (n := n))
  simp only [orderIsA, orderIs, hp]

theorem isInvolA_rep {a : Array ℕ} {σ : Equiv.Perm (Fin n)} (h : Rep n a σ) :
    isInvolA n a = (decide (σ ^ 2 = 1) && decide (σ ≠ 1)) := by
  have h1 : eqA n (compA n a a) (idA n) = decide (σ ^ 2 = 1) := by
    rw [eqA_eq_decide (rep_compA h h) (rep_idA (n := n))]
    simp [pow_two]
  have h2 : eqA n a (idA n) = decide (σ = 1) := eqA_eq_decide h (rep_idA (n := n))
  simp [isInvolA, h1, h2]

theorem centTrivCheck_eq (L : List (Equiv.Perm (Fin n))) (a b : Equiv.Perm (Fin n)) :
    centTrivCheck L a b = centTrivA n (L.map toA) (toA a) (toA b) := by
  unfold centTrivCheck centTrivA
  rw [List.all_map]
  refine all_congr' fun σ _ => ?_
  simp only [Function.comp,
    eqA_eq_decide (rep_compA (rep_toA σ) (rep_toA a)) (rep_compA (rep_toA a) (rep_toA σ)),
    eqA_eq_decide (rep_compA (rep_toA σ) (rep_toA b)) (rep_compA (rep_toA b) (rep_toA σ)),
    eqA_eq_decide (rep_toA σ) (rep_idA (n := n))]

theorem pairInvB_eq (ws : List (List Bool × ℕ)) (x y : Equiv.Perm (Fin n)) :
    pairInvB ws x y = pairInvA n ws (toA x) (toA y) := by
  unfold pairInvB pairInvA
  refine all_congr' fun wk _ => ?_
  exact (orderIsA_rep (rep_evalWA (rep_toA x) (rep_toA y) wk.1) wk.2).symm

theorem length_filter_product {α β : Type*} (p : α × β → Bool) (L1 : List α) (L2 : List β) :
    ((L1 ×ˢ L2).filter p).length = (L1.map fun a => (L2.filter fun b => p (a, b)).length).sum := by
  induction L1 with
  | nil => simp
  | cons a L1 ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.map_cons,
      List.sum_cons, List.filter_map, List.length_map]
    rfl

@[expose] def pairCountN (QP : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) : ℕ :=
  let LA := (elemsT QP).map toA
  countPairsA n ws (LA.filter fun a => orderIsA n a oa) (LA.filter fun a => orderIsA n a ob)

theorem countPairsA_map (ws : List (List Bool × ℕ)) (L1 L2 : List (Equiv.Perm (Fin n))) :
    countPairsA n ws (L1.map toA) (L2.map toA) =
      (L1.map fun a => (L2.filter fun b => pairInvB ws a b).length).sum := by
  unfold countPairsA
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, List.filter_map, List.length_map]
  congr 2
  funext b
  exact (pairInvB_eq ws a b).symm

theorem pairCountB_eq (QP : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) :
    pairCountB QP oa ob ws = pairCountN QP oa ob ws := by
  have hf : ∀ (L : List (Equiv.Perm (Fin n))) (m : ℕ),
      (L.map toA).filter (fun a => orderIsA n a m) = (L.filter fun g => orderIs g m).map toA := by
    intro L m
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun g _ => ?_
    exact orderIsA_rep (rep_toA g) m
  have h1 : pairCountN QP oa ob ws = countPairsA n ws
      (((elemsT QP).filter fun g => orderIs g oa).map toA)
      (((elemsT QP).filter fun g => orderIs g ob).map toA) := by
    unfold pairCountN
    simp only []
    rw [hf, hf]
  rw [h1, countPairsA_map]
  unfold pairCountB
  rw [length_filter_product]

@[expose] def solvN (n : ℕ) (LA LP : List (Array ℕ)) : Bool :=
  LA.all fun τ => bif isInvolA n τ then decide ((centLenA n LP τ).primeFactors.card ≤ 2)
    else true

theorem solvCheck_eq (LA LP : List (Equiv.Perm (Fin n))) :
    solvCheck LA LP = solvN n (LA.map toA) (LP.map toA) := by
  unfold solvCheck solvN
  rw [List.all_map]
  refine all_congr' fun τ _ => ?_
  simp only [Function.comp, isInvolA_rep (rep_toA τ), centLenA, List.filter_map, List.length_map]
  have hq : (fun g : Equiv.Perm (Fin n) => decide (g * τ = τ * g)) =
      ((fun g => eqA n (compA n g (toA τ)) (compA n (toA τ) g)) ∘ toA) := by
    funext g
    exact (eqA_eq_decide (rep_compA (rep_toA g) (rep_toA τ))
      (rep_compA (rep_toA τ) (rep_toA g))).symm
  rw [hq]

@[expose] def powInPN (QP : RawSchreierDatum n) (k : ℕ) (LA : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun g => bif eqA n (powA n (toA g) k) (idA n) then QP.sift g 0 else true

theorem powInPCheck_eq (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n) (k : ℕ) :
    powInPCheck LA QP k = powInPN QP k LA := by
  unfold powInPCheck powInPN
  refine all_congr' fun g _ => ?_
  rw [eqA_eq_decide (rep_powA (rep_toA g) k) (rep_idA (n := n))]

@[expose] def centInCheck (LA LS : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun σ => !(LS.all fun q => decide (σ * q = q * σ)) || decide (σ ∈ LS)

theorem centInCheck_eq (LA LS : List (Equiv.Perm (Fin n))) :
    centInCheck LA LS = centInA n (LA.map toA) (LS.map toA) := by
  unfold centInCheck centInA
  rw [List.all_map]
  refine all_congr' fun σ _ => ?_
  have h1 : (LS.map toA).all (fun q => eqA n (compA n (toA σ) q) (compA n q (toA σ))) =
      LS.all fun q => decide (σ * q = q * σ) := by
    rw [List.all_map]
    refine all_congr' fun q _ => ?_
    exact eqA_eq_decide (rep_compA (rep_toA σ) (rep_toA q)) (rep_compA (rep_toA q) (rep_toA σ))
  have h2 : (LS.map toA).any (fun q => eqA n (toA σ) q) = decide (σ ∈ LS) := by
    rw [List.any_map]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, Function.comp, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, h⟩
      rw [eqA_eq_decide (rep_toA σ) (rep_toA q)] at h
      exact (of_decide_eq_true h) ▸ hq
    · intro h
      exact ⟨σ, h, by rw [eqA_eq_decide (rep_toA σ) (rep_toA σ)]; simp⟩
  simp only [Function.comp, h1, h2]

end CFSG.GH74.KGroups.NativeChecks
