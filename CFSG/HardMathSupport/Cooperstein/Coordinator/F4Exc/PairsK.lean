module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family
public import CFSG.Certificates.Kernel.Common.Loop
import Mathlib.Tactic.Ring

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.PairsK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def betaRows0 : List (List (List ℤ)) :=
  [[[-1, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [-1, -1, -2, -2], [-1, -1, -2, 0], [-1, -1, 0, 0], [-1, 0, 0, 0]],
   [[-2, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [0, -1, -2, -2], [0, -1, -2, 0], [0, -1, 0, 0], [1, 0, 0, 0]],
   [[-2, -3, -4, -2], [-1, -3, -4, -2], [-1, -1, -2, -2], [-1, -1, -2, 0], [0, -1, -2, -2], [0, -1, -2, 0], [0, 1, 0, 0], [1, 1, 0, 0]],
   [[-2, -3, -4, -2], [-1, -3, -4, -2], [-1, -1, -2, -2], [-1, -1, 0, 0], [0, -1, -2, -2], [0, -1, 0, 0], [0, 1, 2, 0], [1, 1, 2, 0]],
   [[-2, -3, -4, -2], [-1, -3, -4, -2], [-1, -1, -2, 0], [-1, -1, 0, 0], [0, -1, -2, 0], [0, -1, 0, 0], [0, 1, 2, 2], [1, 1, 2, 2]],
   [[-2, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, -2], [-1, 0, 0, 0], [0, -1, -2, -2], [0, 1, 0, 0], [0, 1, 2, 0], [1, 2, 2, 0]],
   [[-2, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, 0], [-1, 0, 0, 0], [0, -1, -2, 0], [0, 1, 0, 0], [0, 1, 2, 2], [1, 2, 2, 2]],
   [[-2, -3, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [-1, 0, 0, 0], [0, -1, 0, 0], [0, 1, 2, 0], [0, 1, 2, 2], [1, 2, 4, 2]],
   [[-2, -3, -4, -2], [-1, -1, -2, -2], [-1, -1, -2, 0], [-1, -1, 0, 0], [0, 1, 0, 0], [0, 1, 2, 0], [0, 1, 2, 2], [1, 3, 4, 2]],
   [[-1, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, -2], [1, 0, 0, 0], [-1, -1, -2, -2], [1, 1, 0, 0], [1, 1, 2, 0], [1, 2, 2, 0]],
   [[-1, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, 0], [1, 0, 0, 0], [-1, -1, -2, 0], [1, 1, 0, 0], [1, 1, 2, 2], [1, 2, 2, 2]],
   [[-1, -3, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [1, 0, 0, 0], [-1, -1, 0, 0], [1, 1, 2, 0], [1, 1, 2, 2], [1, 2, 4, 2]]]

@[expose] def gamRows0 : List (List ℤ) :=
  [[-2, -3, -4, -2], [-1, -3, -4, -2], [-1, -2, -4, -2], [-1, -2, -2, -2], [-1, -2, -2, 0], [-1, -1, -2, -2],
   [-1, -1, -2, 0], [-1, -1, 0, 0], [-1, 0, 0, 0], [0, -1, -2, -2], [0, -1, -2, 0], [0, -1, 0, 0]]

@[expose] def betaRows3 : List (List (List ℤ)) :=
  [[[-1, -2, -3, -1], [-1, -2, -2, -1], [-1, -1, -2, -1], [0, -1, -2, -1], [-1, -1, -1, -1], [0, -1, -1, -1], [0, 0, -1, -1], [0, 0, 0, -1]],
   [[-1, -2, -3, -2], [-1, -2, -2, -1], [-1, -1, -2, -1], [0, -1, -2, -1], [-1, -1, -1, 0], [0, -1, -1, 0], [0, 0, -1, 0], [0, 0, 0, 1]],
   [[-1, -2, -3, -2], [-1, -2, -3, -1], [-1, -1, -1, -1], [0, -1, -1, -1], [-1, -1, -1, 0], [0, -1, -1, 0], [0, 0, 1, 0], [0, 0, 1, 1]],
   [[-1, -2, -3, -2], [-1, -2, -3, -1], [-1, -1, -1, -1], [0, 0, -1, -1], [-1, -1, -1, 0], [0, 0, -1, 0], [0, 1, 1, 0], [0, 1, 1, 1]],
   [[-1, -2, -3, -2], [-1, -2, -2, -1], [-1, -1, -2, -1], [0, 0, 0, -1], [-1, -1, -1, 0], [0, 0, 1, 0], [0, 1, 1, 0], [0, 1, 2, 1]],
   [[-1, -2, -3, -1], [-1, -2, -2, -1], [-1, -1, -2, -1], [0, 0, 0, 1], [-1, -1, -1, -1], [0, 0, 1, 1], [0, 1, 1, 1], [0, 1, 2, 1]],
   [[-1, -2, -3, -2], [-1, -2, -3, -1], [0, -1, -1, -1], [0, 0, -1, -1], [0, -1, -1, 0], [0, 0, -1, 0], [1, 1, 1, 0], [1, 1, 1, 1]],
   [[-1, -2, -3, -2], [-1, -2, -2, -1], [0, -1, -2, -1], [0, 0, 0, -1], [0, -1, -1, 0], [0, 0, 1, 0], [1, 1, 1, 0], [1, 1, 2, 1]],
   [[-1, -2, -3, -1], [-1, -2, -2, -1], [0, -1, -2, -1], [0, 0, 0, 1], [0, -1, -1, -1], [0, 0, 1, 1], [1, 1, 1, 1], [1, 1, 2, 1]],
   [[-1, -2, -3, -2], [-1, -1, -2, -1], [0, -1, -2, -1], [0, 0, 0, -1], [0, 0, -1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [1, 2, 2, 1]],
   [[-1, -2, -3, -1], [-1, -1, -2, -1], [0, -1, -2, -1], [0, 0, 0, 1], [0, 0, -1, -1], [0, 1, 1, 1], [1, 1, 1, 1], [1, 2, 2, 1]],
   [[-1, -2, -3, -2], [-1, -1, -1, -1], [0, -1, -1, -1], [0, 0, -1, -1], [0, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [1, 2, 3, 1]]]

@[expose] def gamRows3 : List (List ℤ) :=
  [[-1, -2, -3, -2], [-1, -2, -3, -1], [-1, -2, -2, -1], [-1, -1, -2, -1], [-1, -1, -1, -1], [-1, -1, -1, 0],
   [0, -1, -2, -1], [0, -1, -1, -1], [0, -1, -1, 0], [0, 0, -1, -1], [0, 0, -1, 0], [0, 0, 0, -1]]

theorem pinB0 : ((List.range 12).map fun i => (List.range 8).map fun j => betaL (f4n 0) i j) =
    betaRows0 := by
  have h : (((List.range 12).map fun i => (List.range 8).map fun j => betaL (f4n 0) i j) ==
    betaRows0) = true := by decide +kernel
  exact beq_iff_eq.1 h

theorem pinG0 : (List.range 12).map (gamL (f4n 0)) = gamRows0 := by
  have h : ((List.range 12).map (gamL (f4n 0)) == gamRows0) = true := by decide +kernel
  exact beq_iff_eq.1 h

theorem pinB3 : ((List.range 12).map fun i => (List.range 8).map fun j => betaL (f4n 3) i j) =
    betaRows3 := by
  have h : (((List.range 12).map fun i => (List.range 8).map fun j => betaL (f4n 3) i j) ==
    betaRows3) = true := by decide +kernel
  exact beq_iff_eq.1 h

theorem pinG3 : (List.range 12).map (gamL (f4n 3)) = gamRows3 := by
  have h : ((List.range 12).map (gamL (f4n 3)) == gamRows3) = true := by decide +kernel
  exact beq_iff_eq.1 h

@[expose] def vclassBody (M a dg : ℕ) (β β' γ γ' : List ℤ) : Bool :=
  (List.range 4).all fun c =>
    (((a : ℤ) * (β.getD c 0 - β'.getD c 0) - (2 : ℤ) ^ dg * (γ.getD c 0 - γ'.getD c 0)) % (M : ℤ)) == 0

@[expose] def xc (a dg : ℕ) (β γ : List ℤ) (c : ℕ) : ℤ := (a : ℤ) * β.getD c 0 - (2 : ℤ) ^ dg * γ.getD c 0

@[expose] def keyN (M a dg : ℕ) (β γ : List ℤ) : ℕ :=
  (xc a dg β γ 0 % (M : ℤ)).toNat + (xc a dg β γ 1 % (M : ℤ)).toNat * 64 +
    (xc a dg β γ 2 % (M : ℤ)).toNat * 4096 + (xc a dg β γ 3 % (M : ℤ)).toNat * 262144

@[expose] noncomputable def strictBP (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceL (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => strictBP a fun a' => ih fun l' => k (a' :: l')) l k

@[expose] noncomputable def forceLL (L : List (List ℕ)) (k : List (List ℕ) → Bool) : Bool :=
  List.rec (motive := fun _ => (List (List ℕ) → Bool) → Bool) (fun k => k [])
    (fun r _ ih k => forceL r fun r' => ih fun L' => k (r' :: L')) L k

@[expose] noncomputable def allP {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

@[expose] noncomputable def disj (L : List (List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r rs ih =>
    bAnd(allP (fun x => allP (fun r' => allP (fun y =>
      Bool.rec (motive := fun _ => Bool) true false (Nat.beq x y)) r') rs) r, ih)) L

@[expose] def keyRowsT (M a dg : ℕ) (R : List (List (List ℤ))) (G : List (List ℤ)) :
    List (List ℕ) :=
  List.zipWith (fun r γ => r.map fun β => keyN M a dg β γ) R G

@[expose] noncomputable def fastD (n b c dg : ℕ) (R : List (List (List ℤ))) (G : List (List ℤ)) :
    Bool :=
  forceLL (keyRowsT (2 ^ n - 1) (2 ^ b + 2 ^ c) dg R G) disj

@[expose] noncomputable def digitF (n b c dg : ℕ) (s : Fin Tag.F4.rank) : Bool :=
  bIf(Nat.beq s.val 0, fastD n b c dg betaRows0 gamRows0,
    bIf(Nat.beq s.val 3, fastD n b c dg betaRows3 gamRows3, true))

@[expose] def smallG (D : ℕ → ℕ → ℕ → ℕ → Fin Tag.F4.rank → Bool) : Bool :=
  (List.finRange Tag.F4.rank).all fun s => (s.val != 0 && s.val != 3) ||
    [2, 3, 4, 5, 6].all fun n => (List.range n).all fun b => (List.range n).all fun c =>
      decide (c ≤ b) || D n b c b s || D n b c c s

theorem smallG_digitF : smallG digitF = true := by decide +kernel

theorem strictBP_eq (y : ℕ) (k : ℕ → Bool) : strictBP y k = k y := by
  cases y <;> rfl

theorem bAnd_eqP (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem forceL_eq (l : List ℕ) (k : List ℕ → Bool) : forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    have e : forceL (a :: l) k = strictBP a fun a' => forceL l fun l' => k (a' :: l') := rfl
    rw [e, strictBP_eq, ih]

theorem forceLL_eq (L : List (List ℕ)) (k : List (List ℕ) → Bool) : forceLL L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons r L ih =>
    have e : forceLL (r :: L) k = forceL r fun r' => forceLL L fun L' => k (r' :: L') := rfl
    rw [e, forceL_eq, ih]

theorem allP_spec {α : Type} (f : α → Bool) (L : List α) (h : allP f L = true) :
    ∀ a ∈ L, f a = true := by
  induction L with
  | nil => simp
  | cons b L ih =>
    have e : allP f (b :: L) = (f b && allP f L) := bAnd_eqP _ _
    rw [e, Bool.and_eq_true] at h
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact ih h.2 a ha

theorem disj_spec (L : List (List ℕ)) (h : disj L = true) :
    L.Pairwise fun r r' => ∀ x ∈ r, ∀ y ∈ r', x ≠ y := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons r rs ih =>
    have e : disj (r :: rs) = (allP (fun x => allP (fun r' => allP (fun y =>
        Bool.rec (motive := fun _ => Bool) true false (Nat.beq x y)) r') rs) r && disj rs) :=
      bAnd_eqP _ _
    rw [e, Bool.and_eq_true] at h
    refine List.Pairwise.cons (fun r' hr' x hx y hy hxy => ?_) (ih h.2)
    have h1 := allP_spec _ _ (allP_spec _ _ (allP_spec _ _ h.1 x hx) r' hr') y hy
    subst hxy
    rw [Nat.beq_refl] at h1
    exact Bool.false_ne_true h1

theorem zipWith_map_same {α β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map fun x => f (g x) (h x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem keyRows_map (B : ℕ → ℕ → List ℤ) (g : ℕ → List ℤ) (M a dg : ℕ) :
    keyRowsT M a dg ((List.range 12).map fun i => (List.range 8).map fun j => B i j)
        ((List.range 12).map g) =
      (List.range 12).map fun i => (List.range 8).map fun j => keyN M a dg (B i j) (g i) := by
  unfold keyRowsT
  rw [zipWith_map_same]
  refine congrArg (List.map · (List.range 12)) (funext fun i => ?_)
  simp only [List.map_map, Function.comp_def]

theorem key_eq_of_vclass {M a dg : ℕ} {β β' γ γ' : List ℤ}
    (h : vclassBody M a dg β β' γ γ' = true) : keyN M a dg β γ = keyN M a dg β' γ' := by
  simp only [vclassBody, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e : ∀ c < 4, xc a dg β γ c % (M : ℤ) = xc a dg β' γ' c % (M : ℤ) := by
    intro c hc
    have h1 := h c hc
    have hr : (a : ℤ) * (β.getD c 0 - β'.getD c 0) - (2 : ℤ) ^ dg * (γ.getD c 0 - γ'.getD c 0) =
        xc a dg β γ c - xc a dg β' γ' c := by
      unfold xc
      ring
    rw [hr] at h1
    exact (Int.modEq_iff_dvd.2 (Int.dvd_of_emod_eq_zero h1)).symm
  unfold keyN
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]

theorem body_of_disj {B : ℕ → ℕ → List ℤ} {g : ℕ → List ℤ} {M a dg : ℕ}
    (h : disj ((List.range 12).map fun i => (List.range 8).map fun j => keyN M a dg (B i j) (g i)) =
      true) :
    ((List.range 12).all fun i => (List.range 12).all fun i' => i == i' ||
      (List.range 8).all fun j => (List.range 8).all fun j' =>
        !vclassBody M a dg (B i j) (B i' j') (g i) (g i')) = true := by
  have hp := List.pairwise_iff_getElem.1 (disj_spec _ h)
  have key : ∀ i i', i < i' → i' < 12 → ∀ j < 8, ∀ j' < 8,
      keyN M a dg (B i j) (g i) ≠ keyN M a dg (B i' j') (g i') := by
    intro i i' hii hi' j hj j' hj'
    have h1 := hp i i' (by simp only [List.length_map, List.length_range]; omega)
      (by simp only [List.length_map, List.length_range]; omega) hii
    simp only [List.getElem_map, List.getElem_range] at h1
    exact h1 _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩) _
      (List.mem_map.2 ⟨j', List.mem_range.2 hj', rfl⟩)
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  intro i hi i' hi'
  by_cases hii : i = i'
  · exact Or.inl hii
  · right
    intro j hj j' hj'
    cases hv : vclassBody M a dg (B i j) (B i' j') (g i) (g i')
    · rfl
    · have he := key_eq_of_vclass hv
      rcases Nat.lt_or_gt_of_ne hii with hlt | hlt
      · exact absurd he (key i i' hlt hi' j hj j' hj')
      · exact absurd he.symm (key i' i hlt hi j' hj' j hj)

theorem digitBody_of (s : Fin Tag.F4.rank) (hs : s.val = 0 ∨ s.val = 3) {n b c dg : ℕ}
    (h : digitF n b c dg s = true) :
    ((List.range 12).all fun i => (List.range 12).all fun i' => i == i' ||
      (List.range 8).all fun j => (List.range 8).all fun j' =>
        !vclassBody (2 ^ n - 1) (2 ^ b + 2 ^ c) dg (betaL s i j) (betaL s i' j') (gamL s i)
          (gamL s i')) = true := by
  rcases hs with hs | hs
  · have e : s = f4n 0 := Fin.ext hs
    subst e
    have e2 : digitF n b c dg (f4n 0) = fastD n b c dg betaRows0 gamRows0 := rfl
    rw [e2] at h
    unfold fastD at h
    rw [forceLL_eq, ← pinB0, ← pinG0, keyRows_map] at h
    exact body_of_disj h
  · have e : s = f4n 3 := Fin.ext hs
    subst e
    have e2 : digitF n b c dg (f4n 3) = fastD n b c dg betaRows3 gamRows3 := rfl
    rw [e2] at h
    unfold fastD at h
    rw [forceLL_eq, ← pinB3, ← pinG3, keyRows_map] at h
    exact body_of_disj h

theorem smallG_mono (D D' : ℕ → ℕ → ℕ → ℕ → Fin Tag.F4.rank → Bool)
    (hDD : ∀ s : Fin Tag.F4.rank, (s.val = 0 ∨ s.val = 3) → ∀ n b c dg,
      D n b c dg s = true → D' n b c dg s = true)
    (h : smallG D = true) : smallG D' = true := by
  simp only [smallG, List.all_eq_true, Bool.or_eq_true] at h ⊢
  intro s hs
  rcases h s hs with h1 | h1
  · exact Or.inl h1
  · by_cases hs' : s.val = 0 ∨ s.val = 3
    · right
      intro n hn b hb c hc
      rcases h1 n hn b hb c hc with (h2 | h2) | h2
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr (hDD s hs' _ _ _ _ h2))
      · exact Or.inr (hDD s hs' _ _ _ _ h2)
    · left
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.PairsK

end
