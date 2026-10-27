module

public import Certificates.Data.Kernel.HMathieu.PredXi
public import CFSG.Certificates.Kernel.HMathieu.GreedySound

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1

variable {P : Type*} [Group P] [DecidableEq P] {posF : P → Nat} {R : List P}

theorem forallGreedyP_congr {p q : List P → Bool} : ∀ (j : Nat) (l : List P),
    (∀ l' : List P, l'.length = l.length + j → p l' = q l') →
      forallGreedyP posF R p j l = forallGreedyP posF R q j l
  | 0, l, h => h l rfl
  | j + 1, l, h => by
    rw [forallGreedyP, forallGreedyP]
    congr 1
    funext x
    exact forallGreedyP_congr j (x :: l) fun l' hl' => h l' (by simp at hl' ⊢; omega)

theorem forallGreedyP_of_all {pred : Nat → List P → Bool} {K : Nat}
    (h : forallGreedyAll posF R (fun l => l.isEmpty || pred l.length l) K [] = true) :
    ∀ k, 1 ≤ k → k ≤ K → forallGreedyP posF R (pred k) k [] = true := by
  intro k hk hkK
  have e := forallGreedyAll_le K [] h k hkK
  rw [forallGreedyP_congr (q := pred k) k [] fun l' hl' => ?_] at e
  · exact e
  · simp only [List.length_nil, Nat.zero_add] at hl'
    have hne : l'.isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact List.exists_mem_of_length_pos (by omega)
    rw [hne, Bool.false_or, hl']

theorem forallGreedyAll_mono_of {I : List P → Prop} {p q : List P → Bool}
    (hstep : ∀ l x, I l → x ∈ greedyExtP posF R l → I (x :: l))
    (hpq : ∀ l, I l → p l = true → q l = true) :
    ∀ (k : Nat) (l : List P), I l → forallGreedyAll posF R p k l = true →
      forallGreedyAll posF R q k l = true
  | 0, l, hl, h => hpq l hl h
  | k + 1, l, hl, h => by
    simp only [forallGreedyAll, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨hpq l hl h.1, fun x hx =>
      forallGreedyAll_mono_of hstep hpq k (x :: l) (hstep l x hl hx) (h.2 x hx)⟩

theorem indep_step {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) (l : List P) (x : P)
    (hl : (∀ y ∈ l, y ∈ R) ∧ IndepList l) (hx : x ∈ greedyExtP posF R l) :
    (∀ y ∈ x :: l, y ∈ R) ∧ IndepList (x :: l) := by
  obtain ⟨hxR, hxl, hxS⟩ := mem_greedyExtP hx
  refine ⟨fun y hy => ?_, IndepList.cons x l (T.invol x hxR).2 (T.invol x hxR).1 hxl hxS hl.2⟩
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hxR
  · exact hl.1 y hy

theorem xiCands_eq {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {l : List P}
    (hci : IsCommInvol l) {F : List (List Nat)} {n : Nat} {act : P → Nat → Nat}
    (hF : ∀ s ∈ R, F.getD (R.idxOf s) [] = fixMasks n act [s]) :
    xiCands n act l = xiCandsT F R.length ((subprods l).map R.idxOf) := by
  unfold xiCands xiCandsT
  have key : ∀ S : List P, (∀ s ∈ S, s ∈ R ∨ s = 1) →
      (S.filter (· ≠ 1)).flatMap (fun s => fixMasks n act [s]) =
        ((S.map R.idxOf).filter fun s => !(Nat.beq s R.length)).flatMap (F.getD · []) := by
    intro S
    induction S with
    | nil => intro _; rfl
    | cons s S ih =>
      intro hS
      have ih' := ih fun t ht => hS t (List.mem_cons_of_mem s ht)
      by_cases h1 : s = 1
      · subst h1
        have e : R.idxOf (1 : P) = R.length := List.idxOf_eq_length (one_notMem T)
        rw [List.filter_cons_of_neg (by simp), List.map_cons, e,
          List.filter_cons_of_neg (by simp [Nat.beq_refl])]
        exact ih'
      · have hsR : s ∈ R := (hS s List.mem_cons_self).resolve_right h1
        have hlt : R.idxOf s < R.length := List.idxOf_lt_length_iff.2 hsR
        have hb : Nat.beq (R.idxOf s) R.length = false := by
          cases hq : Nat.beq (R.idxOf s) R.length
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) (Nat.ne_of_lt hlt)
        rw [List.filter_cons_of_pos (by simpa using h1), List.map_cons,
          List.filter_cons_of_pos (by simp [hb]), List.flatMap_cons, List.flatMap_cons, ih',
          hF s hsR]
  exact key _ fun s hs => mem_or_one_of_subprods T hci hs

theorem indepCheck_of_indepK {r : Nat} {vs b : List Nat} (h : indepK r vs b = true) :
    indepCheck r vs b = true := by
  simp only [indepK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  simp only [indepCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨h.1.1, fun x hx => by simpa using h.1.2 x hx⟩, (nodup_of_nodupB _ _ h.2).1⟩

end CFSG.KC.HMathieu

end
