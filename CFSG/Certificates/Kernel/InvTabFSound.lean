module

public import Certificates.Data.Kernel.InvTabK
public import CFSG.Quasithin.Background.HMathieuEnum

public section

namespace CFSG.KC.InvTabK

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {P : Type*} [Group P] [DecidableEq P]

structure TabSpec (m : Nat) (cA : Nat → Nat → Bool) (pA : Nat → Nat → Nat) (X : Nat → P) :
    Prop where
  one : ∀ i, m ≤ i → X i = 1
  inj : ∀ i ≤ m, ∀ j ≤ m, X i = X j → i = j
  comm : ∀ i j, cA i j = true ↔ X i * X j = X j * X i
  prod : ∀ i ≤ m, ∀ j ≤ m, cA i j = true → pA i j ≤ m ∧ X i * X j = X (pA i j)

theorem forallGreedyF_add (m : Nat) (cA : Nat → Nat → Bool) (pA : Nat → Nat → Nat)
    (pred : List Nat → Bool) (b : Nat) :
    ∀ a l, forallGreedyF m cA pA pred (a + b) l =
      forallGreedyF m cA pA (forallGreedyF m cA pA pred b) a l
  | 0, l => by rw [Nat.zero_add]; rfl
  | a + 1, l => by
    rw [show a + 1 + b = (a + b) + 1 by omega, forallGreedyF, forallGreedyF]
    congr 1
    funext x
    exact forallGreedyF_add m cA pA pred b a (x :: l)

theorem forallGreedyF_mono {m : Nat} {cA : Nat → Nat → Bool} {pA : Nat → Nat → Nat}
    {p q : List Nat → Bool} (h : ∀ l, p l = true → q l = true) :
    ∀ k l, forallGreedyF m cA pA p k l = true → forallGreedyF m cA pA q k l = true
  | 0, l, hp => h l hp
  | k + 1, l, hp => by
    rw [forallGreedyF, List.all_eq_true] at hp ⊢
    exact fun x hx => forallGreedyF_mono h k (x :: l) (hp x hx)

theorem forallGreedyF_roots {m : Nat} {cA : Nat → Nat → Bool} {pA : Nat → Nat → Nat}
    {p : List Nat → Bool} {k : Nat} (h : ∀ r < m, forallGreedyF m cA pA p k [r] = true) :
    forallGreedyF m cA pA p (k + 1) [] = true := by
  rw [forallGreedyF, List.all_eq_true]
  intro x hx
  unfold greedyExtF at hx
  exact h x (List.mem_range.1 (List.mem_of_mem_drop (List.mem_filter.1 hx).1))

section Sim

variable {m : Nat} {cA : Nat → Nat → Bool} {pA : Nat → Nat → Nat} {X : Nat → P}
  (hT : TabSpec m cA pA X)
include hT

@[expose] def rinvF (m : Nat) (X : Nat → P) : List P := (List.range m).map X

@[expose] def IsChainF (m : Nat) (cA : Nat → Nat → Bool) (l : List Nat) : Prop :=
  (∀ a ∈ l, a < m) ∧ ∀ a ∈ l, ∀ b ∈ l, cA a b = true

omit hT in
theorem IsChainF.cons {l : List Nat} {x : Nat} (hl : IsChainF m cA l) (hx : x < m)
    (hxl : ∀ y ∈ l, cA x y = true) (hlx : ∀ y ∈ l, cA y x = true) (hxx : cA x x = true) :
    IsChainF m cA (x :: l) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · rcases List.mem_cons.1 ha with h | h
    · rw [h]
      exact hx
    · exact hl.1 a h
  · rcases List.mem_cons.1 ha with h | h <;> rcases List.mem_cons.1 hb with h' | h'
    · rw [h, h']
      exact hxx
    · rw [h]
      exact hxl b h'
    · rw [h']
      exact hlx a h
    · exact hl.2 a h b h'

omit hT in
theorem all_congr_memF {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem eq_one_iff {i : Nat} (hi : i ≤ m) : X i = 1 ↔ i = m := by
  constructor
  · intro h
    exact hT.inj i hi m le_rfl (h.trans (hT.one m le_rfl).symm)
  · rintro rfl
    exact hT.one _ le_rfl

theorem pos_X {i : Nat} (hi : i ≤ m) : pos (rinvF m X) (X i) = i := by
  have key : ∀ k ≤ m, ∀ i ≤ k, ((List.range k).map X).idxOf (X i) = i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      rfl
    | succ k ih =>
      intro hk i hik
      rw [List.range_succ, List.map_append, List.map_singleton]
      rcases Nat.lt_or_ge i k with hlt | hge
      · have hmem : X i ∈ (List.range k).map X := List.mem_map.2 ⟨i, List.mem_range.2 hlt, rfl⟩
        rw [List.idxOf_append_of_mem hmem]
        exact ih (by omega) i (le_of_lt hlt)
      · have hnm : X i ∉ (List.range k).map X := by
          intro h
          obtain ⟨j, hj, hji⟩ := List.mem_map.1 h
          have := List.mem_range.1 hj
          have := hT.inj j (by omega) i (by omega) hji
          omega
        rw [List.idxOf_append_of_notMem hnm, List.length_map, List.length_range]
        rcases Nat.lt_or_ge k i with hlt' | hle'
        · have hnm' : X i ∉ [X k] := by
            rw [List.mem_singleton]
            intro h
            have := hT.inj i (by omega) k (by omega) h
            omega
          rw [List.idxOf_eq_length hnm', List.length_singleton]
          omega
        · have hik' : i = k := by omega
          subst hik'
          rw [List.idxOf_cons_self]
          rfl
  exact key m le_rfl i hi

theorem subprods_mapF {l : List Nat} (hl : IsChainF m cA l) :
    (∀ s ∈ subprodsF m pA l, s ≤ m) ∧ subprods (l.map X) = (subprodsF m pA l).map X := by
  induction l with
  | nil => exact ⟨by simp [subprodsF], by simp [subprodsF, subprods, hT.one m le_rfl]⟩
  | cons y l ih =>
    have hl' : IsChainF m cA l :=
      ⟨fun a ha => hl.1 a (List.mem_cons_of_mem y ha),
        fun a ha b hb => hl.2 a (List.mem_cons_of_mem y ha) b (List.mem_cons_of_mem y hb)⟩
    obtain ⟨hle, heq⟩ := ih hl'
    have hy : y < m := hl.1 y List.mem_cons_self
    have hcomm : ∀ s ∈ subprodsF m pA l, cA y s = true := by
      intro s hs
      rw [hT.comm]
      have hyl : ∀ x ∈ l.map X, X y * x = x * X y := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact (hT.comm _ _).1 (hl.2 y List.mem_cons_self a (List.mem_cons_of_mem y ha))
      have hsm : X s ∈ subprods (l.map X) := by
        rw [heq]
        exact List.mem_map.2 ⟨s, hs, rfl⟩
      exact commute_subprods hyl _ hsm
    refine ⟨fun s hs => ?_, ?_⟩
    · simp only [subprodsF, List.mem_append, List.mem_map] at hs
      rcases hs with hs | ⟨t, ht, rfl⟩
      · exact hle s hs
      · exact (hT.prod y (le_of_lt hy) t (hle t ht) (hcomm t ht)).1
    · rw [List.map_cons, subprods, heq, subprodsF, List.map_append, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      exact (hT.prod y (le_of_lt hy) s (hle s hs) (hcomm s hs)).2

theorem mem_subprods_mapF_iff {l : List Nat} (hl : IsChainF m cA l) {x : Nat} (hx : x ≤ m) :
    X x ∈ subprods (l.map X) ↔ x ∈ subprodsF m pA l := by
  obtain ⟨hle, heq⟩ := subprods_mapF hT hl
  rw [heq, List.mem_map]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rwa [← hT.inj s (hle s hs) x hx hsx]
  · intro h
    exact ⟨x, h, rfl⟩

theorem greedyExt_mapF {l : List Nat} (hl : IsChainF m cA l) :
    greedyExt (rinvF m X) (l.map X) = (greedyExtF m cA pA l).map X := by
  obtain ⟨hle, heq⟩ := subprods_mapF hT hl
  have hst : startPos (rinvF m X) (l.map X) = startF l := by
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [List.map_cons, startPos, startF]
      rw [pos_X hT (le_of_lt (hl.1 a List.mem_cons_self))]
  unfold greedyExt greedyExtF
  rw [hst, show (rinvF m X).drop (startF l) = ((List.range m).drop (startF l)).map X by
    rw [rinvF, List.map_drop], List.filter_map]
  dsimp only
  congr 1
  apply List.filter_congr
  intro x hx
  have hxm : x < m := List.mem_range.1 (List.mem_of_mem_drop hx)
  simp only [Function.comp_apply]
  have h1 : ((l.map X).all fun y => decide (X x * y = y * X x)) = l.all fun y => cA x y := by
    rw [List.all_map]
    refine all_congr_memF fun y _ => ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hT.comm]
  have h2 : decide (X x ∈ subprods (l.map X)) = (subprodsF m pA l).contains x := by
    rw [List.contains_eq_mem, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact mem_subprods_mapF_iff hT hl (le_of_lt hxm)
  have h3 : (l.all fun y => cA x y) = true →
      ((subprods (l.map X)).all fun s =>
        decide (s = 1) || decide (pos (rinvF m X) (X x) < pos (rinvF m X) (X x * s))) =
      (subprodsF m pA l).all fun s => s == m || decide (x < pA x s) := by
    intro hxl
    rw [heq, List.all_map]
    refine all_congr_memF fun s hs => ?_
    simp only [Function.comp_apply]
    have hsm := hle s hs
    have hcs : cA x s = true := by
      rw [hT.comm]
      have hxl' : ∀ z ∈ l.map X, X x * z = z * X x := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
        exact (hT.comm _ _).1 (List.all_eq_true.1 hxl a ha)
      have hsm' : X s ∈ subprods (l.map X) := by
        rw [heq]
        exact List.mem_map.2 ⟨s, hs, rfl⟩
      exact commute_subprods hxl' _ hsm'
    obtain ⟨hpm, hpe⟩ := hT.prod x (le_of_lt hxm) s hsm hcs
    rw [hpe, pos_X hT (le_of_lt hxm), pos_X hT hpm]
    have : decide (X s = 1) = (s == m) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
      exact eq_one_iff hT hsm
    rw [this]
  rw [h1, h2]
  cases hA : (l.all fun y => cA x y)
  · simp
  · rw [h3 hA]

@[expose] noncomputable def predOfF (m : Nat) (X : Nat → P) (pred : List Nat → Bool) :
    List P → Bool := fun l => pred (l.map (pos (rinvF m X)))

theorem map_pos_X {l : List Nat} (hl : ∀ a ∈ l, a ≤ m) : (l.map X).map (pos (rinvF m X)) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => pos_X hT (hl a ha)

theorem forallGreedy_mapF (pred : List Nat → Bool) :
    ∀ (k : Nat) {l : List Nat}, IsChainF m cA l →
      forallGreedy (rinvF m X) (predOfF m X pred) k (l.map X) = forallGreedyF m cA pA pred k l := by
  intro k
  induction k with
  | zero =>
    intro l hl
    simp only [forallGreedy, forallGreedyF, predOfF]
    rw [map_pos_X hT fun a ha => le_of_lt (hl.1 a ha)]
  | succ k ih =>
    intro l hl
    simp only [forallGreedy, forallGreedyF]
    rw [greedyExt_mapF hT hl, List.all_map]
    refine all_congr_memF fun x hx => ?_
    simp only [Function.comp_apply]
    have hx' := hx
    unfold greedyExtF at hx'
    rw [List.mem_filter] at hx'
    obtain ⟨hxr, hxc⟩ := hx'
    have hxm : x < m := List.mem_range.1 (List.mem_of_mem_drop hxr)
    simp only [Bool.and_eq_true] at hxc
    have hxl : ∀ y ∈ l, cA x y = true := fun y hy => List.all_eq_true.1 hxc.1.1 y hy
    have hlx : ∀ y ∈ l, cA y x = true := by
      intro y hy
      rw [hT.comm]
      exact ((hT.comm _ _).1 (hxl y hy)).symm
    have hxx : cA x x = true := by
      rw [hT.comm]
    have := ih (hl.cons hxm hxl hlx hxx)
    rwa [List.map_cons] at this

theorem forallGreedyF_sound {pred : List Nat → Bool} {k : Nat}
    (h : forallGreedyF m cA pA pred k [] = true) (B : Subgroup P) [Finite B]
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hR : ∀ x ∈ B, x ≠ 1 → ∃ i < m, x = X i) (hcard : Nat.card B = 2 ^ k) :
    ∃ l : List Nat, IsChainF m cA l ∧ pred l = true ∧
      ∀ x, x ∈ B ↔ ∃ s ∈ subprodsF m pA l, x = X s := by
  classical
  have hnil : IsChainF m cA [] := ⟨by simp, by simp⟩
  have h' : forallGreedy (rinvF m X) (predOfF m X pred) k [] = true := by
    have := forallGreedy_mapF hT pred k hnil
    rw [List.map_nil] at this
    rw [this]
    exact h
  have hR' : ∀ x ∈ B, x ≠ 1 → x ∈ rinvF m X := by
    intro x hx hx1
    obtain ⟨i, hi, rfl⟩ := hR x hx hx1
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  obtain ⟨l', -, hind, hmem, hpred⟩ := forallGreedy_sound h' B hcomm hsq hR' hcard
  have hl'B : ∀ y ∈ l', ∃ i < m, y = X i := by
    intro y hy
    have hyB : y ∈ B := (hmem y).2 (mem_subprods_of_mem hy)
    have hy1 : y ≠ 1 := by
      clear hpred hmem
      induction hind with
      | nil => simp at hy
      | cons x l hx hx1 _ _ _ ih =>
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hx1
        · exact ih hy
    exact hR y hyB hy1
  set lI := l'.map (pos (rinvF m X)) with hlI
  have hback : lI.map X = l' := by
    rw [hlI, List.map_map]
    conv_rhs => rw [← List.map_id l']
    refine List.map_congr_left fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := hl'B y hy
    simp only [Function.comp_apply, id]
    rw [pos_X hT (le_of_lt hi)]
  have hlt : ∀ a ∈ lI, a < m := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, rfl⟩ := hl'B y hy
    rw [pos_X hT (le_of_lt hi)]
    exact hi
  have hch : IsChainF m cA lI := by
    refine ⟨hlt, fun a ha b hb => ?_⟩
    rw [hT.comm]
    have hci := isCommInvol_of_indepList hind
    have ha' : X a ∈ l' := by rw [← hback]; exact List.mem_map.2 ⟨a, ha, rfl⟩
    have hb' : X b ∈ l' := by rw [← hback]; exact List.mem_map.2 ⟨b, hb, rfl⟩
    exact hci.2 _ ha' _ hb'
  refine ⟨lI, hch, hpred, fun x => ?_⟩
  rw [hmem, ← hback, (subprods_mapF hT hch).2, List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

end Sim

end CFSG.KC.InvTabK

end
