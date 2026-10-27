module

public import Init
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.PK

structure BS where
  pts : List Nat
  par : List Nat
  lab : List Nat

namespace BS

@[expose] def letter (F : Nat → Nat → Nat) (h p : Nat) (s : BS) (l : Nat) : BS :=
  if F l p ∈ s.pts then s else ⟨s.pts ++ [F l p], s.par ++ [h], s.lab ++ [l]⟩

@[expose] def step (F : Nat → Nat → Nat) (lv : List Nat) (s : BS) (h : Nat) : BS :=
  if h < s.pts.length then lv.foldl (letter F h (s.pts.getD h 0)) s else s

@[expose] def run (F : Nat → Nat → Nat) (lv : List Nat) (n r : Nat) : BS :=
  (List.range n).foldl (step F lv) ⟨[r], [0], [0]⟩

@[expose] def trans (F : Nat → Nat → Nat) (s : BS) (k : Nat) (x : Nat) : Nat :=
  if h : 0 < k ∧ s.par.getD k 0 < k then F (s.lab.getD k 0) (trans F s (s.par.getD k 0) x) else x
termination_by k
decreasing_by exact h.2

end BS

@[expose] def IsPermN (n : Nat) (f : Nat → Nat) : Prop :=
  (∀ x < n, f x < n) ∧ ∀ x < n, ∀ y < n, f x = f y → x = y

@[expose] def finv (n : Nat) (f : Nat → Nat) (y : Nat) : Nat :=
  ((List.range n).find? fun x => f x == y).getD 0

theorem isPermN_id (n : Nat) : IsPermN n fun x => x := by
  exact ⟨fun _ hx => hx, fun _ _ _ _ h => h⟩

theorem IsPermN.comp {n : Nat} {f g : Nat → Nat} (hf : IsPermN n f) (hg : IsPermN n g) :
    IsPermN n fun x => f (g x) := by
  exact ⟨fun x hx => hf.1 _ (hg.1 x hx),
    fun x hx y hy h => hg.2 x hx y hy (hf.2 _ (hg.1 x hx) _ (hg.1 y hy) h)⟩

theorem IsPermN.surj {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {y : Nat} (hy : y < n) :
    ∃ x < n, f x = y := by
  let g : Fin n → Fin n := fun x => ⟨f x.val, hf.1 x.val x.isLt⟩
  have hinj : Function.Injective g := fun a b e =>
    Fin.ext (hf.2 a.val a.isLt b.val b.isLt (congrArg Fin.val e))
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
  exact ⟨x.val, x.isLt, congrArg Fin.val hx⟩

theorem finv_spec {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {y : Nat} (hy : y < n) :
    finv n f y < n ∧ f (finv n f y) = y := by
  obtain ⟨x, hx, hfx⟩ := hf.surj hy
  have hsome : ((List.range n).find? fun x => f x == y).isSome = true :=
    List.find?_isSome.2 ⟨x, List.mem_range.2 hx, by simpa using hfx⟩
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hsome
  have h1 := List.find?_some hz
  have h2 := List.mem_range.1 (List.mem_of_find?_eq_some hz)
  have h3 : finv n f y = z := by simp [finv, hz]
  rw [h3]
  exact ⟨h2, by simpa using h1⟩

theorem finv_apply {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {x : Nat} (hx : x < n) :
    finv n f (f x) = x := by
  obtain ⟨h1, h2⟩ := finv_spec hf (hf.1 x hx)
  exact hf.2 _ h1 x hx h2

theorem finv_lt {n : Nat} (hn : 0 < n) (f : Nat → Nat) (y : Nat) : finv n f y < n := by
  unfold finv
  cases h : (List.range n).find? fun x => f x == y with
  | none => simpa using hn
  | some z => simpa using List.mem_range.1 (List.mem_of_find?_eq_some h)

theorem IsPermN.finv {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) : IsPermN n (finv n f) := by
  refine ⟨fun x hx => finv_lt (by omega) f x, fun x hx y hy h => ?_⟩
  have h1 := (finv_spec hf hx).2
  have h2 := (finv_spec hf hy).2
  rw [h] at h1
  exact h1.symm.trans h2

private theorem find?_congr_nat {p q : Nat → Bool} :
    ∀ {l : List Nat}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    have hl : l.find? p = l.find? q :=
      find?_congr_nat fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.find?_cons, ha, hl]

theorem finv_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x) (y : Nat) :
    finv n f y = finv n g y := by
  unfold finv
  rw [find?_congr_nat (q := fun x => g x == y)]
  intro x hx
  rw [h x (List.mem_range.1 hx)]

theorem finv_comp {n : Nat} {f g : Nat → Nat} (hf : IsPermN n f) (hg : IsPermN n g) {y : Nat}
    (hy : y < n) : finv n (fun x => f (g x)) y = finv n g (finv n f y) := by
  obtain ⟨ha, hfa⟩ := finv_spec hf hy
  obtain ⟨hb, hgb⟩ := finv_spec hg ha
  have h3 : finv n (fun x => f (g x)) (f (g (finv n g (finv n f y)))) = finv n g (finv n f y) :=
    finv_apply (hf.comp hg) hb
  rw [hgb, hfa] at h3
  exact h3

structure RunOK (n : Nat) (F : Nat → Nat → Nat) (lv : List Nat) (r : Nat) (s : BS) : Prop where
  len_par : s.par.length = s.pts.length
  len_lab : s.lab.length = s.pts.length
  pos : 0 < s.pts.length
  root : s.pts.getD 0 0 = r
  nodup : s.pts.Nodup
  lt : ∀ p ∈ s.pts, p < n
  le : s.pts.length ≤ n
  par0 : s.par.getD 0 0 = 0
  lab0 : s.lab.getD 0 0 = 0
  par_lt : ∀ k, 0 < k → k < s.pts.length → s.par.getD k 0 < k
  lab_mem : ∀ k, 0 < k → k < s.pts.length → s.lab.getD k 0 ∈ lv
  edge : ∀ k, 0 < k → k < s.pts.length →
    F (s.lab.getD k 0) (s.pts.getD (s.par.getD k 0) 0) = s.pts.getD k 0

variable {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat}

private theorem getD_append_left {l : List Nat} (l' : List Nat) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_self (l : List Nat) {i : Nat} (x : Nat) (h : l.length = i) :
    (l ++ [x]).getD i 0 = x := by
  simp [h]

private theorem getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem exists_getD {l : List Nat} {p : Nat} (h : p ∈ l) :
    ∃ i, ∃ _ : i < l.length, l.getD i 0 = p := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, e]⟩

private theorem length_le_of_nodup {l : List Nat} (hl : l.Nodup) (h : ∀ p ∈ l, p < n) :
    l.length ≤ n := by
  have := hl.length_le_of_subset (l₂ := List.range n) fun p hp => List.mem_range.2 (h p hp)
  simpa using this

private theorem letter_pts (F : Nat → Nat → Nat) (h p : Nat) (s : BS) (l : Nat) :
    ∃ u, (BS.letter F h p s l).pts = s.pts ++ u := by
  unfold BS.letter
  split
  · exact ⟨[], by simp⟩
  · exact ⟨[F l p], rfl⟩

private theorem letter_mem (F : Nat → Nat → Nat) (h p : Nat) (s : BS) (l : Nat) :
    F l p ∈ (BS.letter F h p s l).pts := by
  unfold BS.letter
  split
  · assumption
  · simp

private theorem letter_ok (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) {s : BS} (hs : RunOK n F lv r s)
    {h p : Nat} (hh : h < s.pts.length) (hp : s.pts.getD h 0 = p) {l : Nat} (hl : l ∈ lv) :
    RunOK n F lv r (BS.letter F h p s l) := by
  unfold BS.letter
  split
  · exact hs
  · rename_i hmem
    have hpn : p < n := hs.lt p (hp ▸ getD_mem hh)
    have hFp : F l p < n := hF l hl p hpn
    have hlenpar : s.par.length = s.pts.length := hs.len_par
    have hlenlab : s.lab.length = s.pts.length := hs.len_lab
    have hpos : 0 < s.pts.length := hs.pos
    have hnodup : (s.pts ++ [F l p]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hs.nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      rintro rfl
      exact hmem (hb ▸ ha)
    have hlt : ∀ q ∈ s.pts ++ [F l p], q < n := by
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hs.lt q hq
      · rw [List.mem_singleton] at hq
        exact hq ▸ hFp
    refine ⟨?_, ?_, ?_, ?_, hnodup, hlt, length_le_of_nodup hnodup hlt, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hlenpar]
    · simp [hlenlab]
    · simp
    · rw [getD_append_left _ hpos]
      exact hs.root
    · rw [getD_append_left _ (by omega : 0 < s.par.length)]
      exact hs.par0
    · rw [getD_append_left _ (by omega : 0 < s.lab.length)]
      exact hs.lab0
    · intro k hk0 hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < s.pts.length
      · rw [getD_append_left _ (by omega : k < s.par.length)]
        exact hs.par_lt k hk0 hlt
      · rw [getD_append_self _ _ (by omega : s.par.length = k)]
        omega
    · intro k hk0 hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < s.pts.length
      · rw [getD_append_left _ (by omega : k < s.lab.length)]
        exact hs.lab_mem k hk0 hlt
      · rw [getD_append_self _ _ (by omega : s.lab.length = k)]
        exact hl
    · intro k hk0 hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < s.pts.length
      · have hpk := hs.par_lt k hk0 hlt
        rw [getD_append_left _ (by omega : k < s.lab.length),
          getD_append_left _ (by omega : k < s.par.length),
          getD_append_left _ (by omega : s.par.getD k 0 < s.pts.length),
          getD_append_left _ hlt]
        exact hs.edge k hk0 hlt
      · rw [getD_append_self _ _ (by omega : s.lab.length = k),
          getD_append_self _ _ (by omega : s.par.length = k),
          getD_append_left _ hh, getD_append_self _ _ (by omega : s.pts.length = k), hp]

private theorem foldl_letter (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) {h p : Nat} :
    ∀ (lv' : List Nat), (∀ l ∈ lv', l ∈ lv) → ∀ (t : BS), RunOK n F lv r t →
      h < t.pts.length → t.pts.getD h 0 = p →
      RunOK n F lv r (lv'.foldl (BS.letter F h p) t) ∧
        (∃ u, (lv'.foldl (BS.letter F h p) t).pts = t.pts ++ u) ∧
        ∀ l ∈ lv', F l p ∈ (lv'.foldl (BS.letter F h p) t).pts := by
  intro lv'
  induction lv' with
  | nil =>
    intro _ t ht _ _
    exact ⟨ht, ⟨[], by simp⟩, by simp⟩
  | cons l lv' ih =>
    intro hsub t ht hh hp
    have hl : l ∈ lv := hsub l (List.mem_cons_self ..)
    have hsub' : ∀ l' ∈ lv', l' ∈ lv := fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')
    obtain ⟨u0, hu0⟩ := letter_pts F h p t l
    have hh' : h < (BS.letter F h p t l).pts.length := by
      rw [hu0]
      simp only [List.length_append]
      omega
    have hp' : (BS.letter F h p t l).pts.getD h 0 = p := by
      rw [hu0, getD_append_left _ hh, hp]
    obtain ⟨ho, ⟨u1, hu1⟩, hmem⟩ := ih hsub' _ (letter_ok hF ht hh hp hl) hh' hp'
    simp only [List.foldl_cons]
    refine ⟨ho, ⟨u0 ++ u1, by rw [hu1, hu0, List.append_assoc]⟩, ?_⟩
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · rw [hu1]
      exact List.mem_append.2 (Or.inl (letter_mem F h p t l'))
    · exact hmem l' hl'

private theorem step_ok (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) {s : BS} (hs : RunOK n F lv r s)
    (h : Nat) :
    RunOK n F lv r (BS.step F lv s h) ∧ (∃ u, (BS.step F lv s h).pts = s.pts ++ u) ∧
      (h < s.pts.length → ∀ l ∈ lv, F l (s.pts.getD h 0) ∈ (BS.step F lv s h).pts) ∧
      (¬ h < s.pts.length → BS.step F lv s h = s) := by
  unfold BS.step
  by_cases hh : h < s.pts.length
  · rw [if_pos hh]
    obtain ⟨ho, hu, hmem⟩ := foldl_letter hF (p := s.pts.getD h 0) lv (fun l hl => hl) s hs hh rfl
    exact ⟨ho, hu, fun _ => hmem, fun h' => absurd hh h'⟩
  · rw [if_neg hh]
    exact ⟨hs, ⟨[], by simp⟩, fun h' => absurd h' hh, fun _ => rfl⟩

private theorem init_ok (hr : r < n) : RunOK n F lv r ⟨[r], [0], [0]⟩ := by
  refine ⟨rfl, rfl, by simp, rfl, by simp, ?_, by simp only [List.length_singleton]; omega, rfl,
    rfl, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    exact hp ▸ hr
  · intro k hk0 hk
    simp at hk
    omega
  · intro k hk0 hk
    simp at hk
    omega
  · intro k hk0 hk
    simp at hk
    omega

private theorem run_aux (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hr : r < n) (j : Nat) :
    RunOK n F lv r ((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩) ∧
      ∀ i < j, i < ((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts.length →
        ∀ l ∈ lv, F l (((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts.getD i 0) ∈
          ((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts := by
  induction j with
  | zero =>
    exact ⟨init_ok hr, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ j ih =>
    obtain ⟨hok, hcl⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hok', ⟨u, hu⟩, hmem, hfix⟩ := step_ok hF hok j
    refine ⟨hok', ?_⟩
    intro i hi hi' l hl
    by_cases hj : j < ((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts.length
    · by_cases hij : i < j
      · have his : i < ((List.range j).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts.length := by
          omega
        rw [hu, getD_append_left _ his]
        exact List.mem_append.2 (Or.inl (hcl i hij his l hl))
      · have hij' : i = j := by omega
        subst hij'
        have key := hmem hj l hl
        rw [hu] at key ⊢
        rw [getD_append_left _ hj]
        exact key
    · rw [hfix hj] at hi' ⊢
      exact hcl i (by omega) hi' l hl

theorem run_ok (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hr : r < n) :
    RunOK n F lv r (BS.run F lv n r) := by
  exact (run_aux hF hr n).1

theorem run_closed (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hr : r < n) :
    ∀ p ∈ (BS.run F lv n r).pts, ∀ l ∈ lv, F l p ∈ (BS.run F lv n r).pts := by
  intro p hp l hl
  obtain ⟨hok, hcl⟩ := run_aux hF hr n
  obtain ⟨i, hi, rfl⟩ := exists_getD hp
  exact hcl i (lt_of_lt_of_le hi hok.le) hi l hl

theorem trans_root {s : BS} (hs : RunOK n F lv r s) {k : Nat} (hk : k < s.pts.length) :
    BS.trans F s k r = s.pts.getD k 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      rw [BS.trans, dif_pos ⟨hk0, hpar⟩, ih _ hpar (by omega), hs.edge k hk0 hk]
    · have hk0' : k = 0 := by omega
      subst hk0'
      rw [BS.trans, dif_neg (by simp), hs.root]

theorem trans_isPermN {s : BS} (hs : RunOK n F lv r s) (hF : ∀ l ∈ lv, IsPermN n (F l)) {k : Nat}
    (hk : k < s.pts.length) : IsPermN n (BS.trans F s k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      have heq : BS.trans F s k =
          fun x => F (s.lab.getD k 0) (BS.trans F s (s.par.getD k 0) x) := by
        funext x
        rw [BS.trans, dif_pos ⟨hk0, hpar⟩]
      rw [heq]
      exact (hF _ (hs.lab_mem k hk0 hk)).comp (ih _ hpar (by omega))
    · have hk0' : k = 0 := by omega
      subst hk0'
      have heq : BS.trans F s 0 = fun x => x := by
        funext x
        rw [BS.trans, dif_neg (by simp)]
      rw [heq]
      exact isPermN_id n

end CFSG.KS.PK

end
