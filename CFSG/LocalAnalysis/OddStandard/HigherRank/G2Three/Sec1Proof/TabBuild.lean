module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps1
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

structure GenData where
  n : ℕ
  ng : ℕ
  rt : Array (Array ℕ)
  par : Array (ℕ × ℕ)

namespace GenData

@[expose] def rtAt (G : GenData) (i s : ℕ) : ℕ := (G.rt.getD i #[]).getD s 0

@[expose] def parAt (G : GenData) (j : ℕ) : ℕ × ℕ := G.par.getD (j - 1) (0, 0)

@[expose] def walk {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) : Array α :=
  (List.range G.n).foldl (fun acc j =>
    if j == 0 then acc.push one else acc.push (step (acc.getD (G.parAt j).1 one) (G.parAt j).2))
    #[]

private def walkFold {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    (k : ℕ) : Array α :=
  (List.range k).foldl (fun acc j =>
    if j == 0 then acc.push one
    else acc.push (step (acc.getD (G.parAt j).1 one) (G.parAt j).2)) #[]

private def walkVal {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    (j : ℕ) : α :=
  if j == 0 then one
  else step ((walkFold G one step j).getD (G.parAt j).1 one) (G.parAt j).2

private theorem walk_eq_walkFold {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) :
    G.walk one step = walkFold G one step G.n := rfl

private theorem walkFold_succ {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) (k : ℕ) :
    walkFold G one step (k + 1) = (walkFold G one step k).push (walkVal G one step k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k
    simp [walkFold, walkVal]
  · have hkne : ¬ k = 0 := Nat.pos_iff_ne_zero.mp hk
    simp [walkFold, walkVal, List.range_succ, List.foldl_append, hkne]

private theorem walkFold_size {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) (k : ℕ) :
    (walkFold G one step k).size = k := by
  induction k with
  | zero => simp [walkFold]
  | succ k ih => rw [walkFold_succ, Array.size_push, ih]

private theorem walkFold_getElem?_succ {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    (k p : ℕ) (hp : p < k) :
    (walkFold G one step (k + 1))[p]? = (walkFold G one step k)[p]? := by
  rw [walkFold_succ]
  have hp' : p < (walkFold G one step k).size := by rw [walkFold_size G one step k]; exact hp
  rw [Array.getElem?_push_lt hp', Array.getElem?_eq_getElem hp']

private theorem walkFold_getD_succ {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    (k p : ℕ) (hp : p < k) :
    (walkFold G one step (k + 1)).getD p one = (walkFold G one step k).getD p one := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    walkFold_getElem?_succ G one step k p hp]

private theorem walkFold_getD_le {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    {k k' : ℕ} (hk : k ≤ k') {p : ℕ} (hp : p < k) :
    (walkFold G one step k').getD p one = (walkFold G one step k).getD p one := by
  refine Nat.le_induction (P := fun n _ => (walkFold G one step n).getD p one =
    (walkFold G one step k).getD p one) rfl ?_ k' hk
  intro n hmn ih
  rw [walkFold_getD_succ G one step n p (lt_of_lt_of_le hp hmn), ih]

private theorem walkFold_getD_lt {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α)
    {j k : ℕ} (hj : j < k) :
    (walkFold G one step k).getD j one = walkVal G one step j := by
  have h1 : (walkFold G one step k).getD j one =
      (walkFold G one step (j + 1)).getD j one :=
    walkFold_getD_le G one step (Nat.succ_le_of_lt hj) (Nat.lt_succ_self j)
  rw [h1, walkFold_succ, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    if_pos (show j = (walkFold G one step j).size by rw [walkFold_size G one step j])]
  rfl

theorem size_walk {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) :
    (G.walk one step).size = G.n := by
  rw [walk_eq_walkFold]
  exact walkFold_size G one step G.n

theorem walk_zero {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) (hn : 0 < G.n) :
    (G.walk one step).getD 0 one = one := by
  rw [walk_eq_walkFold, walkFold_getD_lt G one step hn]
  simp [walkVal]

theorem walk_succ {α : Type*} (G : GenData) (one : α) (step : α → ℕ → α) {j : ℕ} (hj : j < G.n)
    (h0 : 0 < j) (hp : (G.parAt j).1 < j) :
    (G.walk one step).getD j one =
      step ((G.walk one step).getD (G.parAt j).1 one) (G.parAt j).2 := by
  rw [walk_eq_walkFold, walkFold_getD_lt G one step hj]
  simp only [walkVal]
  rw [if_neg (by simp [show j ≠ 0 by omega])]
  rw [← walkFold_getD_le G one step (Nat.le_of_lt hj) hp]

@[expose] def rowOf (G : GenData) (i : ℕ) : Array ℕ := G.walk i G.rtAt

@[expose] def rowsOf (G : GenData) : Array (Array ℕ) := (Array.range G.n).map G.rowOf

@[expose] def invsOf (G : GenData) (rs : Array (Array ℕ)) : Array ℕ :=
  (Array.range G.n).map fun i =>
    ((List.range G.n).find? fun j => (rs.getD i #[]).getD j 0 == 0).getD 0

@[expose] def tab (G : GenData) : TabData :=
  let rs := G.rowsOf
  ⟨G.n, rs, G.invsOf rs⟩

@[expose] def parOK (G : GenData) : Bool :=
  G.par.size + 1 == G.n &&
    (List.range (G.n - 1)).all fun j =>
      (G.parAt (j + 1)).1 < j + 1 && (G.parAt (j + 1)).2 < G.ng &&
        G.rtAt (G.parAt (j + 1)).1 (G.parAt (j + 1)).2 == j + 1

@[expose] def rtOK (G : GenData) : Bool :=
  G.rt.size == G.n && 0 < G.n && 0 < G.ng &&
    (List.range G.n).all (fun i => (G.rt.getD i #[]).size == G.ng &&
      (List.range G.ng).all fun s => G.rtAt i s < G.n) &&
    (List.range G.ng).all fun s => G.rtAt 0 s == s + 1

@[expose] def invOK (G : GenData) : Bool :=
  let T := G.tab
  (List.range G.n).all fun i => T.inv i < G.n && T.mul i (T.inv i) == 0

@[expose] def ok (G : GenData) : Bool := G.rtOK && G.parOK && G.invOK

theorem tab_n (G : GenData) : G.tab.n = G.n := rfl

theorem parOK_spec {G : GenData} (h : G.parOK = true) {j : ℕ} (hj : j < G.n) (h0 : 0 < j) :
    (G.parAt j).1 < j ∧ (G.parAt j).2 < G.ng ∧ G.rtAt (G.parAt j).1 (G.parAt j).2 = j := by
  simp only [parOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨-, hcheck⟩ := h
  have hjn : j - 1 < G.n - 1 := by omega
  have h' := hcheck (j - 1) hjn
  rw [Nat.sub_add_cancel h0] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem rtOK_spec {G : GenData} (h : G.rtOK = true) :
    0 < G.n ∧ 0 < G.ng ∧ (∀ i < G.n, ∀ s < G.ng, G.rtAt i s < G.n) ∧
      ∀ s < G.ng, G.rtAt 0 s = s + 1 := by
  simp only [rtOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hnpos⟩, hngpos⟩, hshape⟩, hfirst⟩ := h
  exact ⟨hnpos, hngpos, fun i hi s hs => (hshape i hi).2 s hs, hfirst⟩

theorem invOK_spec {G : GenData} (h : G.invOK = true) :
    ∀ i < G.n, G.tab.inv i < G.n ∧ G.tab.mul i (G.tab.inv i) = 0 := by
  simp only [invOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact fun i hi => h i hi

theorem tab_mul {G : GenData} {i j : ℕ} (hi : i < G.n) (hj : j < G.n) :
    G.tab.mul i j = (G.walk i G.rtAt).getD j i := by
  have hrow : G.rowsOf.getD i #[] = G.rowOf i := by
    simp [rowsOf, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hi]
  have hsize : j < (G.walk i G.rtAt).size := by rw [size_walk G i G.rtAt]; exact hj
  have h1 : (G.walk i G.rtAt).getD j 0 = (G.walk i G.rtAt).getD j i := by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hsize]
    rfl
  have hrowdef : G.rowOf i = G.walk i G.rtAt := rfl
  simpa only [TabData.mul, tab, hrow, hrowdef] using h1

end GenData

open GenData

variable {Γ : Type*} [Group Γ]

theorem realizes_tab {G : GenData} (hok : G.ok = true) {elt : ℕ → Γ} {g : ℕ → Γ}
    (h0 : elt 0 = 1) (hstep : ∀ i < G.n, ∀ s < G.ng, elt (G.rtAt i s) = elt i * g s)
    (hinj : ∀ i < G.n, ∀ j < G.n, elt i = elt j → i = j) : Realizes G.tab elt := by
  rw [ok, Bool.and_eq_true, Bool.and_eq_true] at hok
  obtain ⟨⟨hrt, hpar⟩, hinv⟩ := hok
  obtain ⟨hnpos, -, hrtlt, -⟩ := rtOK_spec hrt
  have key : ∀ j < G.n, ∀ i < G.n,
      (G.walk i G.rtAt).getD j i < G.n ∧
        elt ((G.walk i G.rtAt).getD j i) = elt i * elt j := by
    intro j
    refine Nat.strong_induction_on j ?_
    intro j ih hj i hi
    by_cases hj0 : j = 0
    · subst j
      have hw : (G.walk i G.rtAt).getD 0 i = i := walk_zero G i G.rtAt hnpos
      rw [hw]
      exact ⟨hi, by rw [h0, mul_one]⟩
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      obtain ⟨hp1, hp2, hp3⟩ := parOK_spec hpar hj hjpos
      have hp_lt : (G.parAt j).1 < G.n := lt_trans hp1 hj
      have hws : (G.walk i G.rtAt).getD j i =
          G.rtAt ((G.walk i G.rtAt).getD (G.parAt j).1 i) (G.parAt j).2 :=
        walk_succ G i G.rtAt hj hjpos hp1
      obtain ⟨ihlt, ihelt⟩ := ih (G.parAt j).1 hp1 hp_lt i hi
      have hjelt : elt j = elt (G.parAt j).1 * g (G.parAt j).2 :=
        calc elt j = elt (G.rtAt (G.parAt j).1 (G.parAt j).2) := (congrArg elt hp3).symm
          _ = elt (G.parAt j).1 * g (G.parAt j).2 := hstep _ hp_lt _ hp2
      rw [hws]
      exact ⟨hrtlt _ ihlt _ hp2,
        by rw [hstep _ ihlt _ hp2, ihelt, hjelt, mul_assoc]⟩
  refine ⟨h0, hnpos, ?_, ?_, ?_, ?_, hinj⟩
  · intro i hi j hj
    rw [tab_mul hi hj]
    exact (key j hj i hi).1
  · intro i hi j hj
    rw [tab_mul hi hj]
    exact (key j hj i hi).2
  · intro i hi
    exact (invOK_spec hinv i hi).1
  · intro i hi
    obtain ⟨h1, h2⟩ := invOK_spec hinv i hi
    have hk := (key (G.tab.inv i) h1 i hi).2
    rw [← tab_mul hi h1] at hk
    rw [h2, h0] at hk
    exact eq_inv_of_mul_eq_one_right hk.symm

theorem rep_tab_closure [Finite Γ] {G : GenData} (hok : G.ok = true) {elt : ℕ → Γ} {g : ℕ → Γ}
    (hR : Realizes G.tab elt)
    (hstep : ∀ i < G.n, ∀ s < G.ng, elt (G.rtAt i s) = elt i * g s) :
    Rep G.tab elt (topB G.tab) (Subgroup.closure (g '' {s | s < G.ng}) : Set Γ) := by
  rw [ok, Bool.and_eq_true, Bool.and_eq_true] at hok
  obtain ⟨⟨hrt, hpar⟩, -⟩ := hok
  obtain ⟨hnpos, -, hrtlt, -⟩ := rtOK_spec hrt
  have hmem : ∀ i < G.n, elt i ∈ Subgroup.closure (g '' {s | s < G.ng}) := by
    intro i
    refine Nat.strong_induction_on i ?_
    intro i ih hi
    by_cases hi0 : i = 0
    · subst i
      rw [hR.zero]
      exact Subgroup.one_mem _
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hp1, hp2, hp3⟩ := parOK_spec hpar hi hipos
      have hp_lt : (G.parAt i).1 < G.n := lt_trans hp1 hi
      have hiel : elt i = elt (G.parAt i).1 * g (G.parAt i).2 :=
        calc elt i = elt (G.rtAt (G.parAt i).1 (G.parAt i).2) := (congrArg elt hp3).symm
          _ = elt (G.parAt i).1 * g (G.parAt i).2 := hstep _ hp_lt _ hp2
      rw [hiel]
      exact Subgroup.mul_mem _
        (ih _ hp1 hp_lt) (Subgroup.subset_closure ⟨(G.parAt i).2, hp2, rfl⟩)
  let Tsub : Subgroup Γ :=
    { carrier := {x | ∃ i < G.tab.n, elt i = x}
      mul_mem' := fun {a b} ha hb => by
        change ∃ i < G.tab.n, elt i = a at ha
        change ∃ i < G.tab.n, elt i = b at hb
        obtain ⟨i, hi, rfl⟩ := ha
        obtain ⟨j, hj, rfl⟩ := hb
        exact ⟨G.tab.mul i j, hR.mul_lt i hi j hj, hR.elt_mul i hi j hj⟩
      one_mem' := ⟨0, hR.zero_lt, hR.zero⟩
      inv_mem' := fun {a} ha => by
        change ∃ i < G.tab.n, elt i = a at ha
        obtain ⟨i, hi, rfl⟩ := ha
        exact ⟨G.tab.inv i, hR.inv_lt i hi, hR.elt_inv i hi⟩ }
  have hTS : (g '' {s | s < G.ng}) ⊆ Tsub := by
    rintro y ⟨s, hs, rfl⟩
    change ∃ i < G.tab.n, elt i = g s
    exact ⟨G.rtAt 0 s, hrtlt 0 hnpos s hs,
      by rw [hstep 0 hnpos s hs, hR.zero, one_mul]⟩
  have hTclosure : Subgroup.closure (g '' {s | s < G.ng}) ≤ Tsub :=
    (Subgroup.closure_le (K := Tsub)).mpr hTS
  constructor
  · intro i hi
    rw [topB, BSet.has_ofFn (fun _ => true) hi]
    exact ⟨fun _ => hmem i hi, fun _ => rfl⟩
  · intro x hx
    have hxT : x ∈ Tsub := hTclosure hx
    change ∃ i < G.tab.n, elt i = x at hxT
    obtain ⟨i, hi, hix⟩ := hxT
    exact ⟨i, hi, hix⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
