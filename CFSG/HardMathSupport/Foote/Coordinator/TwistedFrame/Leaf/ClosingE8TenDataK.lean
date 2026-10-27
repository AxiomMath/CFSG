module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

@[expose] def e8tK_vec (l : List ℤ) : Fin Tag.E8.rank → ℤ := fun i => l.getD i.val 0

theorem e8tK_vec_ofFn (v : Fin Tag.E8.rank → ℤ) : e8tK_vec (List.ofFn v) = v := by
  funext i
  simp [e8tK_vec, List.getD_eq_getElem]

theorem e8tK_mem_iff {v : Fin Tag.E8.rank → ℤ} :
    v ∈ rootFinset Tag.E8 ↔ List.ofFn v ∈ Tag.E8.artifactRoots :=
  mem_rootFinset.trans isRoot_iff_mem_artifactRoots

theorem e8tK_forall {Q : (Fin Tag.E8.rank → ℤ) → Prop}
    (h : ∀ l ∈ Tag.E8.artifactRoots, Q (e8tK_vec l)) : ∀ v ∈ rootFinset Tag.E8, Q v := by
  intro v hv
  have := h _ (e8tK_mem_iff.1 hv)
  rwa [e8tK_vec_ofFn] at this

theorem e8tK_filter_iff {p : (Fin Tag.E8.rank → ℤ) → Bool} {L : List (List ℤ)}
    (h : (Tag.E8.artifactRoots.filter (fun l => p (e8tK_vec l)) == L) = true)
    {v : Fin Tag.E8.rank → ℤ} : (v ∈ rootFinset Tag.E8 ∧ p v = true) ↔ List.ofFn v ∈ L := by
  rw [← beq_iff_eq.1 h, List.mem_filter, e8tK_vec_ofFn, e8tK_mem_iff]

@[expose] def e8tK_deg1L : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1], [0, 1, 1, 2, 1, 1, 1, 1],
    [0, 1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 2, 2, 2, 1],
    [1, 0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1],
    [1, 1, 1, 2, 2, 1, 1, 1], [1, 1, 1, 2, 2, 2, 1, 1], [1, 1, 1, 2, 2, 2, 2, 1],
    [1, 1, 2, 2, 1, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1, 1], [1, 1, 2, 2, 2, 2, 1, 1],
    [1, 1, 2, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1, 1], [1, 1, 2, 3, 2, 2, 1, 1],
    [1, 1, 2, 3, 2, 2, 2, 1], [1, 1, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 3, 2, 2, 1],
    [1, 1, 2, 3, 3, 3, 2, 1], [1, 2, 2, 3, 2, 1, 1, 1], [1, 2, 2, 3, 2, 2, 1, 1],
    [1, 2, 2, 3, 2, 2, 2, 1], [1, 2, 2, 3, 3, 2, 1, 1], [1, 2, 2, 3, 3, 2, 2, 1],
    [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1, 1], [1, 2, 2, 4, 3, 2, 2, 1],
    [1, 2, 2, 4, 3, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1], [1, 2, 3, 4, 3, 2, 1, 1],
    [1, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1],
    [1, 2, 3, 5, 4, 3, 2, 1], [1, 3, 3, 5, 4, 3, 2, 1], [2, 2, 3, 4, 3, 2, 1, 1],
    [2, 2, 3, 4, 3, 2, 2, 1], [2, 2, 3, 4, 3, 3, 2, 1], [2, 2, 3, 4, 4, 3, 2, 1],
    [2, 2, 3, 5, 4, 3, 2, 1], [2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1],
    [2, 3, 4, 5, 4, 3, 2, 1], [2, 3, 4, 6, 4, 3, 2, 1], [2, 3, 4, 6, 5, 3, 2, 1],
    [2, 3, 4, 6, 5, 4, 2, 1], [2, 3, 4, 6, 5, 4, 3, 1]]

@[expose] def e8tK_mL : List (List ℤ) :=
  [[0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1], [0, 1, 1, 2, 1, 1, 1, 1],
    [0, 1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 2, 2, 2, 1],
    [1, 0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1],
    [1, 1, 1, 2, 2, 1, 1, 1], [1, 1, 1, 2, 2, 2, 1, 1], [1, 1, 1, 2, 2, 2, 2, 1],
    [1, 1, 2, 2, 1, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1, 1], [1, 1, 2, 2, 2, 2, 1, 1],
    [1, 1, 2, 2, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1, 1], [1, 1, 2, 3, 2, 2, 1, 1],
    [1, 1, 2, 3, 2, 2, 2, 1], [1, 1, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 3, 2, 2, 1],
    [1, 1, 2, 3, 3, 3, 2, 1], [1, 2, 2, 3, 2, 1, 1, 1], [1, 2, 2, 3, 2, 2, 1, 1],
    [1, 2, 2, 3, 2, 2, 2, 1], [1, 2, 2, 3, 3, 2, 1, 1], [1, 2, 2, 3, 3, 2, 2, 1],
    [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 4, 3, 2, 1, 1], [1, 2, 2, 4, 3, 2, 2, 1],
    [1, 2, 2, 4, 3, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1], [1, 2, 3, 4, 3, 2, 1, 1],
    [1, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1],
    [1, 2, 3, 5, 4, 3, 2, 1], [1, 3, 3, 5, 4, 3, 2, 1], [2, 2, 3, 4, 3, 2, 1, 1],
    [2, 2, 3, 4, 3, 2, 2, 1], [2, 2, 3, 4, 3, 3, 2, 1], [2, 2, 3, 4, 4, 3, 2, 1],
    [2, 2, 3, 5, 4, 3, 2, 1], [2, 2, 4, 5, 4, 3, 2, 1], [2, 3, 3, 5, 4, 3, 2, 1],
    [2, 3, 4, 5, 4, 3, 2, 1], [2, 3, 4, 6, 4, 3, 2, 1]]

@[expose] def e8tK_lxL : List (List ℤ) :=
  [[-1, -1, -1, -1, 0, 0, 0, 0], [-1, 0, -1, -1, 0, 0, 0, 0], [-1, 0, -1, 0, 0, 0, 0, 0],
    [-1, 0, 0, 0, 0, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0], [0, -1, 0, -1, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, -1, 0], [0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0],
    [0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0],
    [1, 0, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0]]

@[expose] def e8tK_tvL : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [0, 0, 0, 0, -1, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 0],
    [0, -1, -1, 1, 0, 0], [-1, -1, 1, 0, 0, 0], [0, 1, -1, 0, 0, 0], [-1, 1, 1, -1, 0, 0],
    [-1, 0, 0, 1, 0, 0], [-1, 0, 0, 0, -1, 0], [-1, 0, 0, 0, 1, -1], [-1, 0, 0, 0, 0, 1],
    [1, -1, 0, 0, 0, 0], [1, 1, 0, -1, 0, 0], [1, 0, -1, 1, 0, 0], [1, 0, -1, 0, -1, 0],
    [1, 0, -1, 0, 1, -1], [1, 0, -1, 0, 0, 1], [0, 0, 1, 0, 0, 0], [0, 0, 1, -1, -1, 0],
    [0, 0, 1, -1, 1, -1], [0, 0, 1, -1, 0, 1], [0, -1, 0, 1, -1, 0], [0, -1, 0, 1, 1, -1],
    [0, -1, 0, 1, 0, 1], [0, -1, 0, 0, 0, -1], [0, -1, 0, 0, -1, 1], [0, -1, 0, 0, 1, 0],
    [0, 1, 0, 0, -1, 0], [0, 1, 0, 0, 1, -1], [0, 1, 0, 0, 0, 1], [0, 1, 0, -1, 0, -1],
    [0, 1, 0, -1, -1, 1], [0, 1, 0, -1, 1, 0], [0, 0, -1, 1, 0, -1], [0, 0, -1, 1, -1, 1],
    [0, 0, -1, 1, 1, 0], [0, 0, -1, 0, 0, 0], [-1, 0, 1, 0, 0, -1], [-1, 0, 1, 0, -1, 1],
    [-1, 0, 1, 0, 1, 0], [-1, 0, 1, -1, 0, 0], [-1, -1, 0, 1, 0, 0], [-1, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 1], [1, 0, 0, 0, 1, 0], [1, 0, 0, -1, 0, 0],
    [1, -1, -1, 1, 0, 0], [0, -1, 1, 0, 0, 0], [1, 1, -1, 0, 0, 0], [0, 1, 1, -1, 0, 0],
    [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 1, -1], [0, 0, 0, 0, 0, 1]]

@[expose] def e8tK_nextP : List (List ℤ × List ℤ) :=
  [([0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]),
    ([0, 0, 0, 1, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1]),
    ([0, 0, 1, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1]),
    ([0, 1, 0, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1]),
    ([0, 1, 1, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1, 1]),
    ([0, 1, 1, 2, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1]),
    ([0, 1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 1, 1, 1]),
    ([0, 1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 2, 1, 1, 1]),
    ([0, 1, 1, 2, 2, 2, 2, 1], [0, 1, 1, 2, 2, 2, 1, 1]),
    ([1, 0, 1, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1, 1]),
    ([1, 1, 1, 1, 1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1]),
    ([1, 1, 1, 2, 1, 1, 1, 1], [0, 1, 1, 2, 1, 1, 1, 1]),
    ([1, 1, 1, 2, 2, 1, 1, 1], [0, 1, 1, 2, 2, 1, 1, 1]),
    ([1, 1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 2, 2, 1, 1]),
    ([1, 1, 1, 2, 2, 2, 2, 1], [0, 1, 1, 2, 2, 2, 2, 1]),
    ([1, 1, 2, 2, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1]),
    ([1, 1, 2, 2, 2, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1, 1]),
    ([1, 1, 2, 2, 2, 2, 1, 1], [1, 1, 1, 2, 2, 2, 1, 1]),
    ([1, 1, 2, 2, 2, 2, 2, 1], [1, 1, 1, 2, 2, 2, 2, 1]),
    ([1, 1, 2, 3, 2, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1, 1]),
    ([1, 1, 2, 3, 2, 2, 1, 1], [1, 1, 2, 2, 2, 2, 1, 1]),
    ([1, 1, 2, 3, 2, 2, 2, 1], [1, 1, 2, 2, 2, 2, 2, 1]),
    ([1, 1, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 3, 2, 1, 1]),
    ([1, 1, 2, 3, 3, 2, 2, 1], [1, 1, 2, 3, 3, 2, 1, 1]),
    ([1, 1, 2, 3, 3, 3, 2, 1], [1, 1, 2, 3, 3, 2, 2, 1]),
    ([1, 2, 2, 3, 2, 1, 1, 1], [1, 1, 2, 3, 2, 1, 1, 1]),
    ([1, 2, 2, 3, 2, 2, 1, 1], [1, 1, 2, 3, 2, 2, 1, 1]),
    ([1, 2, 2, 3, 2, 2, 2, 1], [1, 1, 2, 3, 2, 2, 2, 1]),
    ([1, 2, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 3, 2, 1, 1]),
    ([1, 2, 2, 3, 3, 2, 2, 1], [1, 1, 2, 3, 3, 2, 2, 1]),
    ([1, 2, 2, 3, 3, 3, 2, 1], [1, 1, 2, 3, 3, 3, 2, 1]),
    ([1, 2, 2, 4, 3, 2, 1, 1], [1, 2, 2, 3, 3, 2, 1, 1]),
    ([1, 2, 2, 4, 3, 2, 2, 1], [1, 2, 2, 3, 3, 2, 2, 1]),
    ([1, 2, 2, 4, 3, 3, 2, 1], [1, 2, 2, 3, 3, 3, 2, 1]),
    ([1, 2, 2, 4, 4, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1]),
    ([1, 2, 3, 4, 3, 2, 1, 1], [1, 2, 2, 4, 3, 2, 1, 1]),
    ([1, 2, 3, 4, 3, 2, 2, 1], [1, 2, 2, 4, 3, 2, 2, 1]),
    ([1, 2, 3, 4, 3, 3, 2, 1], [1, 2, 2, 4, 3, 3, 2, 1]),
    ([1, 2, 3, 4, 4, 3, 2, 1], [1, 2, 2, 4, 4, 3, 2, 1]),
    ([1, 2, 3, 5, 4, 3, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1]),
    ([1, 3, 3, 5, 4, 3, 2, 1], [1, 2, 3, 5, 4, 3, 2, 1]),
    ([2, 2, 3, 4, 3, 2, 1, 1], [1, 2, 3, 4, 3, 2, 1, 1]),
    ([2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 2, 2, 1]),
    ([2, 2, 3, 4, 3, 3, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1]),
    ([2, 2, 3, 4, 4, 3, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1]),
    ([2, 2, 3, 5, 4, 3, 2, 1], [1, 2, 3, 5, 4, 3, 2, 1]),
    ([2, 2, 4, 5, 4, 3, 2, 1], [2, 2, 3, 5, 4, 3, 2, 1]),
    ([2, 3, 3, 5, 4, 3, 2, 1], [1, 3, 3, 5, 4, 3, 2, 1]),
    ([2, 3, 4, 5, 4, 3, 2, 1], [2, 2, 4, 5, 4, 3, 2, 1]),
    ([2, 3, 4, 6, 4, 3, 2, 1], [2, 3, 4, 5, 4, 3, 2, 1])]

@[expose] def e8tK_nx (l : List ℤ) : List ℤ := (e8tK_nextP.lookup l).getD l

theorem e8tK_iter {D : (Fin Tag.E8.rank → ℤ) → Fin Tag.E8.rank → ℤ} {L : List (List ℤ)}
    {nx : List ℤ → List ℤ} (h : ∀ l ∈ L, nx l ∈ L ∧ D (e8tK_vec l) = e8tK_vec (nx l)) :
    ∀ n : ℕ, ∀ l ∈ L, D^[n] (e8tK_vec l) = e8tK_vec (nx^[n] l) := by
  intro n
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro l hl
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, (h l hl).2]
    exact ih _ (h l hl).1

theorem e8tK_deg1_chk : (Tag.E8.artifactRoots.filter (fun l => e8tK_vec l 7 == 1) ==
    e8tK_deg1L) = true := by
  decide +kernel

theorem e8tK_m_chk : (Tag.E8.artifactRoots.filter
    (fun l => e8tK_vec l 7 == 1 && e8tK_vec l 4 % 5 != 0) == e8tK_mL) = true := by
  decide +kernel

theorem e8tK_lx_chk : (Tag.E8.artifactRoots.filter
    (fun l => e8tK_vec l 7 == 0 && e8tK_vec l 4 % 5 == 0) == e8tK_lxL) = true := by
  decide +kernel

theorem e8tK_tvL_nodup : e8tK_tvL.Nodup := by decide +kernel

theorem e8tK_deg1_iff {v : Fin Tag.E8.rank → ℤ} : v ∈ deg1Roots ↔ List.ofFn v ∈ e8tK_deg1L := by
  rw [← e8tK_filter_iff (p := fun v => v 7 == 1) e8tK_deg1_chk, deg1Roots, Finset.mem_filter,
    beq_iff_eq]

theorem e8tK_m_iff {v : Fin Tag.E8.rank → ℤ} : v ∈ mRoots ↔ List.ofFn v ∈ e8tK_mL := by
  rw [← e8tK_filter_iff (p := fun v => v 7 == 1 && v 4 % 5 != 0) e8tK_m_chk, mRoots,
    Finset.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]

theorem e8tK_lx_iff {v : Fin Tag.E8.rank → ℤ} : v ∈ lxRoots ↔ List.ofFn v ∈ e8tK_lxL := by
  rw [← e8tK_filter_iff (p := fun v => v 7 == 0 && v 4 % 5 == 0) e8tK_lx_chk, lxRoots,
    Finset.mem_filter, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

theorem e8tK_mem_deg1 {v : Fin Tag.E8.rank → ℤ} (h : v 7 = 1) :
    v ∈ rootFinset Tag.E8 ↔ List.ofFn v ∈ e8tK_deg1L := by
  rw [← e8tK_filter_iff (p := fun v => v 7 == 1) e8tK_deg1_chk, beq_iff_eq]
  exact ⟨fun hv => ⟨hv, h⟩, fun hv => hv.1⟩

theorem e8tK_forall_of {S : Finset (Fin Tag.E8.rank → ℤ)} {L : List (List ℤ)}
    (hS : ∀ {v}, v ∈ S → List.ofFn v ∈ L) {Q : (Fin Tag.E8.rank → ℤ) → Prop}
    (h : ∀ l ∈ L, Q (e8tK_vec l)) : ∀ v ∈ S, Q v := by
  intro v hv
  have := h _ (hS hv)
  rwa [e8tK_vec_ofFn] at this

theorem e8tK_ofFn_vec {l : List ℤ} (hl : l ∈ Tag.E8.artifactRoots) :
    List.ofFn (e8tK_vec l) = l := by
  have h8 : l.length = Tag.E8.rank := length_of_mem_artifactRoots hl
  apply List.ext_getElem (by rw [List.length_ofFn, h8])
  intro n h1 h2
  rw [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ h2

theorem e8tK_sub_of_chk {p : List ℤ → Bool} {L : List (List ℤ)}
    (h : (Tag.E8.artifactRoots.filter p == L) = true) : ∀ l ∈ L, l ∈ Tag.E8.artifactRoots := by
  intro l hl
  rw [← beq_iff_eq.1 h] at hl
  exact (List.mem_filter.1 hl).1

theorem e8tK_ball_of {S : Finset (Fin Tag.E8.rank → ℤ)} {L : List (List ℤ)}
    (hS : ∀ {v}, v ∈ S ↔ List.ofFn v ∈ L) (hL : ∀ l ∈ L, l ∈ Tag.E8.artifactRoots)
    {Q : (Fin Tag.E8.rank → ℤ) → Prop} : (∀ v ∈ S, Q v) ↔ ∀ l ∈ L, Q (e8tK_vec l) := by
  constructor
  · intro h l hl
    refine h _ (hS.2 ?_)
    rw [e8tK_ofFn_vec (hL l hl)]
    exact hl
  · exact e8tK_forall_of hS.1

theorem e8tK_ball_root {Q : (Fin Tag.E8.rank → ℤ) → Prop} :
    (∀ v ∈ rootFinset Tag.E8, Q v) ↔ ∀ l ∈ Tag.E8.artifactRoots, Q (e8tK_vec l) :=
  e8tK_ball_of e8tK_mem_iff fun _ h => h

theorem e8tK_ball_deg1 {Q : (Fin Tag.E8.rank → ℤ) → Prop} :
    (∀ v ∈ deg1Roots, Q v) ↔ ∀ l ∈ e8tK_deg1L, Q (e8tK_vec l) :=
  e8tK_ball_of e8tK_deg1_iff (e8tK_sub_of_chk e8tK_deg1_chk)

theorem e8tK_ball_m {Q : (Fin Tag.E8.rank → ℤ) → Prop} :
    (∀ v ∈ mRoots, Q v) ↔ ∀ l ∈ e8tK_mL, Q (e8tK_vec l) :=
  e8tK_ball_of e8tK_m_iff (e8tK_sub_of_chk e8tK_m_chk)

theorem e8tK_ball_lx {Q : (Fin Tag.E8.rank → ℤ) → Prop} :
    (∀ v ∈ lxRoots, Q v) ↔ ∀ l ∈ e8tK_lxL, Q (e8tK_vec l) :=
  e8tK_ball_of e8tK_lx_iff (e8tK_sub_of_chk e8tK_lx_chk)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

end
