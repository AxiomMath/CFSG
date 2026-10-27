module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksPred
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneWords

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.E6


set_option linter.unusedSectionVars false

theorem prod_reflection_eq_of_map_range {rt P : Array ℕ}
    (h : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    {w : List ℕ} (hw : ∀ b ∈ w, b < 240) {v : WeylGroup Tag.E8} (hP : PermOf8 P v)
    (hlist : (List.range 8).map (e8PlanePermOf rt w) = (List.range 8).map fun j => P.getD j 0) :
    (w.map fun b => rootReflection (e8Certificate.root b)).prod = v := by
  refine eq_of_smul_single_eq fun j => ?_
  have hj8 : (j : ℕ) < 8 := j.2
  have hj240 : (j : ℕ) < 240 := by omega
  have h1 : e8PlanePermOf rt w j = P.getD j 0 :=
    List.map_inj_left.1 hlist j (List.mem_range.2 hj8)
  obtain ⟨-, h2⟩ := e8PlanePermOf_spec h hw hj240
  obtain ⟨-, h3⟩ := hP j hj240
  rw [h1] at h2
  have h4 := h2.symm.trans h3
  rwa [e8Certificate_root_single] at h4

theorem testBit_foldl_or_shiftLeft (w : List ℕ) (acc n : ℕ) :
    (w.foldl (fun acc b => acc ||| 1 <<< b) acc).testBit n =
      (acc.testBit n || decide (n ∈ w)) := by
  induction w generalizing acc with
  | nil => simp
  | cons x w ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hn : n = x
    · subst hn
      simp
    · simp [hn, Ne.symm hn]

theorem testBit_e8PlaneWordMask (w : List ℕ) (n : ℕ) :
    (e8PlaneWordMask w).testBit n = decide (n ∈ w) := by
  rw [e8PlaneWordMask, testBit_foldl_or_shiftLeft, Nat.zero_testBit, Bool.false_or]

theorem root_mem_sigSet_of_mask {σ : ℕ} {w : List ℕ} (hw : ∀ b ∈ w, b < 240)
    (hm : σ &&& e8PlaneWordMask w = e8PlaneWordMask w) {b : ℕ} (hb : b ∈ w) :
    e8Certificate.root b ∈ sigSet σ := by
  have h1 : (e8PlaneWordMask w).testBit b = true := by
    rw [testBit_e8PlaneWordMask]
    exact decide_eq_true hb
  rw [← hm, Nat.testBit_and, Bool.and_eq_true] at h1
  exact mem_sigSet.2 ⟨b, hw b hb, h1.1, rfl⟩

theorem prod_mem_closure_of_mask {σ : ℕ} {w : List ℕ} (hw : ∀ b ∈ w, b < 240)
    (hm : σ &&& e8PlaneWordMask w = e8PlaneWordMask w) :
    (w.map fun b => rootReflection (e8Certificate.root b)).prod ∈
      Subgroup.closure (rootReflection '' sigSet σ) := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.subset_closure ⟨_, root_mem_sigSet_of_mask hw hm hb, rfl⟩

theorem mem_closure_of_any_mask {rt P : Array ℕ}
    (h : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    {v : WeylGroup Tag.E8} (hP : PermOf8 P v) {ws : List (List ℕ)}
    (hws : (ws.all fun w => w.all (fun b => decide (b < 240)) &&
      (List.range 8).map (e8PlanePermOf rt w) == (List.range 8).map fun j => P.getD j 0) = true)
    {σ : ℕ} (hany : ((ws.map e8PlaneWordMask).any fun m => σ &&& m == m) = true) :
    v ∈ Subgroup.closure (rootReflection '' sigSet σ) := by
  obtain ⟨m, hm, hσ⟩ := List.any_eq_true.1 hany
  obtain ⟨w, hwws, rfl⟩ := List.mem_map.1 hm
  have hw := List.all_eq_true.1 hws w hwws
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  have hw240 : ∀ b ∈ w, b < 240 := fun b hb => of_decide_eq_true (hw.1 b hb)
  rw [← prod_reflection_eq_of_map_range h hw240 hP hw.2]
  exact prod_mem_closure_of_mask hw240 (beq_iff_eq.1 hσ)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane
