module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCData
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCE6Iso

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux

set_option linter.unusedSectionVars false


theorem addMonoidHom_apply_eq_sum_single {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup A] (F : (ι → ℤ) →+ A) (v : ι → ℤ) :
    F v = ∑ i, v i • F (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_zsmul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem wordW_inv_eq_reverse {τ : Tag} (l : List (Fin τ.rank)) :
    (wordW τ l)⁻¹ = wordW τ l.reverse := by
  induction l with
  | nil => simp [wordW]
  | cons a l ih =>
    have e1 : wordW τ (a :: l) = simple τ a * wordW τ l := by simp [wordW]
    have e2 : wordW τ [a] = simple τ a := by simp [wordW]
    rw [e1, _root_.mul_inv_rev, ih, simple_inv, List.reverse_cons, wordW_append, e2]

theorem r10_w_smul {w : WeylGroup Tag.E8}
    (hD : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -((SeitzExcOpenRest6.Aux.wc1 *
      SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u))
    (x : Fin Tag.E8.rank → ℤ) : w • x = r10NegC0 x := by
  rw [hD, ← e8c0_eq, e8c0, SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8]
  rfl

theorem r10_conj_smul (k : Fin 13) {w : WeylGroup Tag.E8}
    (hD : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -((SeitzExcOpenRest6.Aux.wc1 *
      SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u))
    (x : Fin Tag.E8.rank → ℤ) :
    ((wordW Tag.E8 (r10LineWord k))⁻¹ * w * wordW Tag.E8 (r10LineWord k)) • x = r10WAct k x := by
  rw [mul_smul, mul_smul, SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8, r10_w_smul hD,
    wordW_inv_eq_reverse, SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8]
  rfl

theorem r10_mem_parabolicRoots_iff {α : Fin Tag.E8.rank → ℤ} :
    α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8) ↔ IsRoot Tag.E8 α ∧ α 6 = 0 ∧ α 7 = 0 := by
  rw [e6Nodes_eq_e6Set]
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, h 6 (show ¬ ((6 : Fin Tag.E8.rank).val < Tag.E6.rank) by decide),
      h 7 (show ¬ ((7 : Fin Tag.E8.rank).val < Tag.E6.rank) by decide)⟩
  · rintro ⟨hr, h6, h7⟩
    refine ⟨hr, fun i hi => ?_⟩
    obtain ⟨i, hi8⟩ := i
    have hi8' : i < 8 := hi8
    have hi6 : ¬ i < 6 := hi
    have : i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl
    · exact h6
    · exact h7

theorem r10_u_mem (k : Fin 13) :
    wordW Tag.E8 (r10UWord k) ∈ parabolicWeylGroup Tag.E8 (e6Nodes Tag.E8) := by
  rw [e6Nodes_eq_e6Set]
  exact wordW_mem_parabolicWeylGroup _ fun i hi =>
    (show ∀ k : Fin 13, ∀ i ∈ r10UWord k, i.val < Tag.E6.rank by decide) k i hi

theorem lt_six_of_ne_zero {α : Fin Tag.E8.rank → ℤ} (h6 : α 6 = 0) (h7 : α 7 = 0)
    {i : Fin Tag.E8.rank} (hi : α i ≠ 0) : i.val < 6 := by
  obtain ⟨i, hi8⟩ := i
  have hi8' : i < 8 := hi8
  show i < 6
  by_contra hge
  have : i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl
  · exact hi h6
  · exact hi h7

theorem r10_act_E6 (k : Fin 13) {w : WeylGroup Tag.E8}
    (hD : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -((SeitzExcOpenRest6.Aux.wc1 *
      SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u)) :
    ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      ((wordW Tag.E8 (r10LineWord k))⁻¹ * w * wordW Tag.E8 (r10LineWord k)) • α =
        wordW Tag.E8 (r10UWord k) • ((-1 : ℤ) • α) := by
  intro α hα
  obtain ⟨-, h6, h7⟩ := r10_mem_parabolicRoots_iff.1 hα
  set x := (wordW Tag.E8 (r10LineWord k))⁻¹ * w * wordW Tag.E8 (r10LineWord k) with hx
  let F : (Fin Tag.E8.rank → ℤ) →+ (Fin Tag.E8.rank → ℤ) :=
    AddMonoidHom.mk' (fun v => x • v) fun a b => smul_add x a b
  let G : (Fin Tag.E8.rank → ℤ) →+ (Fin Tag.E8.rank → ℤ) :=
    AddMonoidHom.mk' (fun v => wordW Tag.E8 (r10UWord k) • ((-1 : ℤ) • v)) fun a b => by
      rw [smul_add, smul_add]
  have hF : ∀ v, F v = x • v := fun v => rfl
  have hG : ∀ v, G v = wordW Tag.E8 (r10UWord k) • ((-1 : ℤ) • v) := fun v => rfl
  have hbasis : ∀ i : Fin Tag.E8.rank, α i ≠ 0 → F (Pi.single i 1) = G (Pi.single i 1) := by
    intro i hi
    rw [hF, hG, hx, r10_conj_smul k hD, r10_check_E6_basis k i (lt_six_of_ne_zero h6 h7 hi),
      SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8, neg_one_zsmul]
  rw [← hF, ← hG, addMonoidHom_apply_eq_sum_single F, addMonoidHom_apply_eq_sum_single G]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : α i = 0
  · rw [h, zero_smul, zero_smul]
  · rw [hbasis i h]

theorem r10_form_sum (k : Fin 13) (μ : Fin Tag.E8.rank → ℤ) :
    (∑ i, r10LineForm k i * ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) : ZMod 3)) =
      ∑ i, r10FormCol k i * ((μ i : ℤ) : ZMod 3) := by
  have hlin : ∀ ν, (r10LineWord k).foldr (reflect Tag.E8) ν = wordW Tag.E8 (r10LineWord k) • ν :=
    fun ν => (SeitzExcOpenRest6.Aux.wordW_smul_foldr_E8 _ ν).symm
  let F : (Fin Tag.E8.rank → ℤ) →+ ZMod 3 :=
    { toFun := fun ν => ∑ i, r10LineForm k i *
        ((((wordW Tag.E8 (r10LineWord k) • ν) i : ℤ)) : ZMod 3)
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [smul_add, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib] }
  have h1 : F μ = ∑ i, μ i • F (Pi.single i 1) := addMonoidHom_apply_eq_sum_single F μ
  have hFv : ∀ ν, F ν = ∑ i, r10LineForm k i *
      ((((r10LineWord k).foldr (reflect Tag.E8) ν) i : ℤ) : ZMod 3) := fun ν => by
    rw [hlin]
    rfl
  rw [← hFv, h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hFv, r10_check_cols k i, zsmul_eq_mul, mul_comm]

theorem r10_kernel (k : Fin 13) {μ : Fin Tag.E8.rank → ℤ} (hμ : IsRoot Tag.E8 μ) :
    (∑ i, r10LineForm k i * ((((r10LineWord k).foldr (reflect Tag.E8) μ) i : ℤ) : ZMod 3)) = 0 ↔
      (μ ∈ r10A2pList ∨ (μ 6 = 0 ∧ μ 7 = 0)) := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hμ
  rw [r10_form_sum]
  exact r10_check_kernel_cols k m

@[expose] def r10A2pSet : Set (Fin Tag.E8.rank → ℤ) := {β | β ∈ r10A2pList}

theorem r10_A2p_root : ∀ β ∈ r10A2pSet, IsRoot Tag.E8 β := by
  intro β hβ
  obtain ⟨m, hm⟩ := r10_check_A2p_root β hβ
  exact isRoot_iff_exists_e8RootVec.2 ⟨m, hm⟩

theorem r10_A2p_stable (k : Fin 13) {w : WeylGroup Tag.E8}
    (hD : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -((SeitzExcOpenRest6.Aux.wc1 *
      SeitzExcOpenRest6.Aux.wc2 * SeitzExcOpenRest6.Aux.wc3) • u)) :
    ∀ β ∈ r10A2pSet,
      ((wordW Tag.E8 (r10LineWord k))⁻¹ * w * wordW Tag.E8 (r10LineWord k)) • β ∈ r10A2pSet := by
  intro β hβ
  rw [r10_conj_smul k hD]
  exact r10_check_A2p k β hβ

theorem r10_A2p_orth : ∀ α ∈ r10A2pSet, ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
    α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0 := by
  intro α hα β hβ
  obtain ⟨hr, h6, h7⟩ := r10_mem_parabolicRoots_iff.1 hβ
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
  exact r10_check_orth α hα m h6 h7

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
