module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryBruhat

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.SpecialLinear
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

section Fix

theorem borel_le_stabilizer_flag {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ r) :
    borel r K ≤
      MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K i) :=
  fun _ hb => mem_stabilizer_iff_map.2 ((mem_borel.1 hb).2 i hi1 hi2)

theorem torusElt_smul_coordSpan (d : Fin r → Kˣ) (S : Set (Fin r ⊕ Fin r)) :
    torusElt r K d • coordSpan K S = coordSpan K S := by
  rw [smul_coordSpan_eq_iff (μ := fun x => ((Sum.elim d d⁻¹ x : Kˣ) : K)) (fun x => Units.ne_zero _)
    (by rw [autMat_torusElt, signedPerm_one]), Equiv.Perm.coe_one, Set.image_id]

theorem borel_le_stabilizer_Xstar (hr0 : 0 < r) :
    borel r K ≤
      MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Xstar r K hr0) := by
  intro b hb
  obtain ⟨t, ⟨-, d, rfl⟩, u, hu, rfl⟩ := exists_torus_mul_unipotent hb
  refine mul_mem (MulAction.mem_stabilizer_iff.2 ?_) (mem_stabilizer_iff_map.2 ?_)
  · rw [Xstar_eq_coordSpan]
    exact torusElt_smul_coordSpan d _
  · rw [unipotent_eq_posUnip] at hu
    exact map_Xstar_of_mem_posUnip hr0 hu

end Fix

section Generation

variable (hr : 3 ≤ r)
include hr

theorem eq_one_of_weylLength_eq_zero {w : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)} (hw : w ∈ weylGroup r)
    (h0 : weylLength r w = 0) : w = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_simpleRoot_neg hr hw hne
  have := weylLength_pos (by omega) hw hi
  omega

theorem eq_closure_of_borel_le {M : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))}
    (hMG : M ≤ orthElementaryGroup (quadPlus r K)) (hBM : borel r K ≤ M) :
    M = Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) ∪
      weylElt r K '' {i | weylElt r K i ∈ M}) := by
  have hr2 : 2 ≤ r := by omega
  set H := Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] _)) ∪
    weylElt r K '' {i | weylElt r K i ∈ M}) with hHdef
  have hBH : borel r K ≤ H := fun b hb => Subgroup.subset_closure (Or.inl hb)
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  ·
    have key : ∀ ℓ : ℕ, ∀ n (hn : n ∈ torusWeyl r K), n ∈ M →
        weylLength r ((torusWeylNu r K hr2 ⟨n, hn⟩ : weylGroup r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ℓ → n ∈ H := by
      intro ℓ
      induction ℓ with
      | zero =>
        intro n hn _ hℓ
        have h1 := eq_one_of_weylLength_eq_zero hr (torusWeylNu r K hr2 ⟨n, hn⟩).2 hℓ
        have hker : (⟨n, hn⟩ : torusWeyl r K) ∈ (torusWeylNu r K hr2).ker :=
          MonoidHom.mem_ker.2 (Subtype.ext h1)
        rw [torusWeylNu_ker hr2, Subgroup.mem_subgroupOf] at hker
        exact hBH (torus_le_borel hker)
      | succ ℓ ih =>
        intro n hn hnM hℓ
        set w := ((torusWeylNu r K hr2 ⟨n, hn⟩ : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
          with hw
        have hwW : w ∈ weylGroup r := (torusWeylNu r K hr2 ⟨n, hn⟩).2
        have hne : w ≠ 1 := by
          rintro h1
          rw [h1] at hℓ
          have : weylLength r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = 0 := by
            have hempty : inversionSet r (1 : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ∅ := by
              ext β
              simp only [inversionSet, LinearEquiv.coe_one, id_eq, Set.mem_ofPred_eq,
                Set.mem_empty_iff_false, iff_false, not_and]
              intro hβ hβ'
              exact (mem_posRoots_or_neg_mem_posRoots (posRoots_subset_roots hβ)).2 ⟨hβ, hβ'⟩
            rw [weylLength, hempty, Set.ncard_empty]
          omega
        obtain ⟨i, hi⟩ := exists_simpleRoot_neg hr hwW hne
        have hα := simpleRoot_mem_posRoots hr2 i
        have hXα : rootSubgroup r K (simpleRoot r i) ≤ M :=
          le_trans (le_trans (rootSubgroup_le_unipotent hα) unipotent_le_borel) hBM
        have hXβ : rootSubgroup r K (-(w⁻¹ (simpleRoot r i))) ≤ M :=
          le_trans (le_trans (rootSubgroup_le_unipotent hi) unipotent_le_borel) hBM
        have hmap := map_conj_rootSubgroup_torusWeyl hr2 ⟨n, hn⟩ (posRoots_subset_roots hi)
        have hww : w (w⁻¹ (simpleRoot r i)) = simpleRoot r i := by
          rw [LinearEquiv.coe_inv]
          exact LinearEquiv.apply_symm_apply _ _
        rw [← hw, map_neg, hww] at hmap
        have hXneg : rootSubgroup r K (-simpleRoot r i) ≤ M := by
          rw [← hmap]
          rintro _ ⟨y, hy, rfl⟩
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact mul_mem (mul_mem hnM (hXβ hy)) (inv_mem hnM)
        have hniM : weylElt r K i ∈ M :=
          mul_mem (mul_mem (hXα (rootElt_mem_rootSubgroup _ _))
            (hXneg (rootElt_mem_rootSubgroup _ _))) (hXα (rootElt_mem_rootSubgroup _ _))
        have hniH : weylElt r K i ∈ H := Subgroup.subset_closure (Or.inr ⟨i, hniM, rfl⟩)
        have hn' : (weylElt r K i)⁻¹ * n ∈ torusWeyl r K :=
          mul_mem (inv_mem (weylElt_mem_torusWeyl i)) hn
        have hν : ((torusWeylNu r K hr2 ⟨_, hn'⟩ : weylGroup r) :
            (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleRefl r i * w := by
          have he : (⟨(weylElt r K i)⁻¹ * n, hn'⟩ : torusWeyl r K) =
              (⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : torusWeyl r K)⁻¹ * ⟨n, hn⟩ := rfl
          rw [he, map_mul, map_inv, torusWeylNu_weylElt hr2 i, Subgroup.coe_mul,
            Subgroup.coe_inv]
          congr 1
          rw [inv_eq_iff_mul_eq_one, simpleRefl_mul_self hr2]
        have hlen := weylLength_simpleRefl_mul hr2 hwW hi
        rw [← hν, hℓ, Nat.add_sub_cancel] at hlen
        have := ih _ hn' (mul_mem (inv_mem hniM) hnM) hlen
        have he : n = weylElt r K i * ((weylElt r K i)⁻¹ * n) := by group
        rw [he]
        exact mul_mem hniH this
    obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ :=
      (orthogonal_geometry_split_Bruhat_coverage hr g).1 (hMG hg)
    have hnM : n ∈ M := by
      have : n = b₁⁻¹ * (b₁ * n * b₂) * b₂⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (hBM h1)) hg) (inv_mem (hBM h2))
    exact mul_mem (mul_mem (hBH h1) (key _ n hn hnM rfl)) (hBH h2)
  · rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact hBM hb
    · exact hi

theorem eq_stabilizer_of_isMax {M : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))}
    (hMG : M ≤ orthElementaryGroup (quadPlus r K)) (hBM : borel r K ≤ M)
    (hne : M ≠ orthElementaryGroup (quadPlus r K))
    (hmax : ∀ M' : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)), M ≤ M' →
      M' ≤ orthElementaryGroup (quadPlus r K) → M' = M ∨ M' = orthElementaryGroup (quadPlus r K)) :
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ r - 2 ∧ M = orthElementaryGroup (quadPlus r K) ⊓
      MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K i)) ∨
    M = orthElementaryGroup (quadPlus r K) ⊓
      MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
        (Xstar r K (by omega)) ∨
    M = orthElementaryGroup (quadPlus r K) ⊓
      MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K r) := by
  have hgen := eq_closure_of_borel_le hr hMG hBM
  obtain ⟨i, hi⟩ : ∃ i, weylElt r K i ∉ M := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    refine le_antisymm hMG ?_
    rw [orthogonal_geometry_split_Borel_Weyl_generation hr, Subgroup.closure_le]
    rintro _ (hb | ⟨j, rfl⟩)
    · exact hBM hb
    · exact h j
  have hconcl : ∀ V : Submodule K (Fin r ⊕ Fin r → K),
      borel r K ≤ MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] _) V →
      (∀ j, j ≠ i → weylElt r K j • V = V) → weylElt r K i • V ≠ V →
      M = orthElementaryGroup (quadPlus r K) ⊓
        MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) V := by
    intro V hBV hfix hmove
    have hle : M ≤ orthElementaryGroup (quadPlus r K) ⊓
        MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) V := by
      refine le_inf hMG ?_
      rw [hgen, Subgroup.closure_le]
      rintro _ (hb | ⟨j, hj, rfl⟩)
      · exact hBV hb
      · refine MulAction.mem_stabilizer_iff.2 (hfix j ?_)
        rintro rfl
        exact hi hj
    rcases hmax _ hle inf_le_left with h | h
    · exact h.symm
    · exfalso
      have hni : weylElt r K i ∈ orthElementaryGroup (quadPlus r K) ⊓
          MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) V := by
        rw [h]
        exact weylElt_mem i
      exact hmove (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hni).2)
  have hi_lt := i.isLt
  by_cases h1 : i.val + 1 ≤ r - 2
  ·
    refine Or.inl ⟨i.val + 1, by omega, h1, hconcl _ (borel_le_stabilizer_flag (by omega)
      (by omega)) (fun j hj => weylElt_smul_flag_of_ne hr (by omega) h1 fun h =>
        hj (Fin.ext (by omega))) (weylElt_smul_flag_ne hr h1)⟩
  by_cases h2 : i.val = r - 2
  ·
    have hieq : i = ⟨r - 2, by omega⟩ := Fin.ext h2
    refine Or.inr (Or.inl (hconcl _ (borel_le_stabilizer_Xstar _) (fun j hj => ?_) ?_))
    · by_cases hj1 : j.val + 1 ≤ r - 2
      · exact (weylElt_smul_flag_top_and_Xstar hr hj1).2
      · have hjeq : j = ⟨r - 1, by omega⟩ := Fin.ext (show j.val = r - 1 by
          have := j.isLt
          have : j.val ≠ r - 2 := fun h => hj (Fin.ext (show j.val = i.val by omega))
          omega)
        rw [hjeq]
        exact (weylElt_last_smul hr).2
    · rw [hieq]
      exact (weylElt_penult_smul hr).1
  ·
    have hieq : i = ⟨r - 1, by omega⟩ := Fin.ext (show i.val = r - 1 by omega)
    refine Or.inr (Or.inr (hconcl _ (borel_le_stabilizer_flag (by omega) le_rfl)
      (fun j hj => ?_) ?_))
    · by_cases hj1 : j.val + 1 ≤ r - 2
      · exact (weylElt_smul_flag_top_and_Xstar hr hj1).1
      · have hjeq : j = ⟨r - 2, by omega⟩ := Fin.ext (show j.val = r - 2 by
          have := j.isLt
          have : j.val ≠ r - 1 := fun h => hj (Fin.ext (show j.val = i.val by omega))
          omega)
        rw [hjeq]
        exact (weylElt_penult_smul hr).2
    · rw [hieq]
      exact (weylElt_last_smul hr).1

end Generation

theorem orthogonal_geometry_split_maximal_Borel_overgroups {K : Type*} [Field K] {r : ℕ}
    (hr : 3 ≤ r) :
    (∀ M : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      M ≤ orthElementaryGroup (quadPlus r K) → borel r K ≤ M →
      M = Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] _)) ∪
        weylElt r K '' {i | weylElt r K i ∈ M})) ∧
    ∀ M : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      M ≤ orthElementaryGroup (quadPlus r K) → borel r K ≤ M →
      M ≠ orthElementaryGroup (quadPlus r K) →
      (∀ M' : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)), M ≤ M' →
        M' ≤ orthElementaryGroup (quadPlus r K) →
        M' = M ∨ M' = orthElementaryGroup (quadPlus r K)) →
      (∃ i : ℕ, 1 ≤ i ∧ i ≤ r - 2 ∧ M = orthElementaryGroup (quadPlus r K) ⊓
        MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K i)) ∨
      M = orthElementaryGroup (quadPlus r K) ⊓
        MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
          (Xstar r K (by omega)) ∨
      M = orthElementaryGroup (quadPlus r K) ⊓
        MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K r) :=
  ⟨fun _ hMG hBM => eq_closure_of_borel_le hr hMG hBM,
    fun _ hMG hBM hne hmax => eq_stabilizer_of_isMax hr hMG hBM hne hmax⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
