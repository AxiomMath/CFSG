module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPairs
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {r : ℕ} {K : Type*} [Field K]

variable (r K) in
@[expose] noncomputable def rootSupr : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  ⨆ α ∈ roots r, rootSubgroup r K α

theorem rootSubgroup_le_rootSupr {α : Fin r → ℤ} (hα : α ∈ roots r) :
    rootSubgroup r K α ≤ rootSupr r K :=
  le_iSup₂ (f := fun α (_ : α ∈ roots r) => rootSubgroup r K α) α hα

theorem rootSupr_le : rootSupr r K ≤ orthElementaryGroup (quadPlus r K) :=
  iSup₂_le fun α _ => rootSubgroup_le α

theorem rpElt_mem_rootSupr {a b : Fin r ⊕ Fin r} (hab : coordIdx a ≠ coordIdx b) (t : K) :
    rpElt a b t ∈ rootSupr r K := by
  obtain ⟨ε, hε, h1, -⟩ := exists_sign_rootElt_eq_rpElt (K := K) hab
  have hsq : (ε : K) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have h := h1 ((ε : K) * t)
  rw [← mul_assoc, hsq, one_mul] at h
  rw [← h]
  exact rootSubgroup_le_rootSupr (coordWt_sub_mem_roots hab) (rootElt_mem_rootSubgroup _ _)

theorem eichler_single_mem_rootSupr {x y : Fin r ⊕ Fin r} (h : coordIdx x ≠ coordIdx y) (c : K) :
    eichler (quadPlus r K) (Pi.single x 1) (c • Pi.single y 1) ∈ rootSupr r K := by
  have h' : coordIdx x ≠ coordIdx y.swap := by rwa [coordIdx_swap]
  have := rpElt_mem_rootSupr (K := K) h' (-c)
  rwa [rpElt, neg_neg, Sum.swap_swap] at this

theorem eq_zero_of_polar_plusVec {v : Fin r ⊕ Fin r → K}
    (hv : ∀ k s, polar (quadPlus r K) v (plusVec r K k s) = 0) : v = 0 := by
  funext x
  rcases x with k | k
  · have h := hv k false
    rwa [plusVec_false, polar_quadPlus_single_inr] at h
  · have h := hv k true
    rwa [plusVec_true, polar_quadPlus_single_inl] at h

theorem plusVec_eq_single (i : Fin r) (s : Bool) :
    ∃ x : Fin r ⊕ Fin r, coordIdx x = i ∧ plusVec r K i s = Pi.single x 1 := by
  cases s
  · exact ⟨Sum.inr i, rfl, rfl⟩
  · exact ⟨Sum.inl i, rfl, rfl⟩

theorem hlong_rootSupr {i j : Fin r} (hij : i ≠ j) (s t : Bool) (c : K) :
    eichler (quadPlus r K) (plusVec r K j t) (c • plusVec r K i s) ∈ rootSupr r K := by
  obtain ⟨x, hx, hxe⟩ := plusVec_eq_single (K := K) j t
  obtain ⟨y, hy, hye⟩ := plusVec_eq_single (K := K) i s
  rw [hxe, hye]
  exact eichler_single_mem_rootSupr (by rw [hx, hy]; exact Ne.symm hij) c

theorem hperp_rootSupr (i : Fin r) (s : Bool) (v : Fin r ⊕ Fin r → K)
    (hv : ∀ k t, polar (quadPlus r K) v (plusVec r K k t) = 0) :
    eichler (quadPlus r K) (plusVec r K i s) v ∈ rootSupr r K := by
  rw [eq_zero_of_polar_plusVec hv, eichler_zero_right]
  exact one_mem _


theorem orthogonal_geometry_split_root_generation {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r) :
    orthElementaryGroup (quadPlus r K) = rootSupr r K ∧
      ∀ x y : Fin r ⊕ Fin r → K, x ≠ 0 → y ≠ 0 → quadPlus r K x = 0 → quadPlus r K y = 0 →
        ∃ g ∈ rootSupr r K, g x = y := by
  have hrest : ∀ v : Fin r ⊕ Fin r → K,
      (∀ k t, polar (quadPlus r K) v ((plusFrame r K hr).vec k t) = 0) →
        quadPlus r K v = 0 → v = 0 := fun v hv _ => eq_zero_of_polar_plusVec hv
  refine ⟨le_antisymm ?_ rootSupr_le, fun x y hx0 hy0 hx hy => ?_⟩
  · exact (plusFrame r K hr).elementaryGroup_le (H := rootSupr r K)
      (fun hij s t c => hlong_rootSupr hij s t c) (fun i s v hv => hperp_rootSupr i s v hv) hrest
  · exact (plusFrame r K hr).exists_mem_apply_eq (H := rootSupr r K)
      (fun hij s t c => hlong_rootSupr hij s t c) (fun i s v hv => hperp_rootSupr i s v hv) hrest
      (by omega) hx hy hx0 hy0

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
