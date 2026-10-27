module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRootGen

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

variable (r qA) in
@[expose] noncomputable def tailRootSupr :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  ⨆ α ∈ rootsB r, tailRootGroup r qA α

theorem tailRootGroup_le_tailRootSupr {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    tailRootGroup r qA α ≤ tailRootSupr r qA :=
  le_iSup₂ (f := fun α (_ : α ∈ rootsB r) => tailRootGroup r qA α) α hα

theorem tailRootSupr_le : tailRootSupr r qA ≤ orthElementaryGroup (quadTail r qA) :=
  iSup₂_le fun α _ => tailRootGroup_le α

variable (A) in
@[expose] def prodHom :
    ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) →*
      (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  toFun g := g.prodCongr (LinearEquiv.refl K A)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem prodHom_apply (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
    prodHom A g = g.prodCongr (LinearEquiv.refl K A) :=
  rfl

theorem map_rootSupr_le : (rootSupr r K).map (prodHom A) ≤ tailRootSupr r qA := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun α hα => ?_
  rintro _ ⟨t, rfl⟩
  rw [Subgroup.mem_comap, prodHom_apply, ← tailLongElt_eq_prodCongr]
  exact tailRootGroup_le_tailRootSupr (Or.inr hα)
    ((mem_tailRootGroup_long hα).2 ⟨t, rfl⟩)

theorem polar_hypVec_bif {i j : Fin r} (hij : i ≠ j) (s t : Bool) :
    polar (quadTail r qA) (hypVec K A (bif s then .inl i else .inr i))
      (hypVec K A (bif t then .inl j else .inr j)) = 0 := by
  rw [polar_hypVec_hypVec, ite_eq_right]
  cases s <;> cases t <;> simp [hij.symm]

variable (r qA) in
@[expose] noncomputable def tailFrame {a₀ : A} (ha₀ : qA a₀ ≠ 0) : HypFrame (quadTail r qA) r where
  vec i s := hypVec K A (bif s then .inl i else .inr i)
  map_vec i s := quadTail_hypVec _
  polar_vec_of_ne _ _ hij s t := polar_hypVec_bif hij s t
  polar_vec_not i s := by cases s <;> simp [polar_hypVec_hypVec]
  exists_aux i j := ⟨(0, a₀), by rw [quadTail_tail]; exact Ne.isUnit ha₀, fun s =>
    ⟨polar_hypVec_tail _ a₀, polar_hypVec_tail _ a₀⟩⟩

theorem tailFrame_vec {a₀ : A} (ha₀ : qA a₀ ≠ 0) (i : Fin r) (s : Bool) :
    (tailFrame r qA ha₀).vec i s = hypVec K A (bif s then .inl i else .inr i) :=
  rfl

theorem fst_eq_zero_of_polar {v : (Fin r ⊕ Fin r → K) × A}
    (hv : ∀ c : Fin r ⊕ Fin r, polar (quadTail r qA) v (hypVec K A c) = 0) : v.1 = 0 := by
  funext c
  have h := hv c.swap
  rwa [polar_hypVec, Sum.swap_swap] at h

theorem hlong_tail {i j : Fin r} (hij : i ≠ j) (s t : Bool) (c : K) :
    eichler (quadTail r qA) (hypVec K A (bif t then .inl j else .inr j))
      (c • hypVec K A (bif s then .inl i else .inr i)) ∈ tailRootSupr r qA := by
  rw [hypVec_smul, hypVec, eichler_prod_fst, ← prodHom_apply]
  refine map_rootSupr_le ⟨_, eichler_single_mem_rootSupr ?_ c, rfl⟩
  cases s <;> cases t <;> simp [coordIdx, Ne.symm hij]

theorem hperp_tail (i : Fin r) (s : Bool) (v : (Fin r ⊕ Fin r → K) × A)
    (hv : ∀ c : Fin r ⊕ Fin r, polar (quadTail r qA) v (hypVec K A c) = 0) :
    eichler (quadTail r qA) (hypVec K A (bif s then .inl i else .inr i)) v ∈
      tailRootSupr r qA := by
  have hv1 := fst_eq_zero_of_polar hv
  have hv' : v = (0, v.2) := Prod.ext hv1 rfl
  rw [hv']
  cases s
  · refine tailRootGroup_le_tailRootSupr (Or.inl ⟨i, Or.inr rfl⟩)
      (mem_tailRootGroup_neg_eps.2 ⟨v.2, rfl⟩)
  · refine tailRootGroup_le_tailRootSupr (Or.inl ⟨i, Or.inl rfl⟩)
      (mem_tailRootGroup_eps.2 ⟨v.2, rfl⟩)

theorem orthogonal_geometry_tail_root_generation {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A} (hani : qA.Anisotropic)
    (hA : ∃ a : A, a ≠ 0) :
    orthElementaryGroup (quadTail r qA) = tailRootSupr r qA ∧
      (2 ≤ r → ∀ x y : (Fin r ⊕ Fin r → K) × A, x ≠ 0 → y ≠ 0 → quadTail r qA x = 0 →
        quadTail r qA y = 0 → ∃ g ∈ tailRootSupr r qA, g x = y) := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hq : qA a₀ ≠ 0 := fun h => ha₀ (hani a₀ h)
  set F := tailFrame r qA hq with hF
  have hall : ∀ v : (Fin r ⊕ Fin r → K) × A, (∀ k t, polar (quadTail r qA) v (F.vec k t) = 0) →
      ∀ c : Fin r ⊕ Fin r, polar (quadTail r qA) v (hypVec K A c) = 0 := by
    intro v hv c
    rcases c with i | i
    · exact hv i true
    · exact hv i false
  have hrest : ∀ v : (Fin r ⊕ Fin r → K) × A,
      (∀ k t, polar (quadTail r qA) v (F.vec k t) = 0) → quadTail r qA v = 0 → v = 0 := by
    intro v hv hQv
    have hv1 := fst_eq_zero_of_polar (hall v hv)
    have hv2 : v.2 = 0 := by
      refine hani v.2 ?_
      rw [quadTail_apply, hv1, QuadraticMap.map_zero, zero_add] at hQv
      exact hQv
    exact Prod.ext hv1 hv2
  have hlong : ∀ {i j : Fin r}, i ≠ j → ∀ (s t : Bool) (c : K),
      eichler (quadTail r qA) (F.vec j t) (c • F.vec i s) ∈ tailRootSupr r qA :=
    fun hij s t c => hlong_tail hij s t c
  have hperp : ∀ (i : Fin r) (s : Bool) (v : (Fin r ⊕ Fin r → K) × A),
      (∀ k t, polar (quadTail r qA) v (F.vec k t) = 0) →
        eichler (quadTail r qA) (F.vec i s) v ∈ tailRootSupr r qA :=
    fun i s v hv => hperp_tail i s v (hall v hv)
  refine ⟨le_antisymm (F.elementaryGroup_le hlong hperp hrest) tailRootSupr_le,
    fun hr x y hx0 hy0 hx hy => F.exists_mem_apply_eq hlong hperp hrest hr hx hy hx0 hy0⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
