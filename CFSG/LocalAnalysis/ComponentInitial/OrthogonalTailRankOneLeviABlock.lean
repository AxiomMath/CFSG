module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviDom

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

@[expose] def tailABlock (g : TailModel K A r) : Module.End K A :=
  (LinearMap.snd K (Fin r ⊕ Fin r → K) A).comp
    ((g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)).comp
      (LinearMap.inr K (Fin r ⊕ Fin r → K) A))

theorem tailABlock_apply (g : TailModel K A r) (a : A) :
    tailABlock g a = (g ((0 : Fin r ⊕ Fin r → K), a)).2 := by
  rfl

private theorem tailLeviDom_polar_eq_zero_H02 {v : (Fin r ⊕ Fin r → K) × A}
    (hv : ∀ j, v.1 (.inr j) = 0) {w : (Fin r ⊕ Fin r → K) × A}
    (hw : w ∈ tailFlag K A r r) : polar (quadTail r qA) v w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, rfl⟩ := hx
    simp [polar_hypVec, Sum.swap_inl, hv k]
  | zero => rw [polar_zero_right]
  | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [polar_smul_right, hx, smul_zero]

theorem tailLeviDom_fst_inr_eq_zero {i : Fin r} (hi : i.val + 1 < r) {g : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) {v : (Fin r ⊕ Fin r → K) × A} (hv : ∀ j, v.1 (.inr j) = 0)
    (j : Fin r) : (g v).1 (.inr j) = 0 := by
  have hgE : g ∈ orthElementaryGroup (quadTail r qA) := (mem_tailLeviDom.1 hg).1
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
    orthElementaryGroup_le _ hgE
  have hgInv : g⁻¹ ∈ tailLeviDom r qA i := Subgroup.inv_mem (tailLeviDom r qA i) hg
  have hFr_inv : (tailFlag K A r r).map ((g⁻¹ : TailModel K A r) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      tailFlag K A r r :=
    (mem_tailLeviDom.1 hgInv).2 r (by omega) le_rfl (by omega)
  set w : (Fin r ⊕ Fin r → K) × A := g⁻¹ (hypVec K A (.inl j)) with hw
  have hwF : w ∈ tailFlag K A r r := by
    have he : hypVec K A (.inl j) ∈ tailFlag K A r r :=
      Submodule.subset_span ⟨j, j.isLt, rfl⟩
    have hmem : (g⁻¹ : TailModel K A r) (hypVec K A (.inl j)) ∈
        (tailFlag K A r r).map ((g⁻¹ : TailModel K A r) :
          ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
      Submodule.mem_map_of_mem he
    rw [hFr_inv] at hmem
    rw [← hw] at hmem
    exact hmem
  have hgw : g w = hypVec K A (.inl j) := by
    rw [hw]
    exact LinearEquiv.apply_symm_apply g _
  have hpolar : polar (quadTail r qA) v w = 0 := tailLeviDom_polar_eq_zero_H02 hv hwF
  have h1 := polar_hypVec (qA := qA) (g v) (.inl j)
  rw [Sum.swap_inl] at h1
  rw [← h1, ← hgw, polar_map_of_mem hgO]
  exact hpolar

theorem tailLeviDom_snd_eq_zero {i : Fin r} (hi : i.val + 1 < r) {g : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) {v : (Fin r ⊕ Fin r → K) × A} (hv : ∀ j, v.1 (.inr j) = 0)
    (hv2 : v.2 = 0) : (g v).2 = 0 := by
  have hFr : (tailFlag K A r r).map ((g : TailModel K A r) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      tailFlag K A r r :=
    (mem_tailLeviDom.1 hg).2 r (by omega) le_rfl (by omega)
  have hvF : v ∈ tailFlag K A r r := by
    rw [mem_tailFlag_iff]
    refine ⟨?_, hv2⟩
    rw [mem_flag]
    exact ⟨hv, fun j hj => absurd j.isLt (not_lt_of_ge hj)⟩
  have hmem : g v ∈ tailFlag K A r r := by
    have hmap := Submodule.mem_map_of_mem (f := ((g : TailModel K A r) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A))) hvF
    rwa [hFr] at hmap
  exact (mem_tailFlag_iff.1 hmem).2

theorem tailABlock_one : tailABlock (1 : TailModel K A r) = 1 := by
  ext a
  simp [tailABlock_apply]

theorem tailABlock_mul {i : Fin r} (hi : i.val + 1 < r) {g h : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) (hh : h ∈ tailLeviDom r qA i) :
    tailABlock (g * h) = tailABlock g * tailABlock h := by
  ext a
  set y : (Fin r ⊕ Fin r → K) × A := h ((0 : Fin r ⊕ Fin r → K), a) with hy
  have hy1 : ∀ j : Fin r, y.1 (.inr j) = 0 := by
    intro j
    rw [hy]
    exact tailLeviDom_fst_inr_eq_zero hi hh (fun _ => rfl) j
  have hg2 : (g (y.1, 0)).2 = 0 := by
    apply tailLeviDom_snd_eq_zero hi hg (v := (y.1, 0))
    · intro j
      rw [hy1 j]
    · rfl
  have hdecomp : y = (y.1, 0) + ((0 : Fin r ⊕ Fin r → K), y.2) := by
    refine Prod.ext ?_ ?_ <;> simp
  calc tailABlock (g * h) a
      = (g (h ((0 : Fin r ⊕ Fin r → K), a))).2 := by
          rw [tailABlock_apply, LinearEquiv.mul_apply]
    _ = (g y).2 := by rw [← hy]
    _ = (g ((y.1, 0) + ((0 : Fin r ⊕ Fin r → K), y.2))).2 := by
          conv_lhs => rw [hdecomp]
    _ = (g (y.1, 0) + g ((0 : Fin r ⊕ Fin r → K), y.2)).2 := by rw [map_add]
    _ = (g (y.1, 0)).2 + (g ((0 : Fin r ⊕ Fin r → K), y.2)).2 := rfl
    _ = (g ((0 : Fin r ⊕ Fin r → K), y.2)).2 := by rw [hg2, zero_add]
    _ = tailABlock g y.2 := by rw [← tailABlock_apply]
    _ = tailABlock g (tailABlock h a) := by rw [hy, ← tailABlock_apply]
    _ = (tailABlock g * tailABlock h) a := by rw [Module.End.mul_apply]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
