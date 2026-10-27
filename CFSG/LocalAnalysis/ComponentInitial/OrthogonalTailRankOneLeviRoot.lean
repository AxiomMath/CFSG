module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviHom

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

variable (qA : QuadraticForm K A) in
@[expose] noncomputable def tailUpperRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    TailModel K A r :=
  tailLongElt r qA (eps r (tailPair hi 0) - eps r (tailPair hi 1)) s

variable (qA : QuadraticForm K A) in
@[expose] noncomputable def tailLowerRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    TailModel K A r :=
  tailLongElt r qA (-eps r (tailPair hi 0) + eps r (tailPair hi 1)) s

variable {qA : QuadraticForm K A}

private theorem tailPair_ne_H05 {i : Fin r} (hi : i.val + 1 < r) :
    tailPair hi 0 ≠ tailPair hi 1 := by
  intro h
  have := congrArg Fin.val h
  rw [tailPair_val, tailPair_val] at this
  simp at this

private theorem tailPair_lt_H05 {i : Fin r} (hi : i.val + 1 < r) :
    tailPair hi 0 < tailPair hi 1 := by
  rw [Fin.lt_def, tailPair_val, tailPair_val]
  simp

private theorem eichler_eps_sub_eps_single_H05 {i j k : Fin r} (hij : i < j) (t : K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl i) 1) ((-t) • Pi.single (Sum.inr j) 1)
        (Pi.single (Sum.inl k) 1) =
      Pi.single (Sum.inl k) 1 + (if k = j then t • Pi.single (Sum.inl i) 1 else 0) := by
  have h : coordIdx (Sum.inl i : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl j) :=
    coordIdx_inl_ne hij.ne
  change rpElt (Sum.inl i) (Sum.inl j) t (Pi.single (Sum.inl k) 1) = _
  rw [rpElt_apply h t, Sum.swap_inl]
  by_cases hkj : k = j
  · rw [← hkj]
    simp
  · have h1 : (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inl j) = 0 :=
      Pi.single_eq_of_ne (fun hh => hkj (Sum.inl.inj hh).symm) 1
    have h2 : (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inr i) = 0 :=
      Pi.single_eq_of_ne (fun hh => Sum.inr_ne_inl hh) 1
    rw [h1, h2, if_neg hkj]
    simp

private theorem eichler_neg_eps_add_eps_single_H05 {i j k : Fin r} (hij : i < j) (t : K) :
    eichler (quadPlus r K) (Pi.single (Sum.inl j) 1) ((-t) • Pi.single (Sum.inr i) 1)
        (Pi.single (Sum.inl k) 1) =
      Pi.single (Sum.inl k) 1 + (if k = i then t • Pi.single (Sum.inl j) 1 else 0) := by
  have h : coordIdx (Sum.inl j : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl i) :=
    coordIdx_inl_ne hij.ne'
  change rpElt (Sum.inl j) (Sum.inl i) t (Pi.single (Sum.inl k) 1) = _
  rw [rpElt_apply h t, Sum.swap_inl]
  by_cases hki : k = i
  · rw [← hki]
    simp
  · have h1 : (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inl i) = 0 :=
      Pi.single_eq_of_ne (fun hh => hki (Sum.inl.inj hh).symm) 1
    have h2 : (Pi.single (Sum.inl k) (1 : K) : Fin r ⊕ Fin r → K) (Sum.inr j) = 0 :=
      Pi.single_eq_of_ne (fun hh => Sum.inr_ne_inl hh) 1
    rw [h1, h2, if_neg hki]
    simp

private theorem tailLongElt_eps_sub_eps_apply_H05 {i j : Fin r} (hij : i < j) (t : K)
    (k : Fin r) :
    tailLongElt r qA (eps r i - eps r j) t (hypVec K A (.inl k)) =
      hypVec K A (.inl k) + (if k = j then t • hypVec K A (.inl i) else 0) := by
  rw [tailLongElt_eq_prodCongr, rootElt_eps_sub_eps' hij]
  simp only [hypVec, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [eichler_eps_sub_eps_single_H05 hij t]
  by_cases hkj : k = j <;> simp [hkj]

private theorem tailLongElt_neg_eps_add_eps_apply_H05 {i j : Fin r} (hij : i < j) (t : K)
    (k : Fin r) :
    tailLongElt r qA (-eps r i + eps r j) t (hypVec K A (.inl k)) =
      hypVec K A (.inl k) + (if k = i then t • hypVec K A (.inl j) else 0) := by
  rw [tailLongElt_eq_prodCongr, rootElt_neg_eps_add_eps' hij]
  simp only [hypVec, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [eichler_neg_eps_add_eps_single_H05 hij t]
  by_cases hki : k = i <;> simp [hki]

theorem tailUpperRoot_apply_hypVec_inl {i : Fin r} (hi : i.val + 1 < r) (s : K) (j : Fin r) :
    tailUpperRoot qA hi s (hypVec K A (.inl j)) = hypVec K A (.inl j) +
      if j = tailPair hi 1 then s • hypVec K A (.inl (tailPair hi 0)) else 0 := by
  rw [tailUpperRoot]
  exact tailLongElt_eps_sub_eps_apply_H05 (tailPair_lt_H05 hi) s j

theorem tailLowerRoot_apply_hypVec_inl {i : Fin r} (hi : i.val + 1 < r) (s : K) (j : Fin r) :
    tailLowerRoot qA hi s (hypVec K A (.inl j)) = hypVec K A (.inl j) +
      if j = tailPair hi 0 then s • hypVec K A (.inl (tailPair hi 1)) else 0 := by
  rw [tailLowerRoot]
  exact tailLongElt_neg_eps_add_eps_apply_H05 (tailPair_lt_H05 hi) s j

theorem tailUpperRoot_apply_tail {i : Fin r} (hi : i.val + 1 < r) (s : K) (a : A) :
    tailUpperRoot qA hi s ((0 : Fin r ⊕ Fin r → K), a) = (0, a) := by
  rw [tailUpperRoot, tailLongElt_eq_prodCongr]
  simp [LinearEquiv.prodCongr_apply]

theorem tailLowerRoot_apply_tail {i : Fin r} (hi : i.val + 1 < r) (s : K) (a : A) :
    tailLowerRoot qA hi s ((0 : Fin r ⊕ Fin r → K), a) = (0, a) := by
  rw [tailLowerRoot, tailLongElt_eq_prodCongr]
  simp [LinearEquiv.prodCongr_apply]

private theorem map_tailFlag_eq_of_H05 {k : ℕ} (g : TailModel K A r)
    (h : ∀ j : Fin r, j.val < k → g (hypVec K A (.inl j)) ∈ tailFlag K A r k)
    (h' : ∀ j : Fin r, j.val < k → g⁻¹ (hypVec K A (.inl j)) ∈ tailFlag K A r k) :
    (tailFlag K A r k).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r k := by
  apply le_antisymm
  · rw [tailFlag, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, ⟨j, hj, rfl⟩, rfl⟩
    exact h j hj
  · rw [tailFlag, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.mem_map.mpr ⟨g⁻¹ (hypVec K A (.inl j)), h' j hj, by simp⟩

private theorem mem_tailFlag_of_action_H05 {k : ℕ} {g : TailModel K A r} {b0 b1 : Fin r}
    {c : K}
    (hact : ∀ j : Fin r, g (hypVec K A (.inl j)) =
      hypVec K A (.inl j) + (if j = b0 then c • hypVec K A (.inl b1) else 0))
    (hcond : ∀ j : Fin r, j.val < k → j = b0 → b1.val < k)
    (j : Fin r) (hj : j.val < k) :
    g (hypVec K A (.inl j)) ∈ tailFlag K A r k := by
  rw [hact j]
  by_cases h : j = b0
  · rw [if_pos h]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b1, hcond j hj h, rfl⟩))
  · rw [if_neg h, add_zero]
    exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem tailUpperRoot_mem_tailLeviDom {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailUpperRoot qA hi s ∈ tailLeviDom r qA i := by
  rw [mem_tailLeviDom]
  refine ⟨?_, fun k _ _ _ => ?_⟩
  · rw [tailUpperRoot]
    exact tailLongElt_mem _ _
  · refine map_tailFlag_eq_of_H05 (tailUpperRoot qA hi s) (fun j hj => ?_) (fun j hj => ?_)
    · refine mem_tailFlag_of_action_H05 (b0 := tailPair hi 1) (b1 := tailPair hi 0) (c := s)
        (fun j => tailUpperRoot_apply_hypVec_inl hi s j) (fun j hj h => ?_) j hj
      have hjv : j.val = i.val + 1 := by rw [h, tailPair_val]; simp
      rw [tailPair_val]
      omega
    · have h_inv : (tailUpperRoot qA hi s)⁻¹ = tailUpperRoot qA hi (-s) :=
        tailLongElt_inv (eps r (tailPair hi 0) - eps r (tailPair hi 1)) s
      refine mem_tailFlag_of_action_H05 (g := (tailUpperRoot qA hi s)⁻¹)
        (b0 := tailPair hi 1) (b1 := tailPair hi 0) (c := -s)
        (fun j => by rw [h_inv]; exact tailUpperRoot_apply_hypVec_inl hi (-s) j)
        (fun j hj h => ?_) j hj
      have hjv : j.val = i.val + 1 := by rw [h, tailPair_val]; simp
      rw [tailPair_val]
      omega

theorem tailLowerRoot_mem_tailLeviDom {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailLowerRoot qA hi s ∈ tailLeviDom r qA i := by
  rw [mem_tailLeviDom]
  refine ⟨?_, fun k _ _ hk => ?_⟩
  · rw [tailLowerRoot]
    exact tailLongElt_mem _ _
  · refine map_tailFlag_eq_of_H05 (tailLowerRoot qA hi s) (fun j hj => ?_) (fun j hj => ?_)
    · refine mem_tailFlag_of_action_H05 (b0 := tailPair hi 0) (b1 := tailPair hi 1) (c := s)
        (fun j => tailLowerRoot_apply_hypVec_inl hi s j) (fun j hj h => ?_) j hj
      have hjv : j.val = i.val := by rw [h, tailPair_val]; simp
      rw [tailPair_val]
      omega
    · have h_inv : (tailLowerRoot qA hi s)⁻¹ = tailLowerRoot qA hi (-s) :=
        tailLongElt_inv (-eps r (tailPair hi 0) + eps r (tailPair hi 1)) s
      refine mem_tailFlag_of_action_H05 (g := (tailLowerRoot qA hi s)⁻¹)
        (b0 := tailPair hi 0) (b1 := tailPair hi 1) (c := -s)
        (fun j => by rw [h_inv]; exact tailLowerRoot_apply_hypVec_inl hi (-s) j)
        (fun j hj h => ?_) j hj
      have hjv : j.val = i.val := by rw [h, tailPair_val]; simp
      rw [tailPair_val]
      omega

theorem tailLeviBlk_tailUpperRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailLeviBlk hi (tailUpperRoot qA hi s) = !![1, s; 0, 1] := by
  have hne := tailPair_ne_H05 hi
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [tailLeviBlk_apply, tailCoeff, tailUpperRoot_apply_hypVec_inl] <;>
    simp [hypVec, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hne, hne.symm]

theorem tailLeviBlk_tailLowerRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailLeviBlk hi (tailLowerRoot qA hi s) = !![1, 0; s, 1] := by
  have hne := tailPair_ne_H05 hi
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [tailLeviBlk_apply, tailCoeff, tailLowerRoot_apply_hypVec_inl] <;>
    simp [hypVec, Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hne, hne.symm]

theorem tailCoeff_diag_tailUpperRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) {j : Fin r}
    (hj : j.val ≠ i.val ∧ j.val ≠ i.val + 1) : tailCoeff (tailUpperRoot qA hi s) j j = 1 := by
  have h1 : j ≠ tailPair hi 0 := fun h => hj.1 (by rw [h, tailPair_val]; simp)
  have h2 : j ≠ tailPair hi 1 := fun h => hj.2 (by rw [h, tailPair_val]; simp)
  rw [tailCoeff, tailUpperRoot_apply_hypVec_inl]
  simp [hypVec, Pi.single_apply, h1, h2]

theorem tailCoeff_diag_tailLowerRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) {j : Fin r}
    (hj : j.val ≠ i.val ∧ j.val ≠ i.val + 1) : tailCoeff (tailLowerRoot qA hi s) j j = 1 := by
  have h1 : j ≠ tailPair hi 0 := fun h => hj.1 (by rw [h, tailPair_val]; simp)
  have h2 : j ≠ tailPair hi 1 := fun h => hj.2 (by rw [h, tailPair_val]; simp)
  rw [tailCoeff, tailLowerRoot_apply_hypVec_inl]
  simp [hypVec, Pi.single_apply, h1, h2]

theorem tailABlock_tailUpperRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailABlock (tailUpperRoot qA hi s) = 1 := by
  ext a
  rw [tailABlock_apply, tailUpperRoot_apply_tail]
  simp

theorem tailABlock_tailLowerRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailABlock (tailLowerRoot qA hi s) = 1 := by
  ext a
  rw [tailABlock_apply, tailLowerRoot_apply_tail]
  simp

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
