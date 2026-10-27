module

public import CFSG.LieType.SpinGeom.Simple
public import CFSG.LieType.SpinGeom.FrameVec

public section

namespace CFSG.LieType.SpinGeom

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData QuadraticMap
open scoped Matrix

section Classify

variable {K : Type} [Field K] [CharP K 2] {C : Type} [AddCommGroup C]

private noncomputable def subF (W : AddSubgroup ((Fin (2 * 4) → K) × C)) :
    AddSubgroup (Fin 3 → K) :=
  W.comap (AddMonoidHom.mk' (fun y => (frameVec K 0 0 y 0, (0 : C))) (by
    intro y y'
    refine Prod.ext ?_ ?_
    · show frameVec K 0 0 (y + y') 0 = frameVec K 0 0 y 0 + frameVec K 0 0 y' 0
      rw [frameVec_add]
      simp
    · simp))

private noncomputable def subE (W : AddSubgroup ((Fin (2 * 4) → K) × C)) :
    AddSubgroup (Fin 3 → K) :=
  W.comap (AddMonoidHom.mk' (fun x => (frameVec K 0 x 0 0, (0 : C))) (by
    intro x x'
    refine Prod.ext ?_ ?_
    · show frameVec K 0 (x + x') 0 0 = frameVec K 0 x 0 0 + frameVec K 0 x' 0 0
      rw [frameVec_add]
      simp
    · simp))

omit [CharP K 2] in
private theorem mem_subF {W : AddSubgroup ((Fin (2 * 4) → K) × C)} {y : Fin 3 → K} :
    y ∈ subF W ↔ (frameVec K 0 0 y 0, (0 : C)) ∈ W := Iff.rfl

omit [CharP K 2] in
private theorem mem_subE {W : AddSubgroup ((Fin (2 * 4) → K) × C)} {x : Fin 3 → K} :
    x ∈ subE W ↔ (frameVec K 0 x 0 0, (0 : C)) ∈ W := Iff.rfl

private theorem subF_transvection {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (hX : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∀ w ∈ W,
      (spinElt K 0 0 (Matrix.transvection i j r) w.1, w.2) ∈ W) :
    ∀ i j : Fin 3, i ≠ j → ∀ (s : K) (y : Fin 3 → K), y ∈ subF W →
      (Matrix.transvection i j s *ᵥ y) ∈ subF W := by
  intro i j hij s y hy
  have h := hX j i hij.symm s _ hy
  rw [mem_subF]
  have e : spinElt K 0 0 (Matrix.transvection j i s) (frameVec K 0 0 y 0) =
      frameVec K 0 0 (Matrix.transvection i j s *ᵥ y) 0 := by
    rw [spinElt_iota_frameVec, adjugate_transvection j i hij.symm, transvection_transpose,
      Matrix.mulVec_zero]
  simpa [e] using h

omit [CharP K 2] in
private theorem subE_transvection {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (hX : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∀ w ∈ W,
      (spinElt K 0 0 (Matrix.transvection i j r) w.1, w.2) ∈ W) :
    ∀ i j : Fin 3, i ≠ j → ∀ (s : K) (x : Fin 3 → K), x ∈ subE W →
      (Matrix.transvection i j s *ᵥ x) ∈ subE W := by
  intro i j hij s x hx
  have h := hX i j hij s _ hx
  rw [mem_subE]
  have e : spinElt K 0 0 (Matrix.transvection i j s) (frameVec K 0 x 0 0) =
      frameVec K 0 (Matrix.transvection i j s *ᵥ x) 0 0 := by
    rw [spinElt_iota_frameVec, Matrix.mulVec_zero]
  simpa [e] using h

omit [CharP K 2] in
private theorem quad_frameVec_single :
    coordinateQuadPlus 4 K (frameVec K 0 (Pi.single 0 1) (Pi.single 0 1) 0) = 1 := by
  rw [quad_eq_sum, Fin.sum_univ_succ]
  simp only [coordX_frameVec_zero, coordY_frameVec_zero, coordX_frameVec_succ,
    coordY_frameVec_succ, zero_mul, zero_add]
  rw [Fin.sum_univ_three]
  simp

omit [CharP K 2] in
private theorem zeta_diff_mem {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (h3 : ∀ t : K, (t • frameE K 0, (0 : C)) ∈ W) (h5 : ∀ w ∈ W, coordY K w.1 0 = 0)
    (hζ : ∀ (b : Fin 3) (r : K), ∀ w ∈ W, (spinElt K 0 (Pi.single b r) 1 w.1, w.2) ∈ W)
    {w : (Fin (2 * 4) → K) × C} (hw : w ∈ W) (b : Fin 3) :
    altMat K (Pi.single b 1) *ᵥ xvec K w.1 ∈ subF W := by
  have hw1 : w.1 = frameVec K (coordX K w.1 0) (xvec K w.1) (yvec K w.1) 0 := by
    have := frameVec_coords (K := K) w.1
    rw [h5 w hw] at this
    exact this.symm
  set x₀ := coordX K w.1 0
  set x := xvec K w.1
  set y := yvec K w.1
  set z := altMat K (Pi.single b 1) *ᵥ x with hz
  set t := (Pi.single b 1 : Fin 3 → K) ⬝ᵥ y with ht
  have h1 := hζ b 1 w hw
  rw [hw1, spinElt_zeta_frameVec] at h1
  have e1 : frameVec K (x₀ + t) (x + (0 : K) • (Pi.single b 1 : Fin 3 → K)) (y + z) 0 =
      frameVec K x₀ x y 0 + frameVec K t 0 z 0 := by
    rw [frameVec_add]
    simp
  rw [e1] at h1
  have h2 : (frameVec K t 0 z 0, (0 : C)) ∈ W := by
    have h1' : (frameVec K x₀ x y 0, w.2) + (frameVec K t 0 z 0, (0 : C)) ∈ W := by
      simpa using h1
    have hw' : (frameVec K x₀ x y 0, w.2) ∈ W := by
      rw [← hw1]
      exact hw
    exact (AddSubgroup.add_mem_cancel_left W hw').1 h1'
  have h4 : (t • frameE K 0, (0 : C)) ∈ W := h3 t
  have e2 : frameVec K t 0 z 0 = t • frameE K 0 + frameVec K 0 0 z 0 := by
    rw [frameE_zero_eq, frameVec_smul, frameVec_add]
    simp
  rw [e2] at h2
  have h5' : (t • frameE K 0, (0 : C)) + (frameVec K 0 0 z 0, (0 : C)) ∈ W := by simpa using h2
  exact (AddSubgroup.add_mem_cancel_left W h4).1 h5'

theorem classify_W {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (h3 : ∀ t : K, (t • frameE K 0, (0 : C)) ∈ W) (h5 : ∀ w ∈ W, coordY K w.1 0 = 0)
    (hQ0 : ∀ u : Fin (2 * 4) → K, (u, (0 : C)) ∈ W → coordinateQuadPlus 4 K u = 0)
    (hinj : ∀ w ∈ W, w.1 = 0 → w.2 = 0)
    (hζ : ∀ (b : Fin 3) (r : K), ∀ w ∈ W, (spinElt K 0 (Pi.single b r) 1 w.1, w.2) ∈ W)
    (hX : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∀ w ∈ W,
      (spinElt K 0 0 (Matrix.transvection i j r) w.1, w.2) ∈ W) :
    (∀ w ∈ W, w.2 = 0 ∧ ∃ t : K, w.1 = t • frameE K 0) ∨
      ((∀ w ∈ W, w.2 = 0 ∧ coordY K w.1 0 = 0 ∧ ∀ j : Fin 3, coordX K w.1 j.succ = 0) ∧
        ∀ (x₀ : K) (y : Fin 3 → K), (frameVec K x₀ 0 y 0, (0 : C)) ∈ W) := by
  have hw1 : ∀ w ∈ W, w.1 = frameVec K (coordX K w.1 0) (xvec K w.1) (yvec K w.1) 0 := by
    intro w hw
    have := frameVec_coords (K := K) w.1
    rw [h5 w hw] at this
    exact this.symm
  have hwW : ∀ w ∈ W, (frameVec K (coordX K w.1 0) (xvec K w.1) (yvec K w.1) 0, w.2) ∈ W := by
    intro w hw
    rw [← hw1 w hw]
    exact hw
  have hx0 : ∀ w ∈ W, xvec K w.1 = 0 := by
    intro w hw
    by_contra hxw
    obtain ⟨j, hj⟩ : ∃ j, xvec K w.1 j ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hxw
      exact ⟨j, hj⟩
    have hFtop : subF W = ⊤ := by
      rcases addSubgroup_eq_bot_or_top_of_transvection (subF W) (subF_transvection hX) with hb | ht
      · exfalso
        obtain ⟨b, hb'⟩ : ∃ b : Fin 3, altMat K (Pi.single b 1) *ᵥ xvec K w.1 ≠ 0 := by
          fin_cases j
          · refine ⟨1, fun h => hj ?_⟩
            have := congrFun h 2
            simpa [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
          · refine ⟨0, fun h => hj ?_⟩
            have := congrFun h 2
            simpa [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
          · refine ⟨0, fun h => hj ?_⟩
            have := congrFun h 1
            simpa [altMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
        exact hb' ((AddSubgroup.eq_bot_iff_forall _).1 hb _ (zeta_diff_mem h3 h5 hζ hw b))
      · exact ht
    have hEtop : subE W = ⊤ := by
      rcases addSubgroup_eq_bot_or_top_of_transvection (subE W) (subE_transvection hX) with hb | ht
      · exfalso
        obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
          by_cases hj0 : j = 0
          · exact ⟨1, by rw [hj0]; decide⟩
          · exact ⟨0, fun h => hj0 h.symm⟩
        have h1 := hX i j hij 1 w hw
        rw [hw1 w hw, spinElt_iota_frameVec] at h1
        have hW0 := hwW w hw
        set x₀ := coordX K w.1 0
        set x := xvec K w.1
        set y := yvec K w.1
        set X := Matrix.transvection i j (1 : K) with hXdef
        set X' := (X.adjugate)ᵀ with hX'def
        have hdiff : (frameVec K x₀ (X *ᵥ x) (X' *ᵥ y) 0, w.2) =
            (frameVec K x₀ x y 0, w.2) +
              (frameVec K 0 (X *ᵥ x - x) (X' *ᵥ y - y) 0, (0 : C)) := by
          refine Prod.ext ?_ (by simp)
          show _ = frameVec K x₀ x y 0 + frameVec K 0 (X *ᵥ x - x) (X' *ᵥ y - y) 0
          rw [frameVec_add]
          simp
        have h2 : (frameVec K 0 (X *ᵥ x - x) (X' *ᵥ y - y) 0, (0 : C)) ∈ W := by
          rw [hdiff] at h1
          exact (AddSubgroup.add_mem_cancel_left W hW0).1 h1
        have hF : (frameVec K 0 0 (X' *ᵥ y - y) 0, (0 : C)) ∈ W := by
          rw [← mem_subF, hFtop]
          trivial
        have h3' : (frameVec K 0 (X *ᵥ x - x) 0 0, (0 : C)) ∈ W := by
          have e : (frameVec K 0 (X *ᵥ x - x) 0 0, (0 : C)) +
              (frameVec K 0 0 (X' *ᵥ y - y) 0, (0 : C)) =
              (frameVec K 0 (X *ᵥ x - x) (X' *ᵥ y - y) 0, (0 : C)) := by
            refine Prod.ext ?_ (by simp)
            show frameVec K 0 (X *ᵥ x - x) 0 0 + frameVec K 0 0 (X' *ᵥ y - y) 0 = _
            rw [frameVec_add]
            simp
          have : (frameVec K 0 (X *ᵥ x - x) 0 0, (0 : C)) +
              (frameVec K 0 0 (X' *ᵥ y - y) 0, (0 : C)) ∈ W := by
            rw [e]
            exact h2
          exact (AddSubgroup.add_mem_cancel_right W hF).1 this
        have h4 : X *ᵥ x - x = 0 :=
          (AddSubgroup.eq_bot_iff_forall _).1 hb _ (mem_subE.2 h3')
        have h5' := congrFun h4 i
        rw [hXdef, Pi.sub_apply, transvection_mulVec_apply] at h5'
        simp at h5'
        exact hj h5'
      · exact ht
    have hu : (frameVec K 0 (Pi.single 0 1) (Pi.single 0 1) 0, (0 : C)) ∈ W := by
      have e1 : (frameVec K 0 (Pi.single 0 1) 0 0, (0 : C)) ∈ W := by
        rw [← mem_subE, hEtop]
        trivial
      have e2 : (frameVec K 0 0 (Pi.single 0 1) 0, (0 : C)) ∈ W := by
        rw [← mem_subF, hFtop]
        trivial
      have e : (frameVec K 0 (Pi.single 0 1) 0 0, (0 : C)) +
          (frameVec K 0 0 (Pi.single 0 1) 0, (0 : C)) =
          (frameVec K 0 (Pi.single 0 1) (Pi.single 0 1) 0, (0 : C)) := by
        refine Prod.ext ?_ (by simp)
        show frameVec K 0 (Pi.single 0 1) 0 0 + frameVec K 0 0 (Pi.single 0 1) 0 = _
        rw [frameVec_add]
        simp
      rw [← e]
      exact W.add_mem e1 e2
    have := hQ0 _ hu
    rw [quad_frameVec_single] at this
    exact one_ne_zero this
  by_cases hy : ∀ w ∈ W, yvec K w.1 = 0
  · left
    intro w hw
    have hwv : w.1 = coordX K w.1 0 • frameE K 0 := by
      have h := hw1 w hw
      rw [hx0 w hw, hy w hw] at h
      rw [frameE_zero_eq, frameVec_smul]
      simpa using h
    refine ⟨?_, _, hwv⟩
    have h0 : (0, w.2) ∈ W := by
      have h6 := W.sub_mem hw (h3 (coordX K w.1 0))
      have e : w - (coordX K w.1 0 • frameE K 0, (0 : C)) = (0, w.2) := by
        refine Prod.ext ?_ (by simp)
        show w.1 - coordX K w.1 0 • frameE K 0 = 0
        rw [← hwv, sub_self]
      rwa [e] at h6
    exact hinj (0, w.2) h0 rfl
  · right
    obtain ⟨w, hw, hyw⟩ : ∃ w ∈ W, yvec K w.1 ≠ 0 := by
      by_contra h
      exact hy fun w hw => by
        by_contra hne
        exact h ⟨w, hw, hne⟩
    have hFtop : subF W = ⊤ := by
      rcases addSubgroup_eq_bot_or_top_of_transvection (subF W) (subF_transvection hX) with hb | ht
      · exfalso
        obtain ⟨i, hi⟩ : ∃ i, yvec K w.1 i ≠ 0 := by
          obtain ⟨i, hi⟩ := Function.ne_iff.1 hyw
          exact ⟨i, hi⟩
        obtain ⟨j, hij⟩ : ∃ j : Fin 3, j ≠ i := by
          by_cases hi0 : i = 0
          · exact ⟨1, by rw [hi0]; decide⟩
          · exact ⟨0, fun h => hi0 h.symm⟩
        have h1 := hX i j hij.symm 1 w hw
        rw [hw1 w hw, hx0 w hw, spinElt_iota_frameVec] at h1
        have hW0 := hwW w hw
        rw [hx0 w hw] at hW0
        set x₀ := coordX K w.1 0
        set y := yvec K w.1
        set X := Matrix.transvection i j (1 : K) with hXdef
        set X' := (X.adjugate)ᵀ with hX'def
        have hdiff : (frameVec K x₀ (X *ᵥ (0 : Fin 3 → K)) (X' *ᵥ y) 0, w.2) =
            (frameVec K x₀ 0 y 0, w.2) + (frameVec K 0 0 (X' *ᵥ y - y) 0, (0 : C)) := by
          refine Prod.ext ?_ (by simp)
          show _ = frameVec K x₀ 0 y 0 + frameVec K 0 0 (X' *ᵥ y - y) 0
          rw [frameVec_add]
          simp
        have h2 : (frameVec K 0 0 (X' *ᵥ y - y) 0, (0 : C)) ∈ W := by
          rw [hdiff] at h1
          exact (AddSubgroup.add_mem_cancel_left W hW0).1 h1
        have h4 : X' *ᵥ y - y = 0 := (AddSubgroup.eq_bot_iff_forall _).1 hb _ (mem_subF.2 h2)
        have h5' := congrFun h4 j
        rw [hX'def, hXdef, Pi.sub_apply, adjugate_transvection i j hij.symm,
          transvection_transpose, transvection_mulVec_apply] at h5'
        simp at h5'
        exact hi h5'
      · exact ht
    have hmem : ∀ (x₀ : K) (y : Fin 3 → K), (frameVec K x₀ 0 y 0, (0 : C)) ∈ W := by
      intro x₀ y
      have e : (x₀ • frameE K 0, (0 : C)) + (frameVec K 0 0 y 0, (0 : C)) =
          (frameVec K x₀ 0 y 0, (0 : C)) := by
        refine Prod.ext ?_ (by simp)
        show x₀ • frameE K 0 + frameVec K 0 0 y 0 = _
        rw [frameE_zero_eq, frameVec_smul, frameVec_add]
        simp
      rw [← e]
      refine W.add_mem (h3 x₀) ?_
      rw [← mem_subF, hFtop]
      trivial
    refine ⟨fun w' hw' => ⟨?_, h5 w' hw', fun j => congrFun (hx0 w' hw') j⟩, hmem⟩
    have h0 : (0, w'.2) ∈ W := by
      have h6 := W.sub_mem hw' (hmem (coordX K w'.1 0) (yvec K w'.1))
      have e : w' - (frameVec K (coordX K w'.1 0) 0 (yvec K w'.1) 0, (0 : C)) = (0, w'.2) := by
        refine Prod.ext ?_ (by simp)
        show w'.1 - frameVec K (coordX K w'.1 0) 0 (yvec K w'.1) 0 = 0
        rw [sub_eq_zero]
        have := hw1 w' hw'
        rwa [hx0 w' hw'] at this
      rwa [e] at h6
    exact hinj (0, w'.2) h0 rfl

end Classify

end CFSG.LieType.SpinGeom
