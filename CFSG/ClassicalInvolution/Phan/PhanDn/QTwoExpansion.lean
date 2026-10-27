module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoLines
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoTriangleSolid
public import CFSG.ClassicalInvolution.Phan.Geometry.WalkSubstitution
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoCompressed

public section

namespace CFSG.ClassicalInvolution.PhanDn

open Classical SimpleGraph CFSG.ClassicalInvolution.Phan.Geometry CFSG.Monster.B.Recog
open CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}


@[expose] noncomputable def compLine {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) : FlagVert σ 3 :=
  have hline : IsFlipLine σ (U.1.1 ⊔ W.1.1) := hcoll.isFlipLine hU hW
  ⟨U.1.1 ⊔ W.1.1, hline.1,
    fun hbot => by
      have h := hline.2
      rw [hbot, finrank_bot] at h
      omega,
    fun h3 => by
      have h := hline.2
      omega⟩

omit [Finite K] [CharP K 2] in
theorem compLine_coe {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) :
    (compLine hU hW hcoll).1 = U.1.1 ⊔ W.1.1 :=
  rfl

attribute [simp] compLine_coe

omit [Finite K] [CharP K 2] in
theorem compLine_lt_left {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) :
    U.1.1 < (compLine hU hW hcoll).1 := by
  rw [compLine_coe]
  refine lt_of_le_of_ne le_sup_left ?_
  intro hEq
  have h2 := (hcoll.isFlipLine hU hW).2
  rw [← hEq] at h2
  have h1 : Module.finrank K U.1.1 = 1 := hU.2
  omega

omit [Finite K] [CharP K 2] in
theorem compLine_lt_right {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) :
    W.1.1 < (compLine hU hW hcoll).1 := by
  rw [compLine_coe]
  refine lt_of_le_of_ne le_sup_right ?_
  intro hEq
  have h2 := (hcoll.isFlipLine hU hW).2
  rw [← hEq] at h2
  have h1 : Module.finrank K W.1.1 = 1 := hW.2
  omega

omit [Finite K] [CharP K 2] in
theorem compLine_comm {U W : CompVert σ}
    (hU₁ : IsFlipflopPt σ U.1.1) (hW₁ : IsFlipflopPt σ W.1.1)
    (hcoll₁ : FlipColl σ U.1.1 W.1.1)
    (hW₂ : IsFlipflopPt σ W.1.1) (hU₂ : IsFlipflopPt σ U.1.1)
    (hcoll₂ : FlipColl σ W.1.1 U.1.1) :
    compLine hW₂ hU₂ hcoll₂ = compLine hU₁ hW₁ hcoll₁ :=
  Subtype.ext (by rw [compLine_coe, compLine_coe]; exact sup_comm _ _)

omit [Finite K] [CharP K 2] in
theorem compLine_eq_of_le {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) {L : FlagVert σ 3}
    (hL : Module.finrank K L.1 = 2) (hUL : U.1.1 ≤ L.1) (hWL : W.1.1 ≤ L.1) :
    compLine hU hW hcoll = L := by
  refine Subtype.ext ?_
  rw [compLine_coe]
  exact sup_eq_of_mem_ptsOn ⟨L.2.1, hL⟩ ⟨hU, hUL⟩ ⟨hW, hWL⟩ hcoll.1

omit [Finite K] [CharP K 2] in
theorem not_flagGraph_adj_of_finrank_one {X Y : FlagVert σ 3}
    (hX : Module.finrank K X.1 = 1) (hY : Module.finrank K Y.1 = 1) :
    ¬ (flagGraph σ 3).Adj X Y := by
  intro h
  rcases h with h | h | ⟨h1, h2, -⟩
  · exact (ne_of_lt h) (Submodule.eq_of_le_of_finrank_eq (le_of_lt h) (by rw [hX, hY]))
  · exact (ne_of_lt h) (Submodule.eq_of_le_of_finrank_eq (le_of_lt h) (by rw [hY, hX]))
  · omega

omit [Finite K] [CharP K 2] in
theorem lt_of_flagGraph_adj_of_finrank_one_of_four {X Y : FlagVert σ 3}
    (hX : Module.finrank K X.1 = 1) (hY : Module.finrank K Y.1 = 4)
    (h : (flagGraph σ 3).Adj X Y) : X.1 < Y.1 := by
  rcases h with h | h | ⟨h1, h2, -⟩
  · exact h
  · exfalso
    have hle := Submodule.finrank_mono (le_of_lt h)
    omega
  · omega

@[expose] noncomputable def expandCompEdge {U W : CompVert σ} (h : (compGraph σ).Adj U W) :
    (flagGraph σ 3).Walk U.1 W.1 :=
  if hfg : (flagGraph σ 3).Adj U.1 W.1 then
    Walk.cons hfg Walk.nil
  else
    let hpt : IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ U.1.1 W.1.1 :=
      (show (flagGraph σ 3).Adj U.1 W.1 ∨
          (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ U.1.1 W.1.1)
        from h).resolve_left hfg
    Walk.cons (Or.inl (compLine_lt_left hpt.1 hpt.2.1 hpt.2.2))
      (Walk.cons (Or.inr (Or.inl (compLine_lt_right hpt.1 hpt.2.1 hpt.2.2))) Walk.nil)

omit [Finite K] [CharP K 2] in
@[simp] theorem expandCompEdge_of_flagGraph {U W : CompVert σ}
    (h : (flagGraph σ 3).Adj U.1 W.1) :
    expandCompEdge (Or.inl h : (compGraph σ).Adj U W) = Walk.cons h Walk.nil := by
  unfold expandCompEdge
  rw [dif_pos h]

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_of_flipColl {U W : CompVert σ}
    (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) :
    expandCompEdge (Or.inr ⟨hU, hW, hcoll⟩ : (compGraph σ).Adj U W) =
      Walk.cons (Or.inl (compLine_lt_left hU hW hcoll))
        (Walk.cons (Or.inr (Or.inl (compLine_lt_right hU hW hcoll))) Walk.nil) := by
  have hnot : ¬ (flagGraph σ 3).Adj U.1 W.1 :=
    not_flagGraph_adj_of_finrank_one hU.2 hW.2
  unfold expandCompEdge
  rw [dif_neg hnot]

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_symm_of_flagGraph {U W : CompVert σ}
    (h : (compGraph σ).Adj U W) (hfg : (flagGraph σ 3).Adj U.1 W.1)
    (hh : h = Or.inl hfg) :
    expandCompEdge h.symm = Walk.cons hfg.symm Walk.nil := by
  subst hh
  unfold expandCompEdge
  rw [dif_pos hfg.symm]

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_symm_of_flipColl {U W : CompVert σ}
    (h : (compGraph σ).Adj U W) (hU : IsFlipflopPt σ U.1.1) (hW : IsFlipflopPt σ W.1.1)
    (hcoll : FlipColl σ U.1.1 W.1.1) (hh : h = Or.inr ⟨hU, hW, hcoll⟩)
    (hcolls : FlipColl σ W.1.1 U.1.1) :
    expandCompEdge h.symm =
      Walk.cons (Or.inl (compLine_lt_left hW hU hcolls))
        (Walk.cons (Or.inr (Or.inl (compLine_lt_right hW hU hcolls))) Walk.nil) := by
  subst hh
  have hnot : ¬ (flagGraph σ 3).Adj W.1 U.1 :=
    not_flagGraph_adj_of_finrank_one hW.2 hU.2
  unfold expandCompEdge
  rw [dif_neg hnot]

omit [Finite K] [CharP K 2] in
theorem flagGraph_adj_of_compGraph_adj_of_not_both_points {X Y : CompVert σ}
    (hXY : Module.finrank K X.1.1 = 4 ∨ Module.finrank K Y.1.1 = 4)
    (h : (compGraph σ).Adj X Y) : (flagGraph σ 3).Adj X.1 Y.1 := by
  have hnot : ¬ (IsFlipflopPt σ X.1.1 ∧ IsFlipflopPt σ Y.1.1 ∧ FlipColl σ X.1.1 Y.1.1) := by
    rintro ⟨hXp, hYp, -⟩
    rcases hXY with h4 | h4
    · have := hXp.2; omega
    · have := hYp.2; omega
  exact ((show (flagGraph σ 3).Adj X.1 Y.1 ∨
      (IsFlipflopPt σ X.1.1 ∧ IsFlipflopPt σ Y.1.1 ∧ FlipColl σ X.1.1 Y.1.1)
    from h).resolve_right hnot)

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_triangle_point_last {U V W : CompVert σ}
    (hU1 : Module.finrank K U.1.1 = 1) (hV4 : Module.finrank K V.1.1 = 4)
    (hW1 : Module.finrank K W.1.1 = 1)
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  have hfg_uv : (flagGraph σ 3).Adj U.1 V.1 :=
    flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hV4) huv
  have hfg_vw : (flagGraph σ 3).Adj V.1 W.1 :=
    flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hV4) hvw
  have hfalse_wu : ¬ (flagGraph σ 3).Adj W.1 U.1 :=
    not_flagGraph_adj_of_finrank_one hW1 hU1
  have hcoll : FlipColl σ W.1.1 U.1.1 :=
    ((show (flagGraph σ 3).Adj W.1 U.1 ∨
        (IsFlipflopPt σ W.1.1 ∧ IsFlipflopPt σ U.1.1 ∧ FlipColl σ W.1.1 U.1.1)
      from hwu).resolve_left hfalse_wu).2.2
  let hW : IsFlipflopPt σ W.1.1 := ⟨W.1.2.1, hW1⟩
  let hU : IsFlipflopPt σ U.1.1 := ⟨U.1.2.1, hU1⟩
  have hwu' : hwu = (Or.inr ⟨hW, hU, hcoll⟩ : (compGraph σ).Adj W U) :=
    Subsingleton.elim _ _
  have huv' : huv = (Or.inl hfg_uv : (compGraph σ).Adj U V) := Subsingleton.elim _ _
  have hvw' : hvw = (Or.inl hfg_vw : (compGraph σ).Adj V W) := Subsingleton.elim _ _
  rw [huv', hvw', hwu', expandCompEdge_of_flagGraph hfg_uv,
    expandCompEdge_of_flagGraph hfg_vw, expandCompEdge_of_flipColl hW hU hcoll]
  have hUV_lt : U.1.1 < V.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hU1 hV4 hfg_uv
  have hWV_lt : W.1.1 < V.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hW1 hV4 hfg_vw.symm
  let L := compLine hW hU hcoll
  have hLdim : Module.finrank K L.1 = 2 := (hcoll.isFlipLine hW hU).2
  have hLle : L.1 ≤ V.1.1 := by
    rw [show L.1 = W.1.1 ⊔ U.1.1 from compLine_coe hW hU hcoll]
    exact sup_le (le_of_lt hWV_lt) (le_of_lt hUV_lt)
  have hLne : L.1 ≠ V.1.1 := by
    intro hEq
    have := hLdim
    rw [hEq] at this
    omega
  have hLlt : L.1 < V.1.1 := lt_of_le_of_ne hLle hLne
  have f : (flagGraph σ 3).Adj V.1 L := Or.inr (Or.inl hLlt)
  let c : (flagGraph σ 3).Adj W.1 L := Or.inl (compLine_lt_left hW hU hcoll)
  let d : (flagGraph σ 3).Adj L U.1 := Or.inr (Or.inl (compLine_lt_right hW hU hcoll))
  have h1 : Homotopic (Walk.cons hfg_vw (Walk.cons c Walk.nil)) (Walk.cons f Walk.nil) :=
    homotopic_triangle_path hfg_vw c f
  have h2 : Homotopic (Walk.cons hfg_uv (Walk.cons f Walk.nil)) (Walk.cons d.symm Walk.nil) :=
    homotopic_triangle_path hfg_uv f d.symm
  exact homotopic_four_cycle (Walk.cons hfg_uv Walk.nil)
    (Walk.cons hfg_vw (Walk.cons c Walk.nil)) d f h1 h2

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_triangle_point_middle {U V W : CompVert σ}
    (hU4 : Module.finrank K U.1.1 = 4) (hV1 : Module.finrank K V.1.1 = 1)
    (hW1 : Module.finrank K W.1.1 = 1)
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  have hfg_uv : (flagGraph σ 3).Adj U.1 V.1 :=
    flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hU4) huv
  have hfg_wu : (flagGraph σ 3).Adj W.1 U.1 :=
    flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hU4) hwu
  have hfalse_vw : ¬ (flagGraph σ 3).Adj V.1 W.1 :=
    not_flagGraph_adj_of_finrank_one hV1 hW1
  have hcoll : FlipColl σ V.1.1 W.1.1 :=
    ((show (flagGraph σ 3).Adj V.1 W.1 ∨
        (IsFlipflopPt σ V.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ V.1.1 W.1.1)
      from hvw).resolve_left hfalse_vw).2.2
  let hV : IsFlipflopPt σ V.1.1 := ⟨V.1.2.1, hV1⟩
  let hW : IsFlipflopPt σ W.1.1 := ⟨W.1.2.1, hW1⟩
  have hvw' : hvw = (Or.inr ⟨hV, hW, hcoll⟩ : (compGraph σ).Adj V W) :=
    Subsingleton.elim _ _
  have huv' : huv = (Or.inl hfg_uv : (compGraph σ).Adj U V) := Subsingleton.elim _ _
  have hwu' : hwu = (Or.inl hfg_wu : (compGraph σ).Adj W U) := Subsingleton.elim _ _
  rw [huv', hwu', hvw', expandCompEdge_of_flagGraph hfg_uv,
    expandCompEdge_of_flagGraph hfg_wu, expandCompEdge_of_flipColl hV hW hcoll]
  have hVU_lt : V.1.1 < U.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hV1 hU4 hfg_uv.symm
  have hWU_lt : W.1.1 < U.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hW1 hU4 hfg_wu
  let L := compLine hV hW hcoll
  have hLdim : Module.finrank K L.1 = 2 := (hcoll.isFlipLine hV hW).2
  have hLle : L.1 ≤ U.1.1 := by
    rw [show L.1 = V.1.1 ⊔ W.1.1 from compLine_coe hV hW hcoll]
    exact sup_le (le_of_lt hVU_lt) (le_of_lt hWU_lt)
  have hLne : L.1 ≠ U.1.1 := by
    intro hEq
    have := hLdim
    rw [hEq] at this
    omega
  have hLlt : L.1 < U.1.1 := lt_of_le_of_ne hLle hLne
  have e : (flagGraph σ 3).Adj U.1 L := Or.inr (Or.inl hLlt)
  let b : (flagGraph σ 3).Adj V.1 L := Or.inl (compLine_lt_left hV hW hcoll)
  let c : (flagGraph σ 3).Adj L W.1 := Or.inr (Or.inl (compLine_lt_right hV hW hcoll))
  have hp : Homotopic (Walk.cons hfg_uv (Walk.cons b Walk.nil)) (Walk.cons e Walk.nil) :=
    homotopic_triangle_path hfg_uv b e
  have he : Homotopic (Walk.cons e (Walk.cons c Walk.nil)) (Walk.cons hfg_wu.symm Walk.nil) :=
    homotopic_triangle_path e c hfg_wu.symm
  have h1 : Homotopic (Walk.cons hfg_uv (Walk.cons b (Walk.cons c Walk.nil)))
      (Walk.cons hfg_wu.symm Walk.nil) := by
    have h := (hp.append_right (Walk.cons c Walk.nil)).trans he
    simpa using h
  have h2 : Homotopic (Walk.nil.append (Walk.cons hfg_wu.symm Walk.nil))
      (Walk.cons hfg_wu.symm Walk.nil) := Homotopic.refl _
  exact homotopic_four_cycle Walk.nil (Walk.cons hfg_uv (Walk.cons b (Walk.cons c Walk.nil)))
    hfg_wu hfg_wu.symm h1 h2

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_triangle_two_point_solid {U V W : CompVert σ}
    (hU1 : Module.finrank K U.1.1 = 1) (hV1 : Module.finrank K V.1.1 = 1)
    (hW4 : Module.finrank K W.1.1 = 4)
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  have hfalse_uv : ¬ (flagGraph σ 3).Adj U.1 V.1 :=
    not_flagGraph_adj_of_finrank_one hU1 hV1
  have hcoll : FlipColl σ U.1.1 V.1.1 :=
    ((show (flagGraph σ 3).Adj U.1 V.1 ∨
        (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ V.1.1 ∧ FlipColl σ U.1.1 V.1.1)
      from huv).resolve_left hfalse_uv).2.2
  let hU : IsFlipflopPt σ U.1.1 := ⟨U.1.2.1, hU1⟩
  let hV : IsFlipflopPt σ V.1.1 := ⟨V.1.2.1, hV1⟩
  have huv' : huv = (Or.inr ⟨hU, hV, hcoll⟩ : (compGraph σ).Adj U V) :=
    Subsingleton.elim _ _
  have hnotvw : ¬ (IsFlipflopPt σ V.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ V.1.1 W.1.1) := by
    intro h
    have := h.2.1.2
    omega
  have hfg_vw : (flagGraph σ 3).Adj V.1 W.1 :=
    ((show (flagGraph σ 3).Adj V.1 W.1 ∨
        (IsFlipflopPt σ V.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ V.1.1 W.1.1)
      from hvw).resolve_right hnotvw)
  have hnotwu : ¬ (IsFlipflopPt σ W.1.1 ∧ IsFlipflopPt σ U.1.1 ∧ FlipColl σ W.1.1 U.1.1) := by
    intro h
    have := h.1.2
    omega
  have hfg_wu : (flagGraph σ 3).Adj W.1 U.1 :=
    ((show (flagGraph σ 3).Adj W.1 U.1 ∨
        (IsFlipflopPt σ W.1.1 ∧ IsFlipflopPt σ U.1.1 ∧ FlipColl σ W.1.1 U.1.1)
      from hwu).resolve_right hnotwu)
  have hvw' : hvw = (Or.inl hfg_vw : (compGraph σ).Adj V W) := Subsingleton.elim _ _
  have hwu' : hwu = (Or.inl hfg_wu : (compGraph σ).Adj W U) := Subsingleton.elim _ _
  rw [huv', expandCompEdge_of_flipColl hU hV hcoll,
    hvw', expandCompEdge_of_flagGraph hfg_vw,
    hwu', expandCompEdge_of_flagGraph hfg_wu]
  have hVW_lt : V.1.1 < W.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hV1 hW4 hfg_vw
  have hUW_lt : U.1.1 < W.1.1 :=
    lt_of_flagGraph_adj_of_finrank_one_of_four hU1 hW4 hfg_wu.symm
  let L := compLine hU hV hcoll
  have hLdim : Module.finrank K L.1 = 2 := (hcoll.isFlipLine hU hV).2
  have hLle : L.1 ≤ W.1.1 := by
    rw [show L.1 = U.1.1 ⊔ V.1.1 from compLine_coe hU hV hcoll]
    exact sup_le (le_of_lt hUW_lt) (le_of_lt hVW_lt)
  have hLne : L.1 ≠ W.1.1 := by
    intro hEq
    have := hLdim
    rw [hEq] at this
    omega
  have hLlt : L.1 < W.1.1 := lt_of_le_of_ne hLle hLne
  have e : (flagGraph σ 3).Adj L W.1 := Or.inl hLlt
  let a : (flagGraph σ 3).Adj U.1 L := Or.inl (compLine_lt_left hU hV hcoll)
  let b : (flagGraph σ 3).Adj L V.1 := Or.inr (Or.inl (compLine_lt_right hU hV hcoll))
  have h1 : Homotopic (Walk.cons b (Walk.cons hfg_vw Walk.nil)) (Walk.cons e Walk.nil) :=
    homotopic_triangle_path b hfg_vw e
  have h2 : Homotopic (Walk.cons a (Walk.cons e Walk.nil)) (Walk.cons hfg_wu.symm Walk.nil) :=
    homotopic_triangle_path a e hfg_wu.symm
  exact homotopic_four_cycle (Walk.cons a Walk.nil) (Walk.cons b (Walk.cons hfg_vw Walk.nil))
    hfg_wu e h1 h2

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_triangle_retained {U V W : CompVert σ}
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U)
    (huv' : (flagGraph σ 3).Adj U.1 V.1) (hvw' : (flagGraph σ 3).Adj V.1 W.1)
    (hwu' : (flagGraph σ 3).Adj W.1 U.1) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  have euv : huv = Or.inl huv' := Subsingleton.elim _ _
  have evw : hvw = Or.inl hvw' := Subsingleton.elim _ _
  have ewu : hwu = Or.inl hwu' := Subsingleton.elim _ _
  rw [euv, evw, ewu, expandCompEdge_of_flagGraph huv', expandCompEdge_of_flagGraph hvw',
    expandCompEdge_of_flagGraph hwu']
  have h1 := (homotopic_triangle_path huv' hvw' hwu'.symm).append_right (Walk.cons hwu' Walk.nil)
  have h2 : Homotopic ((Walk.cons hwu'.symm Walk.nil).append (Walk.cons hwu' Walk.nil)) .nil := by
    simpa using homotopic_cons_cons_nil hwu'.symm
  simpa using h1.trans h2

theorem expandCompEdge_triangle_three_points (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {U V W : CompVert σ}
    (hU1 : Module.finrank K U.1.1 = 1) (hV1 : Module.finrank K V.1.1 = 1)
    (hW1 : Module.finrank K W.1.1 = 1)
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  have hU : IsFlipflopPt σ U.1.1 := ⟨U.1.2.1, hU1⟩
  have hV : IsFlipflopPt σ V.1.1 := ⟨V.1.2.1, hV1⟩
  have hW : IsFlipflopPt σ W.1.1 := ⟨W.1.2.1, hW1⟩
  have hcollUV : FlipColl σ U.1.1 V.1.1 :=
    ((show (flagGraph σ 3).Adj U.1 V.1 ∨
        (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ V.1.1 ∧ FlipColl σ U.1.1 V.1.1)
      from huv).resolve_left (not_flagGraph_adj_of_finrank_one hU1 hV1)).2.2
  have hcollVW : FlipColl σ V.1.1 W.1.1 :=
    ((show (flagGraph σ 3).Adj V.1 W.1 ∨
        (IsFlipflopPt σ V.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ V.1.1 W.1.1)
      from hvw).resolve_left (not_flagGraph_adj_of_finrank_one hV1 hW1)).2.2
  have hcollWU : FlipColl σ W.1.1 U.1.1 :=
    ((show (flagGraph σ 3).Adj W.1 U.1 ∨
        (IsFlipflopPt σ W.1.1 ∧ IsFlipflopPt σ U.1.1 ∧ FlipColl σ W.1.1 U.1.1)
      from hwu).resolve_left (not_flagGraph_adj_of_finrank_one hW1 hU1)).2.2
  obtain ⟨S, hSsolid, hUS, hVS, hWS⟩ :=
    exists_solid_contains_of_flipColl_triangle hσ hK hU hV hW hcollUV hcollVW hcollWU
  have hS4 : Module.finrank K S = 4 := hSsolid.2
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hS4
    omega
  have hS3 : Module.finrank K S ≠ 3 := by omega
  let SV : FlagVert σ 3 := ⟨S, hSsolid.1, hSne, hS3⟩
  let SC : CompVert σ := ⟨SV, by change Module.finrank K S ≠ 2; omega⟩
  have hSC4 : Module.finrank K SC.1.1 = 4 := hS4
  have hUS_lt : U.1.1 < S :=
    Submodule.lt_of_le_of_finrank_lt_finrank hUS (by rw [hU1, hS4]; omega)
  have hVS_lt : V.1.1 < S :=
    Submodule.lt_of_le_of_finrank_lt_finrank hVS (by rw [hV1, hS4]; omega)
  have hWS_lt : W.1.1 < S :=
    Submodule.lt_of_le_of_finrank_lt_finrank hWS (by rw [hW1, hS4]; omega)
  have hUSC' : (flagGraph σ 3).Adj U.1 SC.1 := Or.inl hUS_lt
  have hVSC' : (flagGraph σ 3).Adj V.1 SC.1 := Or.inl hVS_lt
  have hWSC' : (flagGraph σ 3).Adj W.1 SC.1 := Or.inl hWS_lt
  have hSCU' : (flagGraph σ 3).Adj SC.1 U.1 := Or.inr (Or.inl hUS_lt)
  have hSCV' : (flagGraph σ 3).Adj SC.1 V.1 := Or.inr (Or.inl hVS_lt)
  have hSCW' : (flagGraph σ 3).Adj SC.1 W.1 := Or.inr (Or.inl hWS_lt)
  have hUVcycle := expandCompEdge_triangle_two_point_solid hU1 hV1 hSC4 huv
    (Or.inl (Or.inl hVS_lt) : (compGraph σ).Adj V SC)
    (Or.inl (Or.inr (Or.inl hUS_lt)) : (compGraph σ).Adj SC U)
  have hVWcycle := expandCompEdge_triangle_two_point_solid hV1 hW1 hSC4 hvw
    (Or.inl (Or.inl hWS_lt) : (compGraph σ).Adj W SC)
    (Or.inl (Or.inr (Or.inl hVS_lt)) : (compGraph σ).Adj SC V)
  have hWUcycle := expandCompEdge_triangle_two_point_solid hW1 hU1 hSC4 hwu
    (Or.inl (Or.inl hUS_lt) : (compGraph σ).Adj U SC)
    (Or.inl (Or.inr (Or.inl hWS_lt)) : (compGraph σ).Adj SC W)
  have eUV1 : expandCompEdge (Or.inl (Or.inl hVS_lt) : (compGraph σ).Adj V SC) =
      Walk.cons hVSC' Walk.nil := expandCompEdge_of_flagGraph hVSC'
  have eUV2 : expandCompEdge (Or.inl (Or.inr (Or.inl hUS_lt)) : (compGraph σ).Adj SC U) =
      Walk.cons hSCU' Walk.nil := expandCompEdge_of_flagGraph hSCU'
  have eVW1 : expandCompEdge (Or.inl (Or.inl hWS_lt) : (compGraph σ).Adj W SC) =
      Walk.cons hWSC' Walk.nil := expandCompEdge_of_flagGraph hWSC'
  have eVW2 : expandCompEdge (Or.inl (Or.inr (Or.inl hVS_lt)) : (compGraph σ).Adj SC V) =
      Walk.cons hSCV' Walk.nil := expandCompEdge_of_flagGraph hSCV'
  have eWU1 : expandCompEdge (Or.inl (Or.inl hUS_lt) : (compGraph σ).Adj U SC) =
      Walk.cons hUSC' Walk.nil := expandCompEdge_of_flagGraph hUSC'
  have eWU2 : expandCompEdge (Or.inl (Or.inr (Or.inl hWS_lt)) : (compGraph σ).Adj SC W) =
      Walk.cons hSCW' Walk.nil := expandCompEdge_of_flagGraph hSCW'
  have hUVrel : Homotopic (expandCompEdge huv)
      ((Walk.cons hUSC' Walk.nil).append (Walk.cons hVSC' Walk.nil).reverse) := by
    have hcycle : Homotopic ((expandCompEdge huv).append
        ((Walk.cons hVSC' Walk.nil).append (Walk.cons hSCU' Walk.nil))) .nil := by
      simpa only [eUV1, eUV2] using hUVcycle
    have h := homotopic_of_append_nil hcycle
    simpa [Walk.reverse_cons, Walk.reverse_append] using h
  have hVWrel : Homotopic (expandCompEdge hvw)
      ((Walk.cons hVSC' Walk.nil).append (Walk.cons hWSC' Walk.nil).reverse) := by
    have hcycle : Homotopic ((expandCompEdge hvw).append
        ((Walk.cons hWSC' Walk.nil).append (Walk.cons hSCV' Walk.nil))) .nil := by
      simpa only [eVW1, eVW2] using hVWcycle
    have h := homotopic_of_append_nil hcycle
    simpa [Walk.reverse_cons, Walk.reverse_append] using h
  have hWUrel : Homotopic (expandCompEdge hwu)
      ((Walk.cons hWSC' Walk.nil).append (Walk.cons hUSC' Walk.nil).reverse) := by
    have hcycle : Homotopic ((expandCompEdge hwu).append
        ((Walk.cons hUSC' Walk.nil).append (Walk.cons hSCW' Walk.nil))) .nil := by
      simpa only [eWU1, eWU2] using hWUcycle
    have h := homotopic_of_append_nil hcycle
    simpa [Walk.reverse_cons, Walk.reverse_append] using h
  exact (hUVrel.append (hVWrel.append hWUrel)).trans
    (homotopic_cone_triangle (Walk.cons hUSC' Walk.nil) (Walk.cons hVSC' Walk.nil)
      (Walk.cons hWSC' Walk.nil))

theorem expandCompEdge_triangle (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {U V W : CompVert σ}
    (huv : (compGraph σ).Adj U V) (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) :
    Homotopic ((expandCompEdge huv).append ((expandCompEdge hvw).append (expandCompEdge hwu))) .nil := by
  rcases CompVert.finrank_one_four U with hU1 | hU4 <;>
  rcases CompVert.finrank_one_four V with hV1 | hV4 <;>
  rcases CompVert.finrank_one_four W with hW1 | hW4
  · exact expandCompEdge_triangle_three_points hσ hK hU1 hV1 hW1 huv hvw hwu
  · exact expandCompEdge_triangle_two_point_solid hU1 hV1 hW4 huv hvw hwu
  · exact expandCompEdge_triangle_point_last hU1 hV4 hW1 huv hvw hwu
  · exact expandCompEdge_triangle_retained huv hvw hwu
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hV4) huv)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hW4) hvw)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hW4) hwu)
  · exact expandCompEdge_triangle_point_middle hU4 hV1 hW1 huv hvw hwu
  · exact expandCompEdge_triangle_retained huv hvw hwu
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hU4) huv)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hW4) hvw)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hU4) hwu)
  · exact expandCompEdge_triangle_retained huv hvw hwu
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hU4) huv)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hV4) hvw)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inr hU4) hwu)
  · exact expandCompEdge_triangle_retained huv hvw hwu
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hU4) huv)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hV4) hvw)
      (flagGraph_adj_of_compGraph_adj_of_not_both_points (Or.inl hW4) hwu)

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_via_line {U W : CompVert σ} {L : FlagVert σ 3}
    (hL : Module.finrank K L.1 = 2) (hUL : U.1.1 < L.1) (hWL : W.1.1 < L.1)
    (hUW : (compGraph σ).Adj U W) :
    Homotopic (expandCompEdge hUW)
      (Walk.cons (Or.inl hUL) (Walk.cons (Or.inr (Or.inl hWL)) Walk.nil)) := by
  have hU1 : Module.finrank K U.1.1 = 1 := by
    have hlt : Module.finrank K U.1.1 < Module.finrank K L.1 :=
      Submodule.finrank_lt_finrank_of_lt hUL
    have hne : Module.finrank K U.1.1 ≠ 0 := fun h0 =>
      U.1.2.2.1 (Submodule.finrank_eq_zero.mp h0)
    omega
  have hW1 : Module.finrank K W.1.1 = 1 := by
    have hlt : Module.finrank K W.1.1 < Module.finrank K L.1 :=
      Submodule.finrank_lt_finrank_of_lt hWL
    have hne : Module.finrank K W.1.1 ≠ 0 := fun h0 =>
      W.1.2.2.1 (Submodule.finrank_eq_zero.mp h0)
    omega
  let hU : IsFlipflopPt σ U.1.1 := ⟨U.1.2.1, hU1⟩
  let hW : IsFlipflopPt σ W.1.1 := ⟨W.1.2.1, hW1⟩
  have hfalse : ¬ (flagGraph σ 3).Adj U.1 W.1 :=
    not_flagGraph_adj_of_finrank_one hU1 hW1
  have hcoll : FlipColl σ U.1.1 W.1.1 :=
    ((show (flagGraph σ 3).Adj U.1 W.1 ∨
        (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ U.1.1 W.1.1)
      from hUW).resolve_left hfalse).2.2
  have hUW' : hUW = (Or.inr ⟨hU, hW, hcoll⟩ : (compGraph σ).Adj U W) :=
    Subsingleton.elim _ _
  rw [hUW', expandCompEdge_of_flipColl hU hW hcoll]
  let L0 := compLine hU hW hcoll
  have hline : L0 = L :=
    compLine_eq_of_le hU hW hcoll hL (le_of_lt hUL) (le_of_lt hWL)
  let a : (flagGraph σ 3).Adj U.1 L0 := Or.inl (compLine_lt_left hU hW hcoll)
  let b : (flagGraph σ 3).Adj L0 W.1 := Or.inr (Or.inl (compLine_lt_right hU hW hcoll))
  change Homotopic (Walk.cons a (Walk.cons b Walk.nil))
    (Walk.cons (Or.inl hUL) (Walk.cons (Or.inr (Or.inl hWL)) Walk.nil))
  exact homotopic_two_edge_of_eq hline a b (Or.inl hUL) (Or.inr (Or.inl hWL))

omit [Finite K] [CharP K 2] in
theorem expandCompEdge_backtrack {U W : CompVert σ} (h : (compGraph σ).Adj U W) :
    Homotopic ((expandCompEdge h).append (expandCompEdge h.symm)) .nil := by
  rcases h with hfg | ⟨hU, hW, hne, hsub⟩
  · rw [expandCompEdge_of_flagGraph hfg]
    rw [expandCompEdge_symm_of_flagGraph (h := Or.inl hfg) hfg rfl]
    exact homotopic_cons_cons_nil hfg
  · have hcoll : FlipColl σ U.1.1 W.1.1 := ⟨hne, hsub⟩
    have hcolls : FlipColl σ W.1.1 U.1.1 := ⟨Ne.symm hne, by rwa [sup_comm]⟩
    rw [expandCompEdge_of_flipColl hU hW hcoll]
    rw [expandCompEdge_symm_of_flipColl (h := Or.inr ⟨hU, hW, hcoll⟩) hU hW hcoll rfl hcolls]
    let L' := compLine hW hU hcolls
    let L := compLine hU hW hcoll
    have hL : L' = L := compLine_comm hU hW hcoll hW hU hcolls
    let a' : (flagGraph σ 3).Adj W.1 L' := Or.inl (compLine_lt_left hW hU hcolls)
    let b' : (flagGraph σ 3).Adj L' U.1 := Or.inr (Or.inl (compLine_lt_right hW hU hcolls))
    set p : (flagGraph σ 3).Walk U.1 W.1 :=
      Walk.cons (Or.inl (compLine_lt_left hU hW hcoll))
        (Walk.cons (Or.inr (Or.inl (compLine_lt_right hU hW hcoll))) Walk.nil) with hp
    have hq : Homotopic (Walk.cons a' (Walk.cons b' Walk.nil)) p.reverse :=
      homotopic_two_edge_of_eq hL a' b'
        (Or.inl (compLine_lt_right hU hW hcoll))
        (Or.inr (Or.inl (compLine_lt_left hU hW hcoll)))
    exact (Homotopic.append_left p hq).trans (homotopic_append_reverse p)

end CFSG.ClassicalInvolution.PhanDn

end
