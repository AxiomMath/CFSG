module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoExpansion
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import CFSG.Monster.B.GSide.HomotopyLocal

public section

namespace CFSG.ClassicalInvolution.PhanDn

open SimpleGraph CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog
open CFSG.ClassicalInvolution.Phan.Geometry

variable {K : Type} [Field K] {σ : K ≃+* K}

noncomputable def chosenLinePoint (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ 3) (hU : Module.finrank K U.1 = 2) : CompVert σ :=
  (exists_compVert_flagGraph_adj_of_finrank_two hσ hU).choose

theorem chosenLinePoint_lt (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ 3) (hU : Module.finrank K U.1 = 2) :
    (chosenLinePoint hσ U hU).1.1 < U.1 :=
  (exists_compVert_flagGraph_adj_of_finrank_two hσ hU).choose_spec.1

theorem chosenLinePoint_adj (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ 3) (hU : Module.finrank K U.1 = 2) :
    (flagGraph σ 3).Adj (chosenLinePoint hσ U hU).1 U :=
  (exists_compVert_flagGraph_adj_of_finrank_two hσ hU).choose_spec.2

abbrev compIncl (σ : K ≃+* K) : CompVert σ → FlagVert σ 3 := fun U => U.1

noncomputable def retractCompVert (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ 3) : CompVert σ :=
  @dite (CompVert σ) (Module.finrank K U.1 = 2) (Classical.propDecidable _)
    (fun hU => chosenLinePoint hσ U hU) (fun hU => ⟨U, hU⟩)

theorem retractCompVert_line (hσ : IsUnitaryInvolution σ) {U : FlagVert σ 3}
    (hU : Module.finrank K U.1 = 2) :
    retractCompVert hσ U = chosenLinePoint hσ U hU := by
  erw [retractCompVert, dif_pos hU]

theorem retractCompVert_ret (hσ : IsUnitaryInvolution σ) {U : FlagVert σ 3}
    (hU : Module.finrank K U.1 ≠ 2) :
    retractCompVert hσ U = ⟨U, hU⟩ := by
  erw [retractCompVert, dif_neg hU]

noncomputable def retractConnector (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ 3) : (flagGraph σ 3).Walk U (retractCompVert hσ U).1 := by
  classical
  by_cases hU : Module.finrank K U.1 = 2
  · exact (Walk.cons (chosenLinePoint_adj hσ U hU).symm Walk.nil).copy rfl
      (congrArg (compIncl σ) (retractCompVert_line hσ hU).symm)
  · exact (Walk.nil : (flagGraph σ 3).Walk U U).copy rfl
      (congrArg (compIncl σ) (retractCompVert_ret hσ hU).symm)

theorem retractConnector_line (hσ : IsUnitaryInvolution σ) {U : FlagVert σ 3}
    (hU : Module.finrank K U.1 = 2) :
    retractConnector hσ U =
      (Walk.cons (chosenLinePoint_adj hσ U hU).symm Walk.nil).copy rfl
        (congrArg (compIncl σ) (retractCompVert_line hσ hU).symm) := by
  unfold retractConnector
  rw [dif_pos hU]

theorem retractConnector_ret (hσ : IsUnitaryInvolution σ) {U : FlagVert σ 3}
    (hU : Module.finrank K U.1 ≠ 2) :
    retractConnector hσ U =
      (Walk.nil : (flagGraph σ 3).Walk U U).copy rfl
        (congrArg (compIncl σ) (retractCompVert_ret hσ hU).symm) := by
  unfold retractConnector
  rw [dif_neg hU]

@[simp] theorem retractCompVert_retained (hσ : IsUnitaryInvolution σ) (U : CompVert σ) :
    retractCompVert hσ U.1 = U := by
  classical
  erw [retractCompVert, dif_neg U.2]
  rfl

theorem flagGraph_not_two_two {U W : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj U W) (hU : Module.finrank K U.1 = 2) :
    Module.finrank K W.1 ≠ 2 := by
  intro hW
  rcases h with h | h | ⟨h, _, _⟩
  · have hd := Submodule.finrank_lt_finrank_of_lt h
    omega
  · have hd := Submodule.finrank_lt_finrank_of_lt h
    omega
  · omega


abbrev CompHedge (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj u v)
    (q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v)) : Prop :=
  Homotopic ((retractConnector hσ u).append
      (substituteWalk (compIncl σ) (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) =>
        expandCompEdge e) q))
    ((Walk.cons h Walk.nil).append (retractConnector hσ v))

theorem hedge_of_copies (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    {U0 V0 : CompVert σ}
    (eu : retractCompVert hσ u = U0) (ev : retractCompVert hσ v = V0)
    (q0 : (compGraph σ).Walk U0 V0)
    (cu0 : (flagGraph σ 3).Walk u U0.1) (cv0 : (flagGraph σ 3).Walk v V0.1)
    (h : (flagGraph σ 3).Adj u v)
    (H0 : Homotopic (cu0.append
        (substituteWalk (compIncl σ) (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) =>
          expandCompEdge e) q0))
      ((Walk.cons h Walk.nil).append cv0))
    (hcu : retractConnector hσ u =
      cu0.copy rfl (congrArg (compIncl σ) eu.symm))
    (hcv : retractConnector hσ v =
      cv0.copy rfl (congrArg (compIncl σ) ev.symm)) :
    CompHedge hσ h (q0.copy eu.symm ev.symm) := by
  unfold CompHedge
  have hq : substituteWalk (compIncl σ)
      (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e)
      (q0.copy eu.symm ev.symm) =
      (substituteWalk (compIncl σ)
        (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e) q0).copy
        (congrArg (compIncl σ) eu.symm) (congrArg (compIncl σ) ev.symm) := by
    erw [substituteWalk_copy]
  erw [hq, hcu, hcv]
  have hL : ((cu0.copy rfl (congrArg (compIncl σ) eu.symm)).append
      ((substituteWalk (compIncl σ)
        (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e) q0).copy
        (congrArg (compIncl σ) eu.symm) (congrArg (compIncl σ) ev.symm))) =
      ((cu0.append (substituteWalk (compIncl σ)
        (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e) q0)).copy
        rfl (congrArg (compIncl σ) ev.symm)) :=
    Walk.append_copy_copy _ _ rfl _ _
  rw [hL]
  have hR : ((Walk.cons h Walk.nil).append
      (cv0.copy rfl (congrArg (compIncl σ) ev.symm))) =
      ((Walk.cons h Walk.nil).append cv0).copy rfl
        (congrArg (compIncl σ) ev.symm) := by
    simpa only [Walk.copy_rfl_rfl] using
      (Walk.append_copy_copy (p := Walk.cons h Walk.nil) (q := cv0) rfl rfl
        (congrArg (compIncl σ) ev.symm))
  rw [hR]
  exact CFSG.Monster.B.GSide.homotopic_copy H0 rfl (congrArg (compIncl σ) ev.symm)

theorem exists_reduce_line_solid (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hu : Module.finrank K u.1 = 2) (hv4 : Module.finrank K v.1 = 4)
    (h : (flagGraph σ 3).Adj u v) (huv : u.1 < v.1) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  have hv : Module.finrank K v.1 ≠ 2 := by omega
  let U0 : CompVert σ := chosenLinePoint hσ u hu
  let V0 : CompVert σ := ⟨v, hv⟩
  have eu : retractCompVert hσ u = U0 := retractCompVert_line hσ hu
  have ev : retractCompVert hσ v = V0 := retractCompVert_ret hσ hv
  have hUP : (flagGraph σ 3).Adj U0.1 u := chosenLinePoint_adj hσ u hu
  have hPv : (flagGraph σ 3).Adj U0.1 v :=
    Or.inl (lt_trans (chosenLinePoint_lt hσ u hu) huv)
  let q0 : (compGraph σ).Walk U0 V0 := Walk.cons (Or.inl hPv) Walk.nil
  let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.cons hUP.symm Walk.nil
  let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.nil
  have H0 : Homotopic (cu0.append
      (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
        (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
      ((Walk.cons h Walk.nil).append cv0) := by
    dsimp only [cu0, cv0, q0]
    erw [substituteWalk_cons, substituteWalk_nil, expandCompEdge_of_flagGraph hPv]
    exact homotopic_triangle_path hUP.symm hPv h
  refine ⟨q0.copy eu.symm ev.symm, ?_⟩
  exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
    (retractConnector_line hσ hu) (retractConnector_ret hσ hv)

theorem exists_reduce_solid_line (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hu4 : Module.finrank K u.1 = 4) (hv : Module.finrank K v.1 = 2)
    (h : (flagGraph σ 3).Adj u v) (hvu : v.1 < u.1) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  have hune : Module.finrank K u.1 ≠ 2 := by omega
  let U0 : CompVert σ := ⟨u, hune⟩
  let V0 : CompVert σ := chosenLinePoint hσ v hv
  have eu : retractCompVert hσ u = U0 := retractCompVert_ret hσ hune
  have ev : retractCompVert hσ v = V0 := retractCompVert_line hσ hv
  have hVP : (flagGraph σ 3).Adj V0.1 v := chosenLinePoint_adj hσ v hv
  have hPV : (flagGraph σ 3).Adj u V0.1 :=
    Or.inr (Or.inl (lt_trans (chosenLinePoint_lt hσ v hv) hvu))
  let q0 : (compGraph σ).Walk U0 V0 := Walk.cons (Or.inl hPV) Walk.nil
  let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.nil
  let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.cons hVP.symm Walk.nil
  have H0 : Homotopic (cu0.append
      (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
        (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
      ((Walk.cons h Walk.nil).append cv0) := by
    dsimp only [cu0, cv0, q0]
    erw [substituteWalk_cons, substituteWalk_nil, expandCompEdge_of_flagGraph hPV]
    exact (homotopic_triangle_path h hVP.symm hPV).symm
  refine ⟨q0.copy eu.symm ev.symm, ?_⟩
  exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
    (retractConnector_ret hσ hune) (retractConnector_line hσ hv)

theorem exists_reduce_retained (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hune : Module.finrank K u.1 ≠ 2) (hvne : Module.finrank K v.1 ≠ 2)
    (h : (flagGraph σ 3).Adj u v) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  let U0 : CompVert σ := ⟨u, hune⟩
  let V0 : CompVert σ := ⟨v, hvne⟩
  have eu : retractCompVert hσ u = U0 := retractCompVert_ret hσ hune
  have ev : retractCompVert hσ v = V0 := retractCompVert_ret hσ hvne
  let q0 : (compGraph σ).Walk U0 V0 := Walk.cons (Or.inl h) Walk.nil
  let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.nil
  let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.nil
  have H0 : Homotopic (cu0.append
      (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
        (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
      ((Walk.cons h Walk.nil).append cv0) := by
    dsimp only [cu0, cv0, q0]
    erw [substituteWalk_cons, substituteWalk_nil, expandCompEdge_of_flagGraph h]
    exact Homotopic.refl _
  refine ⟨q0.copy eu.symm ev.symm, ?_⟩
  exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
    (retractConnector_ret hσ hune) (retractConnector_ret hσ hvne)

theorem exists_reduce_point_line (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hu1 : Module.finrank K u.1 = 1) (hv : Module.finrank K v.1 = 2)
    (h : (flagGraph σ 3).Adj u v) (huv : u.1 < v.1) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  have hune : Module.finrank K u.1 ≠ 2 := by omega
  let P : CompVert σ := chosenLinePoint hσ v hv
  let U0 : CompVert σ := ⟨u, hune⟩
  let V0 : CompVert σ := P
  have eu : retractCompVert hσ u = U0 := retractCompVert_ret hσ hune
  have ev : retractCompVert hσ v = V0 := retractCompVert_line hσ hv
  have hVP : (flagGraph σ 3).Adj P.1 v := chosenLinePoint_adj hσ v hv
  have hP_lt : P.1.1 < v.1 := chosenLinePoint_lt hσ v hv
  have hPfin : Module.finrank K P.1.1 = 1 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt hP_lt
    rcases P.1.finrank_one_two_four (σ := σ) with h1 | h2 | h4
    · exact h1
    · exact absurd h2 P.2
    · omega
  have hPpt : IsFlipflopPt σ P.1.1 := ⟨P.1.2.1, hPfin⟩
  have hUpt : IsFlipflopPt σ u.1 := ⟨u.2.1, hu1⟩
  have hline : IsFlipLine σ v.1 := ⟨v.2.1, hv⟩
  by_cases hz : u.1 = P.1.1
  · have e : U0 = V0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    let q0 : (compGraph σ).Walk U0 V0 :=
      (Walk.nil : (compGraph σ).Walk U0 U0).copy rfl e
    let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.nil
    let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.cons hVP.symm Walk.nil
    have H0 : Homotopic (cu0.append
        (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
          (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
        ((Walk.cons h Walk.nil).append cv0) := by
      dsimp only [cu0, cv0, q0]
      have hq0 : substituteWalk (compIncl σ)
          (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e)
          ((Walk.nil : (compGraph σ).Walk U0 U0).copy rfl e) =
          (Walk.nil : (flagGraph σ 3).Walk U0.1 U0.1).copy rfl
            (congrArg (compIncl σ) e) := by
        erw [substituteWalk_copy]
        rfl
      erw [hq0]
      change Homotopic ((Walk.nil : (flagGraph σ 3).Walk (compIncl σ U0) (compIncl σ U0)).copy
          rfl (congrArg (compIncl σ) e))
        (Walk.cons h (Walk.cons hVP.symm Walk.nil))
      exact homotopic_nil_copy_cons (congrArg (compIncl σ) e) h hVP.symm
    refine ⟨q0.copy eu.symm ev.symm, ?_⟩
    exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
      (retractConnector_ret hσ hune) (retractConnector_line hσ hv)
  · have hcoll : FlipColl σ u.1 P.1.1 :=
      flipColl_of_le_line hline ⟨hUpt, le_of_lt huv⟩ ⟨hPpt, le_of_lt hP_lt⟩ hz
    have hUW : (compGraph σ).Adj U0 V0 := Or.inr ⟨hUpt, hPpt, hcoll⟩
    let q0 : (compGraph σ).Walk U0 V0 := Walk.cons hUW Walk.nil
    let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.nil
    let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.cons hVP.symm Walk.nil
    have H0 : Homotopic (cu0.append
        (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
          (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
        ((Walk.cons h Walk.nil).append cv0) := by
      dsimp only [cu0, cv0, q0]
      erw [substituteWalk_cons, substituteWalk_nil]
      have hwalk : ((Walk.cons h Walk.nil).append (Walk.cons hVP.symm Walk.nil) :
          (flagGraph σ 3).Walk u P.1) =
          Walk.cons (Or.inl huv) (Walk.cons (Or.inr (Or.inl hP_lt)) Walk.nil) := by
        erw [Walk.cons_append, Walk.nil_append]
      erw [hwalk]
      simpa only [Walk.nil_append, Walk.append_nil] using
        expandCompEdge_via_line hv huv hP_lt hUW
    refine ⟨q0.copy eu.symm ev.symm, ?_⟩
    exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
      (retractConnector_ret hσ hune) (retractConnector_line hσ hv)

theorem exists_reduce_line_point (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hu : Module.finrank K u.1 = 2) (hv1 : Module.finrank K v.1 = 1)
    (h : (flagGraph σ 3).Adj u v) (hvu : v.1 < u.1) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  have hvne : Module.finrank K v.1 ≠ 2 := by omega
  let P : CompVert σ := chosenLinePoint hσ u hu
  let U0 : CompVert σ := P
  let V0 : CompVert σ := ⟨v, hvne⟩
  have eu : retractCompVert hσ u = U0 := retractCompVert_line hσ hu
  have ev : retractCompVert hσ v = V0 := retractCompVert_ret hσ hvne
  have hUP : (flagGraph σ 3).Adj P.1 u := chosenLinePoint_adj hσ u hu
  have hP_lt : P.1.1 < u.1 := chosenLinePoint_lt hσ u hu
  have hPfin : Module.finrank K P.1.1 = 1 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt hP_lt
    rcases P.1.finrank_one_two_four (σ := σ) with h1 | h2 | h4
    · exact h1
    · exact absurd h2 P.2
    · omega
  have hPpt : IsFlipflopPt σ P.1.1 := ⟨P.1.2.1, hPfin⟩
  have hVpt : IsFlipflopPt σ v.1 := ⟨v.2.1, hv1⟩
  have hline : IsFlipLine σ u.1 := ⟨u.2.1, hu⟩
  by_cases hz : v.1 = P.1.1
  · have e : U0 = V0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz.symm
    let q0 : (compGraph σ).Walk U0 V0 :=
      (Walk.nil : (compGraph σ).Walk U0 U0).copy rfl e
    let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.cons hUP.symm Walk.nil
    let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.nil
    have H0 : Homotopic (cu0.append
        (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
          (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
        ((Walk.cons h Walk.nil).append cv0) := by
      dsimp only [cu0, cv0, q0]
      have hq0 : substituteWalk (compIncl σ)
          (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e)
          ((Walk.nil : (compGraph σ).Walk U0 U0).copy rfl e) =
          (Walk.nil : (flagGraph σ 3).Walk U0.1 U0.1).copy rfl
            (congrArg (compIncl σ) e) := by
        erw [substituteWalk_copy]
        rfl
      erw [hq0]
      have h1 := homotopic_append_nil_copy (Walk.cons hUP.symm Walk.nil)
        (congrArg (compIncl σ) e)
      have h3 : Homotopic ((Walk.cons hUP.symm Walk.nil).copy rfl
          (congrArg (compIncl σ) e))
          (Walk.cons hUP.symm ((Walk.nil : (flagGraph σ 3).Walk U0.1 U0.1).copy rfl
            (congrArg (compIncl σ) e))) := by
        rw [Walk.copy_cons]
      have h2 := homotopic_cons_copy_nil hUP.symm h (congrArg (compIncl σ) e)
      simpa only [Walk.append_nil] using h1.trans (h3.trans h2)
    refine ⟨q0.copy eu.symm ev.symm, ?_⟩
    exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
      (retractConnector_line hσ hu) (retractConnector_ret hσ hvne)
  · have hcoll : FlipColl σ P.1.1 v.1 :=
      flipColl_of_le_line hline ⟨hPpt, le_of_lt hP_lt⟩ ⟨hVpt, le_of_lt hvu⟩ (Ne.symm hz)
    have hUW : (compGraph σ).Adj U0 V0 := Or.inr ⟨hPpt, hVpt, hcoll⟩
    let q0 : (compGraph σ).Walk U0 V0 := Walk.cons hUW Walk.nil
    let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.cons hUP.symm Walk.nil
    let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.nil
    have H0 : Homotopic (cu0.append
        (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
          (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
        ((Walk.cons h Walk.nil).append cv0) := by
      dsimp only [cu0, cv0, q0]
      erw [substituteWalk_cons, substituteWalk_nil]
      have hPW : (flagGraph σ 3).Adj P.1 u := Or.inl hP_lt
      have hVU : (flagGraph σ 3).Adj u v := Or.inr (Or.inl hvu)
      have hback : Homotopic (Walk.cons hUP.symm (Walk.cons hPW Walk.nil)) Walk.nil := by
        rw [show hPW = hUP.symm.symm from Subsingleton.elim _ _]
        exact homotopic_cons_cons_nil hUP.symm
      have h2 : Homotopic (Walk.cons hUP.symm (Walk.cons hPW (Walk.cons hVU Walk.nil)))
          (Walk.cons hVU Walk.nil) := by
        simpa only [Walk.nil_append, Walk.cons_append] using
          hback.append_right (Walk.cons hVU Walk.nil)
      have h1 := expandCompEdge_via_line hu hP_lt hvu hUW
      have h3 : Homotopic
          (Walk.cons hUP.symm (Walk.cons (Or.inl hP_lt)
            (Walk.cons (Or.inr (Or.inl hvu)) Walk.nil)))
          (Walk.cons hVU Walk.nil) := by
        simpa only [show (Or.inl hP_lt : (flagGraph σ 3).Adj P.1 u) = hPW from
            Subsingleton.elim _ _,
          show (Or.inr (Or.inl hvu) : (flagGraph σ 3).Adj u v) = hVU from
            Subsingleton.elim _ _] using h2
      simpa only [Walk.nil_append, Walk.append_nil, Walk.cons_append,
        show hVU = h from Subsingleton.elim _ _] using
        (h1.append_left (Walk.cons hUP.symm Walk.nil)).trans h3
    refine ⟨q0.copy eu.symm ev.symm, ?_⟩
    exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
      (retractConnector_line hσ hu) (retractConnector_ret hσ hvne)

theorem exists_reduce (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj u v) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  classical
  by_cases hu : Module.finrank K u.1 = 2
  · by_cases hv : Module.finrank K v.1 = 2
    · exact absurd hv (flagGraph_not_two_two h hu)
    · have hv14 : Module.finrank K v.1 = 1 ∨ Module.finrank K v.1 = 4 := by
        rcases v.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hv
        · exact Or.inr h4
      rcases hv14 with hv1 | hv4
      · have hvu : v.1 < u.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · exact hgt
          · omega
        exact exists_reduce_line_point hσ hu hv1 h hvu
      · have huv : u.1 < v.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · exact hlt
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        exact exists_reduce_line_solid hσ hu hv4 h huv
  · by_cases hv : Module.finrank K v.1 = 2
    · have hu14 : Module.finrank K u.1 = 1 ∨ Module.finrank K u.1 = 4 := by
        rcases u.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hu
        · exact Or.inr h4
      rcases hu14 with hu1 | hu4
      · have huv : u.1 < v.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · exact hlt
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        exact exists_reduce_point_line hσ hu1 hv h huv
      · have hvu : v.1 < u.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · exact hgt
          · omega
        exact exists_reduce_solid_line hσ hu4 hv h hvu
    · have hu14 : Module.finrank K u.1 = 1 ∨ Module.finrank K u.1 = 4 := by
        rcases u.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hu
        · exact Or.inr h4
      have hv14 : Module.finrank K v.1 = 1 ∨ Module.finrank K v.1 = 4 := by
        rcases v.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hv
        · exact Or.inr h4
      rcases hu14 with hu1 | hu4
      · rcases hv14 with hv1 | hv4
        · exfalso
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        · exact exists_reduce_retained hσ hu hv h
      · rcases hv14 with hv1 | hv4
        · exact exists_reduce_retained hσ hu hv h
        · exact exists_reduce_retained hσ hu hv h

noncomputable def reduceCompEdge (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj u v) :
    (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v) :=
  (exists_reduce hσ h).choose

theorem reduceCompEdge_spec (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj u v) : CompHedge hσ h (reduceCompEdge hσ h) :=
  (exists_reduce hσ h).choose_spec

theorem flagGraph_three_connected_of_compGraph {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hc : (compGraph σ).Connected) :
    (flagGraph σ 3).Connected :=
  connected_of_walk_cover (compIncl σ) (retractCompVert hσ)
    (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e)
    (retractConnector hσ) hc

theorem flagGraph_three_of_compGraph {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hc : (compGraph σ).Connected)
    (ht : CFSG.Monster.B.Recog.Triangulable (compGraph σ)) :
    (flagGraph σ 3).Connected ∧ CFSG.Monster.B.Recog.Triangulable (flagGraph σ 3) :=
  ⟨flagGraph_three_connected_of_compGraph hσ hc,
    triangulable_of_walk_retraction (compIncl σ) (retractCompVert hσ)
      (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge e)
      (fun {U W : FlagVert σ 3} (e : (flagGraph σ 3).Adj U W) => reduceCompEdge hσ e)
      (retractConnector hσ)
      (fun {U W : CompVert σ} (e : (compGraph σ).Adj U W) => expandCompEdge_backtrack e)
      (fun {U V W : CompVert σ} (huv : (compGraph σ).Adj U V)
          (hvw : (compGraph σ).Adj V W) (hwu : (compGraph σ).Adj W U) =>
        expandCompEdge_triangle hσ hK huv hvw hwu)
      (fun {U W : FlagVert σ 3} (e : (flagGraph σ 3).Adj U W) => reduceCompEdge_spec hσ e)
      ht⟩

end CFSG.ClassicalInvolution.PhanDn

end
