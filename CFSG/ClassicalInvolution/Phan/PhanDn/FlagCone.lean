module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagLift
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import CFSG.ClassicalInvolution.Phan.Geometry.ConeQuad
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoHermitian
import CFSG.ClassicalGroups.Orthogonal.LineStabilizer
import CFSG.Monster.B.GSide.HomotopyLocal

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
open CFSG.Monster.B.Recog CFSG.Monster.B.GSide

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

variable (σ m) in
@[expose] def ConeStep (Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (y y' : FlipPt σ (m + 1)) : Prop :=
  ∃ T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K), IsFlipflopSub σ T ∧ T ≤ Y ∧
    Module.finrank K T + 2 ≤ m ∧ y.1 ≤ T ∧ y'.1 ≤ T

variable (σ m) in
@[expose] def ConeConnected (Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)) : Prop :=
  ∀ y y' : FlipPt σ (m + 1), y.1 ≤ Y → y'.1 ≤ Y →
    Relation.ReflTransGen (ConeStep σ m Y) y y'

theorem ConeStep.symm {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    {y y' : FlipPt σ (m + 1)} (h : ConeStep σ m Y y y') : ConeStep σ m Y y' y := by
  obtain ⟨T, hT, hTY, hdim, hy, hy'⟩ := h
  exact ⟨T, hT, hTY, hdim, hy', hy⟩

theorem flipHerm_map_linearEquiv {n : ℕ} (L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (hQ : ∀ y, quadPlus n K (L y) = quadPlus n K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y)) (x y : Fin n ⊕ Fin n → K) :
    flipHerm σ (L x) (L y) = flipHerm σ x y := by
  change polar (quadPlus n K) (L x) (dFlip σ (L y)) = polar (quadPlus n K) x (dFlip σ y)
  rw [← hL y, CFSG.ClassicalGroups.Orthogonal.polar_map_of_linearIsometry (quadPlus n K) L hQ]

private theorem isFlipflopSub_map_linearEquiv
    (L : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hQ : ∀ y, quadPlus (m + 1) K (L y) = quadPlus (m + 1) K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    {U : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} (hU : IsFlipflopSub σ U) :
    IsFlipflopSub σ (U.map L.toLinearMap) := by
  have hH := flipHerm_map_linearEquiv (σ := σ) L hQ hL
  constructor
  · intro u hu
    obtain ⟨t, ht, htu⟩ := Submodule.mem_map.mp hu
    subst htu
    exact (hQ t).trans (hU.total t ht)
  · intro u hu hper
    obtain ⟨t, ht, htu⟩ := Submodule.mem_map.mp hu
    subst htu
    have ht0 : t = 0 := hU.nondeg t ht fun v hv => by
      have h := hper (L v) (Submodule.mem_map_of_mem hv)
      exact (hH t v).symm.trans h
    rw [ht0, map_zero]

private theorem isFlipflopPt_map_linearEquiv
    (L : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hQ : ∀ y, quadPlus (m + 1) K (L y) = quadPlus (m + 1) K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    {p : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} (hp : IsFlipflopPt σ p) :
    IsFlipflopPt σ (p.map L.toLinearMap) := by
  obtain ⟨v, rfl, hvq, hvh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h, flipHerm_zero_right])
  have hLv0 : L v ≠ 0 := fun h => hv0 (by simpa using congrArg L.symm h)
  have hH : flipHerm σ (L v) (L v) = flipHerm σ v v :=
    flipHerm_map_linearEquiv L hQ hL v v
  rw [Submodule.map_span, Set.image_singleton]
  refine (isFlipflopPt_span_singleton_iff hLv0).mpr ⟨?_, ?_⟩
  · exact (hQ v).trans hvq
  · intro hzero
    exact hvh (by rwa [hH] at hzero)

private theorem ConeStep.map_linearEquiv
    (L : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hQ : ∀ y, quadPlus (m + 1) K (L y) = quadPlus (m + 1) K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y))
    {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} {y y' : FlipPt σ (m + 1)}
    (h : ConeStep σ m Y y y') :
    ConeStep σ m (Y.map L.toLinearMap)
      ⟨y.1.map L.toLinearMap, isFlipflopPt_map_linearEquiv L hQ hL y.2⟩
      ⟨y'.1.map L.toLinearMap, isFlipflopPt_map_linearEquiv L hQ hL y'.2⟩ := by
  obtain ⟨T, hT, hTY, hdim, hyT, hy'T⟩ := h
  exact ⟨T.map L.toLinearMap, isFlipflopSub_map_linearEquiv L hQ hL hT,
    Submodule.map_mono hTY,
    by rw [LinearEquiv.finrank_map_eq]; exact hdim,
    Submodule.map_mono hyT, Submodule.map_mono hy'T⟩

theorem ConeConnected.map_linearEquiv (hσ : ∀ x, σ (σ x) = x)
    (L : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hQ : ∀ y, quadPlus (m + 1) K (L y) = quadPlus (m + 1) K y)
    (hL : ∀ y, L (dFlip σ y) = dFlip σ (L y)) {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (h : ConeConnected σ m Y) : ConeConnected σ m (Y.map L.toLinearMap) := by
  have hQs : ∀ y, quadPlus (m + 1) K (L.symm y) = quadPlus (m + 1) K y := by
    intro y
    simpa using (hQ (L.symm y)).symm
  have hLs : ∀ y, L.symm (dFlip σ y) = dFlip σ (L.symm y) := by
    intro y
    have h := congrArg (fun z => L.symm z) (hL (L.symm (dFlip σ y)))
    rw [L.symm_apply_apply, L.apply_symm_apply] at h
    have h' := congrArg (dFlip σ) h
    rw [dFlip_dFlip hσ, dFlip_dFlip hσ] at h'
    exact h'
  let fL : FlipPt σ (m + 1) → FlipPt σ (m + 1) := fun p =>
    ⟨p.1.map L.toLinearMap, isFlipflopPt_map_linearEquiv L hQ hL p.2⟩
  let fS : FlipPt σ (m + 1) → FlipPt σ (m + 1) := fun p =>
    ⟨p.1.map L.symm.toLinearMap, isFlipflopPt_map_linearEquiv L.symm hQs hLs p.2⟩
  intro y y' hy hy'
  have hyS : (fS y).1 ≤ Y := by
    have hle := Submodule.map_mono (f := L.symm.toLinearMap) hy
    rwa [show (Y.map L.toLinearMap).map L.symm.toLinearMap = Y from by
      rw [← Submodule.map_comp, L.symm_comp, Submodule.map_id]] at hle
  have hyS' : (fS y').1 ≤ Y := by
    have hle := Submodule.map_mono (f := L.symm.toLinearMap) hy'
    rwa [show (Y.map L.toLinearMap).map L.symm.toLinearMap = Y from by
      rw [← Submodule.map_comp, L.symm_comp, Submodule.map_id]] at hle
  have hchain := h (fS y) (fS y') hyS hyS'
  have hmap : Relation.ReflTransGen (ConeStep σ m (Y.map L.toLinearMap))
      (fL (fS y)) (fL (fS y')) :=
    Relation.ReflTransGen.lift fL
      (fun p q hpq => ConeStep.map_linearEquiv L hQ hL hpq) (fS y) (fS y') hchain
  have hfy : fL (fS y) = y := Subtype.ext (by
    change (y.1.map L.symm.toLinearMap).map L.toLinearMap = y.1
    rw [← Submodule.map_comp, L.comp_symm, Submodule.map_id])
  have hfy' : fL (fS y') = y' := Subtype.ext (by
    change (y'.1.map L.symm.toLinearMap).map L.toLinearMap = y'.1
    rw [← Submodule.map_comp, L.comp_symm, Submodule.map_id])
  simpa [hfy, hfy'] using hmap

private theorem flagGraph_adj_of_lt {U W : FlagVert σ m} (h : U.1 < W.1) :
    (flagGraph σ m).Adj U W :=
  Or.inl h

private theorem flagGraph_adj_of_gt {U W : FlagVert σ m} (h : W.1 < U.1) :
    (flagGraph σ m).Adj U W :=
  Or.inr (Or.inl h)

private theorem flagGraph_adj_of_le_of_finrank_lt {U W : FlagVert σ m}
    (hle : U.1 ≤ W.1) (hlt : Module.finrank K U.1 < Module.finrank K W.1) :
    (flagGraph σ m).Adj U W :=
  flagGraph_adj_of_lt (Submodule.lt_of_le_of_finrank_lt_finrank hle hlt)

private theorem two_le_finrank_of_two_distinct_points_le
    {y y' : FlipPt σ (m + 1)}
    {T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hy : y ≠ y') (hyT : y.1 ≤ T) (hy'T : y'.1 ≤ T) :
    2 ≤ Module.finrank K T := by
  by_contra hlt
  have hy1 : Module.finrank K y.1 = 1 := y.2.finrank_eq_one
  have hy'1 : Module.finrank K y'.1 = 1 := y'.2.finrank_eq_one
  have hT1 : Module.finrank K T = 1 := by
    have hge : 1 ≤ Module.finrank K T := by
      have h := Submodule.finrank_mono hyT
      omega
    omega
  have hy_eq : y.1 = T := by
    refine Submodule.eq_of_le_of_finrank_eq hyT ?_
    omega
  have hy'_eq : y'.1 = T := by
    refine Submodule.eq_of_le_of_finrank_eq hy'T ?_
    omega
  exact hy (Subtype.ext (hy_eq.trans hy'_eq.symm))

private theorem finrank_sup_eq_finrank_add_of_isFlipflopSub (hσ : ∀ x, σ (σ x) = x)
    {U T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hU : IsFlipflopSub σ U) (hT : IsFlipflopSub σ T)
    (hf : U ≤ qPerp (m + 1) K T) (hh : U ≤ flipOrth σ T) :
    Module.finrank K ↥(U ⊔ T) = Module.finrank K U + Module.finrank K T := by
  have hdisj := (IsFlipflopSub.sup_of_orth hσ hU hT hf hh).2
  have h := Submodule.finrank_sup_add_finrank_inf_eq U T
  rw [hdisj.eq_bot, finrank_bot, add_zero] at h
  exact h

private theorem ConeStep.isFlipflopSub_sup_and_finrank (hσ : ∀ x, σ (σ x) = x)
    {a c : FlipPt σ (m + 1)} {T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : IsFlipflopSub σ T)
    (hTE : T ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)) :
    IsFlipflopSub σ (a.1 ⊔ T) ∧ IsFlipflopSub σ (c.1 ⊔ T) ∧
      Module.finrank K ↥(a.1 ⊔ T) = Module.finrank K T + 1 ∧
      Module.finrank K ↥(c.1 ⊔ T) = Module.finrank K T + 1 := by
  have hTq : T ≤ qPerp (m + 1) K (a.1 ⊔ c.1) := le_trans hTE inf_le_left
  have hTh : T ≤ flipOrth σ (a.1 ⊔ c.1) := le_trans hTE inf_le_right
  have haq : a.1 ≤ qPerp (m + 1) K T := by
    intro x hx
    rw [mem_qPerp]
    intro t ht
    rw [polar_comm]
    exact (mem_qPerp.mp (hTq ht)) x (Submodule.mem_sup_left hx)
  have hah : a.1 ≤ flipOrth σ T := by
    intro x hx
    rw [mem_flipOrth]
    intro t ht
    exact (flipHerm_eq_zero_iff hσ).mpr
      ((mem_flipOrth.mp (hTh ht)) x (Submodule.mem_sup_left hx))
  have hcq : c.1 ≤ qPerp (m + 1) K T := by
    intro x hx
    rw [mem_qPerp]
    intro t ht
    rw [polar_comm]
    exact (mem_qPerp.mp (hTq ht)) x (Submodule.mem_sup_right hx)
  have hch : c.1 ≤ flipOrth σ T := by
    intro x hx
    rw [mem_flipOrth]
    intro t ht
    exact (flipHerm_eq_zero_iff hσ).mpr
      ((mem_flipOrth.mp (hTh ht)) x (Submodule.mem_sup_right hx))
  have hA : IsFlipflopSub σ (a.1 ⊔ T) :=
    (IsFlipflopSub.sup_of_orth hσ a.2.isFlipflopSub hT haq hah).1
  have hC : IsFlipflopSub σ (c.1 ⊔ T) :=
    (IsFlipflopSub.sup_of_orth hσ c.2.isFlipflopSub hT hcq hch).1
  have hA_fin : Module.finrank K ↥(a.1 ⊔ T) = Module.finrank K T + 1 := by
    have h := finrank_sup_eq_finrank_add_of_isFlipflopSub hσ a.2.isFlipflopSub hT haq hah
    rw [a.2.finrank_eq_one] at h
    omega
  have hC_fin : Module.finrank K ↥(c.1 ⊔ T) = Module.finrank K T + 1 := by
    have h := finrank_sup_eq_finrank_add_of_isFlipflopSub hσ c.2.isFlipflopSub hT hcq hch
    rw [c.2.finrank_eq_one] at h
    omega
  exact ⟨hA, hC, hA_fin, hC_fin⟩

private theorem ConeStep.exists_coneVerts (hσ : ∀ x, σ (σ x) = x) (hm : 3 ≤ m)
    {a c y y' : FlipPt σ (m + 1)}
    {T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : IsFlipflopSub σ T)
    (hTE : T ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))
    (hTdim : Module.finrank K T + 2 ≤ m) (hyT : y.1 ≤ T) (hy'T : y'.1 ≤ T)
    (hy : y ≠ y') :
    ∃ Tp Ap Cp : FlagVert σ m,
      y.1 ≤ Tp.1 ∧ y'.1 ≤ Tp.1 ∧ a.1 ≤ Ap.1 ∧ c.1 ≤ Cp.1 ∧
      Tp.1 ≤ Ap.1 ∧ Tp.1 ≤ Cp.1 ∧
      Module.finrank K Tp.1 < Module.finrank K Ap.1 ∧
      Module.finrank K Tp.1 < Module.finrank K Cp.1 ∧
      2 < Module.finrank K Ap.1 ∧ 2 < Module.finrank K Cp.1 ∧
      (flagGraph σ m).Adj (ptVert hm y) Tp ∧
      (flagGraph σ m).Adj Tp (ptVert hm y') := by
  classical
  obtain ⟨hAsub, hCsub, hA_fin, hC_fin⟩ := ConeStep.isFlipflopSub_sup_and_finrank hσ hT hTE
  have hT_two := two_le_finrank_of_two_distinct_points_le hy hyT hy'T
  have hT_ne : T ≠ ⊥ := by
    intro hbot
    have h := hT_two
    rw [hbot, finrank_bot] at h
    omega
  have hT_dim_ne : Module.finrank K T ≠ m := by
    have h := hTdim
    omega
  have hA_ne : a.1 ⊔ T ≠ ⊥ := by
    intro hbot
    have h := hA_fin
    rw [hbot, finrank_bot] at h
    omega
  have hA_dim_ne : Module.finrank K ↥(a.1 ⊔ T) ≠ m := by omega
  have hC_ne : c.1 ⊔ T ≠ ⊥ := by
    intro hbot
    have h := hC_fin
    rw [hbot, finrank_bot] at h
    omega
  have hC_dim_ne : Module.finrank K ↥(c.1 ⊔ T) ≠ m := by omega
  have hA_gt_two : 2 < Module.finrank K ↥(a.1 ⊔ T) := by omega
  have hC_gt_two : 2 < Module.finrank K ↥(c.1 ⊔ T) := by omega
  have hyT_lt : y.1 < T :=
    lt_of_le_of_ne hyT fun hEq => by
      have h1 : Module.finrank K T = 1 := by rw [← hEq, y.2.finrank_eq_one]
      omega
  have hy'T_lt : y'.1 < T :=
    lt_of_le_of_ne hy'T fun hEq => by
      have h1 : Module.finrank K T = 1 := by rw [← hEq, y'.2.finrank_eq_one]
      omega
  let Tp : FlagVert σ m := ⟨T, hT, hT_ne, hT_dim_ne⟩
  let Ap : FlagVert σ m := ⟨a.1 ⊔ T, hAsub, hA_ne, hA_dim_ne⟩
  let Cp : FlagVert σ m := ⟨c.1 ⊔ T, hCsub, hC_ne, hC_dim_ne⟩
  have hyT_adj : (flagGraph σ m).Adj (ptVert hm y) Tp :=
    flagGraph_adj_of_lt (show (ptVert hm y).1 < Tp.1 from hyT_lt)
  have hTy'_adj : (flagGraph σ m).Adj Tp (ptVert hm y') :=
    flagGraph_adj_of_gt (show (ptVert hm y').1 < Tp.1 from hy'T_lt)
  refine ⟨Tp, Ap, Cp, hyT, hy'T, le_sup_left, le_sup_left, le_sup_right, le_sup_right,
    ?_, ?_, ?_, ?_, hyT_adj, hTy'_adj⟩
  · change Module.finrank K T < Module.finrank K ↥(a.1 ⊔ T)
    omega
  · change Module.finrank K T < Module.finrank K ↥(c.1 ⊔ T)
    omega
  · change 2 < Module.finrank K ↥(a.1 ⊔ T)
    omega
  · change 2 < Module.finrank K ↥(c.1 ⊔ T)
    omega

private theorem homotopic_liftWalk_cons_cons_append_reverse_of_cone (hm : 3 ≤ m)
    {y c y' : FlipPt σ (m + 1)} (h₂ : (flipGraph σ (m + 1)).Adj y c)
    (h₃ : (flipGraph σ (m + 1)).Adj c y') {Tp Cp : FlagVert σ m}
    (hyT : y.1 ≤ Tp.1) (hy'T : y'.1 ≤ Tp.1) (hcT : c.1 ≤ Cp.1)
    (hT : Tp.1 ≤ Cp.1) (hT_lt : Module.finrank K Tp.1 < Module.finrank K Cp.1)
    (hC_gt_two : 2 < Module.finrank K Cp.1)
    (hyT_adj : (flagGraph σ m).Adj (ptVert hm y) Tp)
    (hTy'_adj : (flagGraph σ m).Adj Tp (ptVert hm y')) :
    Homotopic ((liftWalk hm (.cons h₂ (.cons h₃ .nil))).append
      ((.cons hyT_adj (.cons hTy'_adj .nil) :
        (flagGraph σ m).Walk (ptVert hm y) (ptVert hm y'))).reverse) .nil := by
  have hsuppC : ∀ x ∈ (SimpleGraph.Walk.cons h₂
      (SimpleGraph.Walk.cons h₃ SimpleGraph.Walk.nil)).support, x.1 ≤ Cp.1 := by
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_trans hyT hT
    · exact hcT
    · exact le_trans hy'T hT
  refine homotopic_nil_of_forall_adj (z := Cp) _ ?_
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · exact flagGraph_adj_of_le_of_finrank_lt
      (le_of_mem_support_liftWalk hm _ hsuppC hx)
      (lt_of_le_of_lt (finrank_le_two_of_mem_support_liftWalk hm _ hx) hC_gt_two)
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    have hx' : x = ptVert hm y ∨ x = Tp ∨ x = ptVert hm y' := by simpa using hx
    rcases hx' with rfl | rfl | rfl
    · refine flagGraph_adj_of_le_of_finrank_lt (le_trans hyT hT) ?_
      change Module.finrank K y.1 < Module.finrank K Cp.1
      rw [y.2.finrank_eq_one]
      omega
    · exact flagGraph_adj_of_le_of_finrank_lt hT hT_lt
    · refine flagGraph_adj_of_le_of_finrank_lt (le_trans hy'T hT) ?_
      change Module.finrank K y'.1 < Module.finrank K Cp.1
      rw [y'.2.finrank_eq_one]
      omega

private theorem homotopic_liftWalk_cons_append_cons_of_cone (hm : 3 ≤ m)
    {a y y' : FlipPt σ (m + 1)} (h₁ : (flipGraph σ (m + 1)).Adj a y)
    (h₄ : (flipGraph σ (m + 1)).Adj y' a) {Tp Ap : FlagVert σ m}
    (hyT : y.1 ≤ Tp.1) (hy'T : y'.1 ≤ Tp.1) (haT : a.1 ≤ Ap.1)
    (hT : Tp.1 ≤ Ap.1) (hT_lt : Module.finrank K Tp.1 < Module.finrank K Ap.1)
    (hA_gt_two : 2 < Module.finrank K Ap.1)
    (hyT_adj : (flagGraph σ m).Adj (ptVert hm y) Tp)
    (hTy'_adj : (flagGraph σ m).Adj Tp (ptVert hm y')) :
    Homotopic ((liftWalk hm (.cons h₁ .nil)).append
      (((.cons hyT_adj (.cons hTy'_adj .nil) :
        (flagGraph σ m).Walk (ptVert hm y) (ptVert hm y'))).append
        (liftWalk hm (.cons h₄ .nil)))) .nil := by
  have hsupp₁ : ∀ x ∈ (SimpleGraph.Walk.cons h₁ SimpleGraph.Walk.nil).support,
      x.1 ≤ Ap.1 := by
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact haT
    · exact le_trans hyT hT
  have hsupp₄ : ∀ x ∈ (SimpleGraph.Walk.cons h₄ SimpleGraph.Walk.nil).support,
      x.1 ≤ Ap.1 := by
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact le_trans hy'T hT
    · exact haT
  refine homotopic_nil_of_forall_adj (z := Ap) _ ?_
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · exact flagGraph_adj_of_le_of_finrank_lt
      (le_of_mem_support_liftWalk hm _ hsupp₁ hx)
      (lt_of_le_of_lt (finrank_le_two_of_mem_support_liftWalk hm _ hx) hA_gt_two)
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · have hx' : x = ptVert hm y ∨ x = Tp ∨ x = ptVert hm y' := by simpa using hx
      rcases hx' with rfl | rfl | rfl
      · refine flagGraph_adj_of_le_of_finrank_lt (le_trans hyT hT) ?_
        change Module.finrank K y.1 < Module.finrank K Ap.1
        rw [y.2.finrank_eq_one]
        omega
      · exact flagGraph_adj_of_le_of_finrank_lt hT hT_lt
      · refine flagGraph_adj_of_le_of_finrank_lt (le_trans hy'T hT) ?_
        change Module.finrank K y'.1 < Module.finrank K Ap.1
        rw [y'.2.finrank_eq_one]
        omega
    · exact flagGraph_adj_of_le_of_finrank_lt
        (le_of_mem_support_liftWalk hm _ hsupp₄ hx)
        (lt_of_le_of_lt (finrank_le_two_of_mem_support_liftWalk hm _ hx) hA_gt_two)

theorem quadWalk_mem_flagNullWalks_of_coneStep (hσ : ∀ x, σ (σ x) = x) (hm : 3 ≤ m)
    {a y c y' : FlipPt σ (m + 1)} (h₁ : (flipGraph σ (m + 1)).Adj a y)
    (h₂ : (flipGraph σ (m + 1)).Adj y c) (h₃ : (flipGraph σ (m + 1)).Adj c y')
    (h₄ : (flipGraph σ (m + 1)).Adj y' a)
    (h : ConeStep σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)) y y') :
    quadWalk h₁ h₂ h₃ h₄ ∈ flagNullWalks σ hm a := by
  classical
  by_cases hy : y = y'
  · subst y'
    exact homotopic_liftWalk_of_cycleHomotopic hm
      (cycleHomotopic_quadWalk_of_eq_fourth (flagNullWalks σ hm) h₁ h₂ h₃ h₄)
  · obtain ⟨T, hT, hTE, hTdim, hyT, hy'T⟩ := h
    obtain ⟨Tp, Ap, Cp, hyTp, hy'Tp, haAp, hcCp, hT_A, hT_C, hT_lt_A, hT_lt_C,
      hA_gt_two, hC_gt_two, hyT_adj, hTy'_adj⟩ :=
      ConeStep.exists_coneVerts hσ hm hT hTE hTdim hyT hy'T hy
    have hnullC := homotopic_liftWalk_cons_cons_append_reverse_of_cone hm h₂ h₃
      hyTp hy'Tp hcCp hT_C hT_lt_C hC_gt_two hyT_adj hTy'_adj
    have hnullA := homotopic_liftWalk_cons_append_cons_of_cone hm h₁ h₄
      hyTp hy'Tp haAp hT_A hT_lt_A hA_gt_two hyT_adj hTy'_adj
    have hmiddle : Homotopic (liftWalk hm (.cons h₂ (.cons h₃ .nil)))
        ((.cons hyT_adj (.cons hTy'_adj .nil) :
          (flagGraph σ m).Walk (ptVert hm y) (ptVert hm y'))) :=
      homotopic_iff_append_reverse_nil.mpr hnullC
    have hdecomp : liftWalk hm (quadWalk h₁ h₂ h₃ h₄) =
        (liftWalk hm (.cons h₁ .nil)).append
          ((liftWalk hm (.cons h₂ (.cons h₃ .nil))).append
            (liftWalk hm (.cons h₄ .nil))) := by
      rw [show quadWalk h₁ h₂ h₃ h₄ =
        (SimpleGraph.Walk.cons h₁ SimpleGraph.Walk.nil).append
          ((SimpleGraph.Walk.cons h₂ (SimpleGraph.Walk.cons h₃ SimpleGraph.Walk.nil)).append
            (SimpleGraph.Walk.cons h₄ SimpleGraph.Walk.nil)) from rfl]
      rw [liftWalk_append, liftWalk_append]
    have hstep : Homotopic (liftWalk hm (quadWalk h₁ h₂ h₃ h₄))
        ((liftWalk hm (.cons h₁ .nil)).append
          (((.cons hyT_adj (.cons hTy'_adj .nil) :
            (flagGraph σ m).Walk (ptVert hm y) (ptVert hm y'))).append
            (liftWalk hm (.cons h₄ .nil)))) := by
      rw [hdecomp]
      exact (hmiddle.append_right (liftWalk hm (.cons h₄ .nil))).append_left
        (liftWalk hm (.cons h₁ .nil))
    exact hstep.trans hnullA

theorem cycleHomotopic_quadWalk_of_reflTransGen (hσ : ∀ x, σ (σ x) = x) (hm : 3 ≤ m)
    {a y c y' : FlipPt σ (m + 1)} (h₁ : (flipGraph σ (m + 1)).Adj a y)
    (h₂ : (flipGraph σ (m + 1)).Adj y c) (h₃ : (flipGraph σ (m + 1)).Adj c y')
    (h₄ : (flipGraph σ (m + 1)).Adj y' a)
    (h : Relation.ReflTransGen
      (ConeStep σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))) y y') :
    CycleHomotopic (flagNullWalks σ hm) (quadWalk h₁ h₂ h₃ h₄) .nil := by
  classical
  revert h₃ h₄
  refine Relation.ReflTransGen.rec (motive := fun z _ =>
    ∀ (h₃ : (flipGraph σ (m + 1)).Adj c z) (h₄ : (flipGraph σ (m + 1)).Adj z a),
      CycleHomotopic (flagNullWalks σ hm) (quadWalk h₁ h₂ h₃ h₄) .nil) ?_ ?_ h
  · intro h₃ h₄
    exact cycleHomotopic_quadWalk_of_eq_fourth (flagNullWalks σ hm) h₁ h₂ h₃ h₄
  · intro b z hyb hbz ih h₃ h₄
    have hbz' := hbz
    obtain ⟨T, -, hTE, -, hbT, -⟩ := hbz
    have hbE : b.1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) :=
      le_trans hbT hTE
    have hbqa : b.1 ≤ qPerp (m + 1) K a.1 :=
      le_trans (le_trans hbE inf_le_left) (qPerp_antitone le_sup_left)
    have hbqc : b.1 ≤ qPerp (m + 1) K c.1 :=
      le_trans (le_trans hbE inf_le_left) (qPerp_antitone le_sup_right)
    have hbha : b.1 ≤ flipOrth σ a.1 :=
      le_trans (le_trans hbE inf_le_right) (by rw [flipOrth_sup]; exact inf_le_left)
    have hbhc : b.1 ≤ flipOrth σ c.1 :=
      le_trans (le_trans hbE inf_le_right) (by rw [flipOrth_sup]; exact inf_le_right)
    have hba : (flipGraph σ (m + 1)).Adj b a := flipColl_of_orth hσ b.2 a.2 hbqa hbha
    have hbc : (flipGraph σ (m + 1)).Adj b c := flipColl_of_orth hσ b.2 c.2 hbqc hbhc
    have hab : (flipGraph σ (m + 1)).Adj a b := hba.symm
    have hcb : (flipGraph σ (m + 1)).Adj c b := hbc.symm
    exact cycleHomotopic_quad_trans (flagNullWalks σ hm) h₁ h₂ hcb hba h₃ h₄
      (ih hcb hba)
      (cycleHomotopic_of_mem (flagNullWalks σ hm)
        (quadWalk_mem_flagNullWalks_of_coneStep hσ hm hab hbc h₃ h₄ hbz'))

private theorem cycleHomotopic_quadWalk_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 3 ≤ m)
    (hcone : ∀ a c : FlipPt σ (m + 1), a ≠ c → ¬ (flipGraph σ (m + 1)).Adj a c →
      ConeConnected σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)))
    {a b c d : FlipPt σ (m + 1)} (h₁ : (flipGraph σ (m + 1)).Adj a b)
    (h₂ : (flipGraph σ (m + 1)).Adj b c) (h₃ : (flipGraph σ (m + 1)).Adj c d)
    (h₄ : (flipGraph σ (m + 1)).Adj d a) :
    CycleHomotopic (flagNullWalks σ hm) (quadWalk h₁ h₂ h₃ h₄) .nil := by
  classical
  by_cases hac : a = c
  · subst c
    exact cycleHomotopic_quadWalk_of_eq_third (flagNullWalks σ hm) h₁ h₂ h₃ h₄
  · by_cases hadj : (flipGraph σ (m + 1)).Adj a c
    · exact cycleHomotopic_quadWalk_of_chord (flagNullWalks σ hm)
        (nullLen_three_flagNullWalks_of_card_eq_four hσ hK hm) h₁ h₂ h₃ h₄ hadj
    · have hbqa : b.1 ≤ qPerp (m + 1) K a.1 := h₁.symm.le_qPerp
      have hbqc : b.1 ≤ qPerp (m + 1) K c.1 := h₂.le_qPerp
      have hbha : b.1 ≤ flipOrth σ a.1 :=
        FlipColl.le_flipOrth_of_card_four hσ hK h₁.symm b.2 a.2
      have hbhc : b.1 ≤ flipOrth σ c.1 :=
        FlipColl.le_flipOrth_of_card_four hσ hK h₂ b.2 c.2
      have hbE : b.1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) := by
        refine le_inf ?_ ?_
        · rw [qPerp_sup]
          exact le_inf hbqa hbqc
        · rw [flipOrth_sup]
          exact le_inf hbha hbhc
      have hdqa : d.1 ≤ qPerp (m + 1) K a.1 := h₄.le_qPerp
      have hdqc : d.1 ≤ qPerp (m + 1) K c.1 := h₃.symm.le_qPerp
      have hdha : d.1 ≤ flipOrth σ a.1 :=
        FlipColl.le_flipOrth_of_card_four hσ hK h₄ d.2 a.2
      have hdhc : d.1 ≤ flipOrth σ c.1 :=
        FlipColl.le_flipOrth_of_card_four hσ hK h₃.symm d.2 c.2
      have hdE : d.1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) := by
        refine le_inf ?_ ?_
        · rw [qPerp_sup]
          exact le_inf hdqa hdqc
        · rw [flipOrth_sup]
          exact le_inf hdha hdhc
      exact cycleHomotopic_quadWalk_of_reflTransGen hσ.invol hm h₁ h₂ h₃ h₄
        (hcone a c hac hadj b d hbE hdE)

theorem nullLen_four_flagNullWalks_of_coneConnected [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 3 ≤ m)
    (hcone : ∀ a c : FlipPt σ (m + 1), a ≠ c → ¬ (flipGraph σ (m + 1)).Adj a c →
      ConeConnected σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))) :
    NullLen (flagNullWalks σ hm) 4 := by
  intro u p hp
  match u, p, hp with
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ .nil)), hp => simp at hp
  | _, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil))), _ =>
      exact cycleHomotopic_quadWalk_of_card_eq_four hσ hK hm hcone h₁ h₂ h₃ h₄
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))), hp =>
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

end CFSG.ClassicalInvolution.PhanDn
