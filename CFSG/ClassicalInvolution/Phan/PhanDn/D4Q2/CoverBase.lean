
module

public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.Solids
public import CFSG.Sporadic.SuzRecog.LevelTwoHomotopy
import all CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoCompressed

public section

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

open CFSG.ClassicalGroups.Unitary CFSG.Sporadic.SuzRecog
open CFSG.Sporadic.SuzRecog.ElimCert

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

section Codes

variable {ω : K} {F : Array (Array ℕ)}

private theorem d4v_pts_size (hT : Checks F) : (ptCodes ()).size = 2240 := by
  have h := hT.size
  change ((ptCodes ()).size == 2240 && F.size == 4480) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem d4v_frames_size (hT : Checks F) : F.size = 4480 := by
  have h := hT.size
  change ((ptCodes ()).size == 2240 && F.size == 4480) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem d4v_ptCodes_nodup : (ptCodes ()).toList.Nodup := by
  show ((Array.range 65536).filter _).toList.Nodup
  rw [Array.toList_filter, Array.toList_range]
  exact List.nodup_range.filter _

private theorem d4v_getElem!_eq_getElem {α : Type} [Inhabited α] (s : Array α) (i : ℕ)
    (h : i < s.size) : s[i]! = s[i]'h := by
  rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]

private theorem d4v_sub_lt {a : ℕ} (h : a < 6720) : a - 2240 < 4480 := by
  omega

private theorem d4v_sub_inj {a b : ℕ} (ha : 2240 ≤ a) (hb : 2240 ≤ b)
    (h : a - 2240 = b - 2240) : a = b := by
  omega

private theorem d4v_not_lt_add (j : ℕ) : ¬ 2240 + j < 2240 := by
  omega

private theorem d4v_occB_iff {s : Array ℕ} {y : ℕ} : occB s y = true ↔ y ∈ s := by
  rw [occB_iff]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [← hk', d4v_getElem!_eq_getElem s k hk]
    exact Array.getElem_mem hk
  · intro hy
    rw [Array.mem_iff_getElem] at hy
    obtain ⟨k, hk, hk'⟩ := hy
    exact ⟨k, hk, by rw [d4v_getElem!_eq_getElem s k hk, hk']⟩

omit [Finite K] in
private theorem d4v_finrank_pt (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {c : ℕ}
    (hc : c ∈ ptCodes ()) : Module.finrank K (K ∙ vecC ω c) = 1 := by
  have hp : IsFlipflopSub σ (K ∙ vecC ω c) ∧ Module.finrank K (K ∙ vecC ω c) = 1 :=
    isFlipflopPt_span_vecC hω hσω hc
  exact hp.2

omit [Finite K] in
private theorem d4v_isFlipflopSub_pt (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {c : ℕ}
    (hc : c ∈ ptCodes ()) : IsFlipflopSub σ (K ∙ vecC ω c) := by
  have hp : IsFlipflopSub σ (K ∙ vecC ω c) ∧ Module.finrank K (K ∙ vecC ω c) = 1 :=
    isFlipflopPt_span_vecC hω hσω hc
  exact hp.1

omit [Finite K] [CharP K 2] in
private theorem d4v_finrank_of_pt {P : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (h : IsFlipflopPt σ P) : Module.finrank K P = 1 := by
  have h' : IsFlipflopSub σ P ∧ Module.finrank K P = 1 := h
  exact h'.2

private theorem d4v_pt_mem (hT : Checks F) {x : ℕ} (hx : x < 2240) :
    (ptCodes ())[x]! ∈ ptCodes () := by
  have hsize : (ptCodes ()).size = 2240 := d4v_pts_size hT
  have h : x < (ptCodes ()).size := by rw [hsize]; exact hx
  rw [d4v_getElem!_eq_getElem (ptCodes ()) x h]
  exact Array.getElem_mem h

private theorem d4v_nbOf_getElem (T : Tabs) {x : ℕ} (hx : x < 6720) :
    (nbOf T)[x]! = (Array.range 6720).filter (adjT T x) := by
  have hnb : nbOf T = (Array.range 6720).map
      (fun y => (Array.range 6720).filter (adjT T y)) := rfl
  rw [hnb]
  have h : x < ((Array.range 6720).map
      (fun y => (Array.range 6720).filter (adjT T y))).size := by
    simp only [Array.size_map, Array.size_range]
    exact hx
  have h' : ((Array.range 6720).map (fun y => (Array.range 6720).filter (adjT T y)))[x]! =
      ((Array.range 6720).map (fun y => (Array.range 6720).filter (adjT T y)))[x]'h :=
    d4v_getElem!_eq_getElem
      ((Array.range 6720).map (fun y => (Array.range 6720).filter (adjT T y))) x h
  rw [h', Array.getElem_map, Array.getElem_range]

private noncomputable def d4v_ptVert (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {c : ℕ}
    (hc : c ∈ ptCodes ()) : CompVert σ :=
  have h1 : Module.finrank K (K ∙ vecC ω c) = 1 := d4v_finrank_pt hω hσω hc
  ⟨⟨K ∙ vecC ω c, d4v_isFlipflopSub_pt hω hσω hc,
      fun hbot => by rw [hbot, finrank_bot] at h1; omega, by rw [h1]; omega⟩,
    by rw [h1]; omega⟩

private noncomputable def d4v_solVert (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) {j : ℕ}
    (hj : j < 4480) : CompVert σ :=
  have h4 : Module.finrank K (solSub ω F j) = 4 := finrank_solSub hω hσω hσ hK hT hj
  ⟨⟨solSub ω F j, isFlipflopSub_solSub hω hσω hσ hK hT hj,
      fun hbot => by rw [hbot, finrank_bot] at h4; omega, by rw [h4]; omega⟩,
    by rw [h4]; omega⟩

private noncomputable def d4v_vmap (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x : Fin 6720) :
    CompVert σ :=
  if hx : (x : ℕ) < 2240 then
    d4v_ptVert hω hσω (c := (ptCodes ())[x.1]!) (d4v_pt_mem hT hx)
  else
    d4v_solVert hω hσω hσ hK hT (j := x.1 - 2240) (by have h := x.2; omega)

private theorem d4v_vmap_pt (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x : Fin 6720)
    (hx : x.1 < 2240) :
    (d4v_vmap hω hσω hσ hK hT x).1.1 = K ∙ vecC ω ((ptCodes ())[x.1]!) := by
  have hv : d4v_vmap hω hσω hσ hK hT x = d4v_ptVert hω hσω
      (c := (ptCodes ())[x.1]!) (d4v_pt_mem hT hx) := by
    simp only [d4v_vmap]
    exact dif_pos hx
  rw [hv]
  rfl

private theorem d4v_vmap_sol (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x : Fin 6720)
    (hx : ¬ x.1 < 2240) :
    (d4v_vmap hω hσω hσ hK hT x).1.1 = solSub ω F (x.1 - 2240) := by
  have hv : d4v_vmap hω hσω hσ hK hT x = d4v_solVert hω hσω hσ hK hT
      (j := x.1 - 2240) (by have h := x.2; omega) := by
    simp only [d4v_vmap]
    exact dif_neg hx
  rw [hv]
  rfl

omit [Finite K] [CharP K 2] in
private theorem d4v_flagGraph_pt_pt {P Q : FlagVert σ 3}
    (hP : Module.finrank K P.1 = 1) (hQ : Module.finrank K Q.1 = 1) :
    ¬ (flagGraph σ 3).Adj P Q := by
  rintro (h | h | ⟨h4, -⟩)
  · exfalso
    have hlt := Submodule.finrank_lt_finrank_of_lt h
    rw [hP, hQ] at hlt
    omega
  · exfalso
    have hlt := Submodule.finrank_lt_finrank_of_lt h
    rw [hP, hQ] at hlt
    omega
  · omega

omit [Finite K] [CharP K 2] in
private theorem d4v_flagGraph_pt_sol {P Q : FlagVert σ 3}
    (hP : Module.finrank K P.1 = 1) (hQ : Module.finrank K Q.1 = 4) :
    (flagGraph σ 3).Adj P Q ↔ P.1 < Q.1 := by
  constructor
  · rintro (h | h | ⟨h4, -⟩)
    · exact h
    · exfalso
      have hlt := Submodule.finrank_lt_finrank_of_lt h
      rw [hP, hQ] at hlt
      omega
    · omega
  · exact Or.inl

omit [Finite K] [CharP K 2] in
private theorem d4v_flagGraph_sol_pt {P Q : FlagVert σ 3}
    (hP : Module.finrank K P.1 = 4) (hQ : Module.finrank K Q.1 = 1) :
    (flagGraph σ 3).Adj P Q ↔ Q.1 < P.1 := by
  constructor
  · rintro (h | h | ⟨-, h4, -⟩)
    · exfalso
      have hlt := Submodule.finrank_lt_finrank_of_lt h
      rw [hP, hQ] at hlt
      omega
    · exact h
    · omega
  · exact fun h => Or.inr (Or.inl h)

omit [Finite K] [CharP K 2] in
private theorem d4v_flagGraph_sol_sol {P Q : FlagVert σ 3}
    (hP : Module.finrank K P.1 = 4) (hQ : Module.finrank K Q.1 = 4) :
    (flagGraph σ 3).Adj P Q ↔ Module.finrank K ↥(P.1 ⊓ Q.1) = 3 := by
  constructor
  · rintro (h | h | ⟨-, -, h3⟩)
    · exfalso
      have hlt := Submodule.finrank_lt_finrank_of_lt h
      rw [hP, hQ] at hlt
      omega
    · exfalso
      have hlt := Submodule.finrank_lt_finrank_of_lt h
      rw [hP, hQ] at hlt
      omega
    · exact h3
  · exact fun h => Or.inr (Or.inr ⟨hP, hQ, h⟩)

private theorem d4v_adjT_pt_pt (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720)
    (hx : x.1 < 2240) (hy : y.1 < 2240) :
    adjT (mkTabs (ptCodes ()) F) x.1 y.1 = true ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  have hcx : (ptCodes ())[x.1]! ∈ ptCodes () := d4v_pt_mem hT hx
  have hcy : (ptCodes ())[y.1]! ∈ ptCodes () := d4v_pt_mem hT hy
  have hvx := d4v_vmap_pt hω hσω hσ hK hT x hx
  have hvy := d4v_vmap_pt hω hσω hσ hK hT y hy
  have hpx : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 1 := by
    rw [hvx]
    exact d4v_finrank_pt hω hσω hcx
  have hpy : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 1 := by
    rw [hvy]
    exact d4v_finrank_pt hω hσω hcy
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hL : adjT (mkTabs (ptCodes ()) F) x.1 y.1 =
      ptAdjC ((ptCodes ())[x.1]!) ((ptCodes ())[y.1]!) := by
    simp only [adjT, if_pos hx, if_pos hy, hpts]
  rw [hL, compGraph_adj]
  constructor
  · intro h
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [hvx]
      exact isFlipflopPt_span_vecC hω hσω hcx
    · rw [hvy]
      exact isFlipflopPt_span_vecC hω hσω hcy
    · rw [hvx, hvy]
      exact (flipColl_span_vecC_iff hω hσω hσ hK hcx hcy).2 h
  · rintro (h | ⟨-, -, hcoll⟩)
    · exact absurd h (d4v_flagGraph_pt_pt hpx hpy)
    · rw [hvx, hvy] at hcoll
      exact (flipColl_span_vecC_iff hω hσω hσ hK hcx hcy).1 hcoll

private theorem d4v_adjT_pt_sol (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720)
    (hx : x.1 < 2240) (hy : ¬ y.1 < 2240) :
    adjT (mkTabs (ptCodes ()) F) x.1 y.1 = true ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  have hcx : (ptCodes ())[x.1]! ∈ ptCodes () := d4v_pt_mem hT hx
  have hpy : y.1 - 2240 < F.size := by
    have h := y.2
    have hF := d4v_frames_size hT
    omega
  have hpy' : y.1 - 2240 < 4480 := by
    have h := y.2
    omega
  have hvx := d4v_vmap_pt hω hσω hσ hK hT x hx
  have hvy := d4v_vmap_sol hω hσω hσ hK hT y hy
  have hfx : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 1 := by
    rw [hvx]
    exact d4v_finrank_pt hω hσω hcx
  have hfy : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 4 := by
    rw [hvy]
    exact finrank_solSub hω hσω hσ hK hT hpy'
  have hpx : x.1 < (ptCodes ()).size := by
    rw [d4v_pts_size hT]
    exact hx
  have hL : adjT (mkTabs (ptCodes ()) F) x.1 y.1 =
      memC (ptCodes ()) F[y.1 - 2240]! ((ptCodes ())[x.1]!) := by
    simp only [adjT, if_pos hx, if_neg hy]
    exact inc_mkTabs hpy hpx
  have hvC : (ptCodes ())[x.1]! < 65536 := (mem_ptCodes.mp hcx).1
  have hmem := memC_iff hω hσω hσ hK hT hpy' hvC
  have hlt : (d4v_vmap hω hσω hσ hK hT x).1.1 <
      (d4v_vmap hω hσω hσ hK hT y).1.1 ↔
      vecC ω ((ptCodes ())[x.1]!) ∈ solSub ω F (y.1 - 2240) := by
    rw [hvx, hvy]
    constructor
    · intro h
      exact (Submodule.span_singleton_le_iff_mem _ _).mp h.le
    · intro h
      refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr h) ?_
      intro heq
      have h1 : Module.finrank K (K ∙ vecC ω ((ptCodes ())[x.1]!)) = 1 :=
        d4v_finrank_pt hω hσω hcx
      rw [heq] at h1
      rw [finrank_solSub hω hσω hσ hK hT hpy'] at h1
      omega
  rw [hL, compGraph_adj]
  constructor
  · intro h
    exact Or.inl ((d4v_flagGraph_pt_sol hfx hfy).2 (hlt.2 (hmem.mp h)))
  · rintro (h | ⟨-, hpt, -⟩)
    · exact hmem.mpr (hlt.1 ((d4v_flagGraph_pt_sol hfx hfy).1 h))
    · exact absurd (d4v_finrank_of_pt hpt) (by rw [hfy]; omega)

private theorem d4v_adjT_sol_pt (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720)
    (hx : ¬ x.1 < 2240) (hy : y.1 < 2240) :
    adjT (mkTabs (ptCodes ()) F) x.1 y.1 = true ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  have hcy : (ptCodes ())[y.1]! ∈ ptCodes () := d4v_pt_mem hT hy
  have hpx : x.1 - 2240 < F.size := by
    have h := x.2
    have hF := d4v_frames_size hT
    omega
  have hpx' : x.1 - 2240 < 4480 := by
    have h := x.2
    omega
  have hvx := d4v_vmap_sol hω hσω hσ hK hT x hx
  have hvy := d4v_vmap_pt hω hσω hσ hK hT y hy
  have hfx : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 4 := by
    rw [hvx]
    exact finrank_solSub hω hσω hσ hK hT hpx'
  have hfy : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 1 := by
    rw [hvy]
    exact d4v_finrank_pt hω hσω hcy
  have hpy : y.1 < (ptCodes ()).size := by
    rw [d4v_pts_size hT]
    exact hy
  have hL : adjT (mkTabs (ptCodes ()) F) x.1 y.1 =
      memC (ptCodes ()) F[x.1 - 2240]! ((ptCodes ())[y.1]!) := by
    simp only [adjT, if_neg hx, if_pos hy]
    exact inc_mkTabs hpx hpy
  have hvC : (ptCodes ())[y.1]! < 65536 := (mem_ptCodes.mp hcy).1
  have hmem := memC_iff hω hσω hσ hK hT hpx' hvC
  have hlt : (d4v_vmap hω hσω hσ hK hT y).1.1 <
      (d4v_vmap hω hσω hσ hK hT x).1.1 ↔
      vecC ω ((ptCodes ())[y.1]!) ∈ solSub ω F (x.1 - 2240) := by
    rw [hvy, hvx]
    constructor
    · intro h
      exact (Submodule.span_singleton_le_iff_mem _ _).mp h.le
    · intro h
      refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr h) ?_
      intro heq
      have h1 : Module.finrank K (K ∙ vecC ω ((ptCodes ())[y.1]!)) = 1 :=
        d4v_finrank_pt hω hσω hcy
      rw [heq] at h1
      rw [finrank_solSub hω hσω hσ hK hT hpx'] at h1
      omega
  rw [hL, compGraph_adj]
  constructor
  · intro h
    exact Or.inl ((d4v_flagGraph_sol_pt hfx hfy).2 (hlt.2 (hmem.mp h)))
  · rintro (h | ⟨hpt, -, -⟩)
    · exact hmem.mpr (hlt.1 ((d4v_flagGraph_sol_pt hfx hfy).1 h))
    · exact absurd (d4v_finrank_of_pt hpt) (by rw [hfx]; omega)

private theorem d4v_adjT_sol_sol (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720)
    (hx : ¬ x.1 < 2240) (hy : ¬ y.1 < 2240) :
    adjT (mkTabs (ptCodes ()) F) x.1 y.1 = true ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  have hix : x.1 - 2240 < 4480 := d4v_sub_lt x.2
  have hiy : y.1 - 2240 < 4480 := d4v_sub_lt y.2
  have hvx := d4v_vmap_sol hω hσω hσ hK hT x hx
  have hvy := d4v_vmap_sol hω hσω hσ hK hT y hy
  have hfx : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 4 := by
    rw [hvx]
    exact finrank_solSub hω hσω hσ hK hT hix
  have hfy : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 4 := by
    rw [hvy]
    exact finrank_solSub hω hσω hσ hK hT hiy
  have hL : adjT (mkTabs (ptCodes ()) F) x.1 y.1 =
      (x.1 != y.1 && triTest (mkTabs (ptCodes ()) F) (x.1 - 2240) (y.1 - 2240)) := by
    simp only [adjT, if_neg hx, if_neg hy]
  have hne' : x.1 ≠ y.1 → x.1 - 2240 ≠ y.1 - 2240 := fun hne hh =>
    hne (d4v_sub_inj (Nat.le_of_not_lt hx) (Nat.le_of_not_lt hy) hh)
  constructor
  · intro h
    have h' : x.1 ≠ y.1 ∧
        triTest (mkTabs (ptCodes ()) F) (x.1 - 2240) (y.1 - 2240) = true := by
      rwa [hL, Bool.and_eq_true, bne_iff_ne] at h
    rw [compGraph_adj]
    refine Or.inl ((d4v_flagGraph_sol_sol hfx hfy).2 ?_)
    rw [hvx, hvy]
    exact (finrank_inf_solSub_eq_three_iff hω hσω hσ hK hT hix hiy (hne' h'.1)).2 h'.2
  · intro h
    have hne : x.1 ≠ y.1 := fun hxy => h.ne (by rw [Fin.ext hxy])
    have htri : triTest (mkTabs (ptCodes ()) F) (x.1 - 2240) (y.1 - 2240) = true := by
      rcases h with hf | ⟨hpt, -, -⟩
      · have h3 := (d4v_flagGraph_sol_sol hfx hfy).1 hf
        rw [hvx, hvy] at h3
        exact (finrank_inf_solSub_eq_three_iff hω hσω hσ hK hT hix hiy (hne' hne)).1 h3
      · exact absurd (d4v_finrank_of_pt hpt) (by rw [hfx]; omega)
    rw [hL, Bool.and_eq_true, bne_iff_ne]
    exact ⟨hne, htri⟩

private theorem d4v_adjT_iff (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720) :
    adjT (mkTabs (ptCodes ()) F) x.1 y.1 = true ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  by_cases hx : x.1 < 2240
  · by_cases hy : y.1 < 2240
    · exact d4v_adjT_pt_pt hω hσω hσ hK hT x y hx hy
    · exact d4v_adjT_pt_sol hω hσω hσ hK hT x y hx hy
  · by_cases hy : y.1 < 2240
    · exact d4v_adjT_sol_pt hω hσω hσ hK hT x y hx hy
    · exact d4v_adjT_sol_sol hω hσω hσ hK hT x y hx hy

private theorem d4v_adjT_symm (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) {x y : ℕ}
    (hx : x < 6720) (hy : y < 6720) :
    adjT (mkTabs (ptCodes ()) F) x y = true ↔
      adjT (mkTabs (ptCodes ()) F) y x = true := by
  constructor
  · intro h
    exact (d4v_adjT_iff hω hσω hσ hK hT ⟨y, hy⟩ ⟨x, hx⟩).2
      (((d4v_adjT_iff hω hσω hσ hK hT ⟨x, hx⟩ ⟨y, hy⟩).1 h).symm)
  · intro h
    exact (d4v_adjT_iff hω hσω hσ hK hT ⟨x, hx⟩ ⟨y, hy⟩).2
      (((d4v_adjT_iff hω hσω hσ hK hT ⟨y, hy⟩ ⟨x, hx⟩).1 h).symm)

private theorem d4v_occB_nbOf {x y : ℕ} (hx : x < 6720) (hy : y < 6720) :
    occB (nbOf (mkTabs (ptCodes ()) F))[x]! y = true ↔
      adjT (mkTabs (ptCodes ()) F) x y = true := by
  rw [d4v_occB_iff, d4v_nbOf_getElem (mkTabs (ptCodes ()) F) hx, Array.mem_filter,
    Array.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

private theorem d4v_nbrGraph_adj_iff (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) (x y : Fin 6720) :
    (nbrGraph 6720 (nbOf (mkTabs (ptCodes ()) F))).Adj x y ↔
      (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x)
        (d4v_vmap hω hσω hσ hK hT y) := by
  constructor
  · intro h
    have h' : x.1 ≠ y.1 ∧ (occB (nbOf (mkTabs (ptCodes ()) F))[x.1]! y.1 = true ∨
        occB (nbOf (mkTabs (ptCodes ()) F))[y.1]! x.1 = true) := by
      rwa [nbrGraph_adj_iff, adjB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at h
    rcases h'.2 with hocc | hocc
    · exact (d4v_adjT_iff hω hσω hσ hK hT x y).1 ((d4v_occB_nbOf x.2 y.2).1 hocc)
    · exact (d4v_adjT_iff hω hσω hσ hK hT x y).1
        ((d4v_adjT_symm hω hσω hσ hK hT y.2 x.2).1 ((d4v_occB_nbOf y.2 x.2).1 hocc))
  · intro h
    have hne : x.1 ≠ y.1 := fun hxy => h.ne (by rw [Fin.ext hxy])
    have hocc : occB (nbOf (mkTabs (ptCodes ()) F))[x.1]! y.1 = true :=
      (d4v_occB_nbOf x.2 y.2).2 ((d4v_adjT_iff hω hσω hσ hK hT x y).2 h)
    rw [nbrGraph_adj_iff, adjB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
    exact ⟨hne, Or.inl hocc⟩

private theorem d4v_vmap_inj (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) :
    Function.Injective (d4v_vmap hω hσω hσ hK hT) := by
  intro x y h
  have hP : (ptCodes ()).size = 2240 := d4v_pts_size hT
  by_cases hx : x.1 < 2240 <;> by_cases hy : y.1 < 2240
  · have hvx := d4v_vmap_pt hω hσω hσ hK hT x hx
    have hvy := d4v_vmap_pt hω hσω hσ hK hT y hy
    have hsub : K ∙ vecC ω ((ptCodes ())[x.1]!) = K ∙ vecC ω ((ptCodes ())[y.1]!) := by
      have h' := congrArg (fun v : CompVert σ => v.1.1) h
      rwa [hvx, hvy] at h'
    have hcx : (ptCodes ())[x.1]! ∈ ptCodes () := d4v_pt_mem hT hx
    have hcy : (ptCodes ())[y.1]! ∈ ptCodes () := d4v_pt_mem hT hy
    have hcode : (ptCodes ())[x.1]! = (ptCodes ())[y.1]! :=
      eq_of_span_vecC_eq hω hσω hcx hcy hsub
    have hxx : x.1 < (ptCodes ()).toList.length := by
      rw [Array.length_toList, hP]
      exact hx
    have hyy : y.1 < (ptCodes ()).toList.length := by
      rw [Array.length_toList, hP]
      exact hy
    have hpx : x.1 < (ptCodes ()).size := by rw [hP]; exact hx
    have hpy : y.1 < (ptCodes ()).size := by rw [hP]; exact hy
    have hxx' : (ptCodes ()).toList[x.1] = (ptCodes ())[x.1]! := by
      rw [Array.getElem_toList]
      exact (d4v_getElem!_eq_getElem (ptCodes ()) x.1 hpx).symm
    have hyy' : (ptCodes ()).toList[y.1] = (ptCodes ())[y.1]! := by
      rw [Array.getElem_toList]
      exact (d4v_getElem!_eq_getElem (ptCodes ()) y.1 hpy).symm
    have hlist : (ptCodes ()).toList[x.1] = (ptCodes ()).toList[y.1] := by
      rw [hxx', hyy']
      exact hcode
    exact Fin.ext ((List.getElem_inj (d4v_ptCodes_nodup)).mp hlist)
  · have hvx := d4v_vmap_pt hω hσω hσ hK hT x hx
    have hvy := d4v_vmap_sol hω hσω hσ hK hT y hy
    have h1 : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 1 := by
      rw [hvx]
      exact d4v_finrank_pt hω hσω (d4v_pt_mem hT hx)
    have h4 : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 4 := by
      rw [hvy]
      exact finrank_solSub hω hσω hσ hK hT (d4v_sub_lt y.2)
    have hfin := congrArg (fun v : CompVert σ => Module.finrank K v.1.1) h
    rw [h1, h4] at hfin
    omega
  · have hvx := d4v_vmap_sol hω hσω hσ hK hT x hx
    have hvy := d4v_vmap_pt hω hσω hσ hK hT y hy
    have h1 : Module.finrank K (d4v_vmap hω hσω hσ hK hT x).1.1 = 4 := by
      rw [hvx]
      exact finrank_solSub hω hσω hσ hK hT (d4v_sub_lt x.2)
    have h4 : Module.finrank K (d4v_vmap hω hσω hσ hK hT y).1.1 = 1 := by
      rw [hvy]
      exact d4v_finrank_pt hω hσω (d4v_pt_mem hT hy)
    have hfin := congrArg (fun v : CompVert σ => Module.finrank K v.1.1) h
    rw [h1, h4] at hfin
    omega
  · have hvx := d4v_vmap_sol hω hσω hσ hK hT x hx
    have hvy := d4v_vmap_sol hω hσω hσ hK hT y hy
    have hsub : solSub ω F (x.1 - 2240) = solSub ω F (y.1 - 2240) := by
      have h' := congrArg (fun v : CompVert σ => v.1.1) h
      rwa [hvx, hvy] at h'
    have hix : x.1 - 2240 < 4480 := d4v_sub_lt x.2
    have hiy : y.1 - 2240 < 4480 := d4v_sub_lt y.2
    have hji := solSub_injOn hω hσω hσ hK hT hix hiy hsub
    exact Fin.ext (d4v_sub_inj (Nat.le_of_not_lt hx) (Nat.le_of_not_lt hy) hji)

private theorem d4v_vmap_surj (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) :
    Function.Surjective (d4v_vmap hω hσω hσ hK hT) := by
  intro U
  have hP : (ptCodes ()).size = 2240 := d4v_pts_size hT
  rcases CompVert.finrank_one_four U with h1 | h4
  · have hpt : IsFlipflopPt σ U.1.1 := ⟨U.1.2.1, h1⟩
    obtain ⟨c, hc, hU⟩ := exists_mem_ptCodes hω hσω hK hpt
    obtain ⟨i, hi, hci⟩ := Array.mem_iff_getElem.mp hc
    have hi2240 : i < 2240 := by rw [hP] at hi; exact hi
    have hi' : i < 6720 := by omega
    let z : Fin 6720 := ⟨i, hi'⟩
    have hzv : (z : ℕ) = i := rfl
    have hz : z.1 < 2240 := by rw [hzv]; exact hi2240
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [d4v_vmap_pt hω hσω hσ hK hT z hz, hU, hzv,
      d4v_getElem!_eq_getElem (ptCodes ()) i hi, hci]
  · obtain ⟨j, hj, hU⟩ := exists_solSub_eq hω hσω hσ hK hT U.1.2.1 h4
    have hj' : 2240 + j < 6720 := by omega
    let z : Fin 6720 := ⟨2240 + j, hj'⟩
    have hzv : (z : ℕ) = 2240 + j := rfl
    have hz : ¬ z.1 < 2240 := by rw [hzv]; exact d4v_not_lt_add j
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [d4v_vmap_sol hω hσω hσ hK hT z hz, hU, hzv, Nat.add_sub_cancel_left]

end Codes

theorem nonempty_nbrGraph_iso (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {ω : K}
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {F : Array (Array ℕ)} (hT : Checks F) :
    Nonempty (nbrGraph 6720 (nbOf (mkTabs (ptCodes ()) F)) ≃g compGraph σ) := by
  let e : Fin 6720 ≃ CompVert σ :=
    Equiv.ofBijective (d4v_vmap hω hσω hσ hK hT)
      ⟨d4v_vmap_inj hω hσω hσ hK hT, d4v_vmap_surj hω hσω hσ hK hT⟩
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro x y
  show (compGraph σ).Adj (d4v_vmap hω hσω hσ hK hT x) (d4v_vmap hω hσω hσ hK hT y) ↔
    (nbrGraph 6720 (nbOf (mkTabs (ptCodes ()) F))).Adj x y
  exact (d4v_nbrGraph_adj_iff hω hσω hσ hK hT x y).symm

end CFSG.ClassicalInvolution.PhanDn.D4Q2
