module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327Proof

public section

namespace CFSG.GH74.GLS.Bg.Pu5.BalA

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_conjugate {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (h : IsPCompIn 2 (centralizer ({x} : Set G)) L) :
    IsPCompIn 2 (centralizer ({x} : Set G)) (conjugate L y) := by
  have h1 := isPCompIn_map_conj h y⁻¹
  rw [map_centralizer_singleton_conj] at h1
  have e : y⁻¹ * x * y⁻¹⁻¹ = x := by
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hxy]
      _ = x := by group
  rw [e] at h1
  exact h1

theorem sup_conjugate_le_pLayerOf_gen {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({x} : Set G)) L) :
    L ⊔ conjugate L y ≤ pLayerOf 2 (centralizer ({x} : Set G)) ∧
      pLayerOf 2 (centralizer ({x} : Set G)) ≤ normalizer ((L ⊔ conjugate L y : Subgroup G) : Set G) :=
  have hL' := isPCompIn_conjugate hxy hL
  ⟨sup_le (le_sSup hL) (le_sSup hL'), fun _ hg =>
    mem_normalizer_sup' (pLayerOf_le_normalizer hL hg) (pLayerOf_le_normalizer hL' hg)⟩

theorem isSubnormal_fixed_sup_gen {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({x} : Set G)) L) :
    (((L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G)).subgroupOf
      (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))).IsSubnormal := by
  obtain ⟨hKE, hEN⟩ := sup_conjugate_le_pLayerOf_gen hxy hL
  have hEC : pLayerOf 2 (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G) :=
    TwoThin.pLayerOf_le 2 _
  have hZ : ((L ⊔ conjugate L y).subgroupOf (pLayerOf 2 (centralizer ({x} : Set G)))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hEN g.2) n).mp hn
    simpa using this
  have hK : ((pLayerOf 2 (centralizer ({x} : Set G))).subgroupOf (centralizer ({x} : Set G))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (mem_normalizer_pLayerOf g.2) n).mp hn
    simpa using this
  exact isSubnormal_inf_centralizer' hKE hEC hZ hK {y}

theorem IG_i_gen {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({x} : Set G)) L) (hyL : y ∉ normalizer (L : Set G)) :
    IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) (IDiag y L) := by
  have hab : y * x = x * y := hxy.symm
  have hMHb : L ≤ centralizer ({x} : Set G) := hL.1
  have hM : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G))) := hL.2
  have hne : L ≠ conjugate L y := (conjugate_ne_of_not_mem_normalizer hyL).symm
  obtain ⟨T, hTK, hTpc⟩ := exists_diag_pcomp hy hab hMHb hM hne
  have hcomp := orbit_fixed_component_comparison hy hab hMHb hM hTK hTpc
  have hfix : gsFixedLayer (L ⊔ conjugate L y) y = T := hcomp.2.1 hne
  have hI : IDiag y L = T := by
    rw [← hfix]
    unfold IDiag gsFixedLayer
    rw [inf_comm (centralizer ({y} : Set G)), pLayerOf_eq_map']
  rw [hI]
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM
  have hKC : L ⊔ conjugate L y ≤ centralizer ({x} : Set G) := sup_le hMHb hMaHb
  have hDW : (L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G) ≤
      centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := inf_le_inf_right _ hKC
  have hD2 : TwoComponents.IsTwoComponent
      (T.subgroupOf ((L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hTpc
  refine ⟨hTK.trans hDW, ?_⟩
  exact (CatalogueBAlternating.pComponent_two_iff _).mpr
    (TwoComponentTransport.extend_nested T _ _ hTK hDW (isSubnormal_fixed_sup_gen hxy hL) hD2)

theorem IG_bar_gen {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({x} : Set G)) L) (hyL : y ∉ normalizer (L : Set G))
    (hyC : y ∈ centralizer ({x} : Set G)) :
    ∃ hAB : ⁅(L.subgroupOf (centralizer ({x} : Set G))).map (TwoThin.barMk ↥(centralizer ({x} : Set G))),
        conjSub (TwoThin.barMk ↥(centralizer ({x} : Set G)) ⟨y, hyC⟩)⁻¹
          ((L.subgroupOf (centralizer ({x} : Set G))).map
            (TwoThin.barMk ↥(centralizer ({x} : Set G))))⁆ = ⊥,
      ((IDiag y L).subgroupOf (centralizer ({x} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({x} : Set G))) = (swapDiag hAB).range := by
  have hI := IG_i_gen hy hxy hL hyL
  have hL' := isPCompIn_conjugate hxy hL
  set C := centralizer ({x} : Set G) with hC
  have hI' : IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({x} : Set G)) (IDiag y L) := by
    rw [inf_comm]; exact hI
  have hso : orderOf (⟨y, hyC⟩ : ↥C) = 2 := TwoThin.orderOf_mk_centralizer hyC hy
  have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hI').1 hyC
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hI' hyC
  have hLC : L ≤ C := hL.1
  have hL'C : conjugate L y ≤ C := hL'.1
  set s : ↥C := ⟨y, hyC⟩ with hs
  set π := TwoThin.barMk ↥C with hπ
  have hinv : (π s)⁻¹ = π s := inv_eq_self_of_orderOf_eq_two (TwoThin.orderOf_barMk hso)
  have hLY2 : TwoComponents.IsTwoComponent (L.subgroupOf C) := (TwoThin.isPCompIn_two_iff.mp hL).2
  have hLY'2 : TwoComponents.IsTwoComponent ((conjugate L y).subgroupOf C) :=
    (TwoThin.isPCompIn_two_iff.mp hL').2
  have hAb := TwoThin.isComponent_map_barMk hLY2
  have hBb := TwoThin.isComponent_map_barMk hLY'2
  have hconjLY : conjugate (L.subgroupOf C) s = (conjugate L y).subgroupOf C :=
    conjugate_subgroupOf_eq L C s
  set Ab : Subgroup (TwoThin.barQ ↥C) := (L.subgroupOf C).map π with hAbdef
  set Bb : Subgroup (TwoThin.barQ ↥C) := ((conjugate L y).subgroupOf C).map π with hBbdef
  set Ib : Subgroup (TwoThin.barQ ↥C) := ((IDiag y L).subgroupOf C).map π with hIbdef
  have hB : Bb = conjSub (π s)⁻¹ Ab := by
    rw [hBbdef, ← hconjLY, map_conjugate']
    rfl
  have hAneB : Ab ≠ Bb := by
    intro h
    have h3 := OddKernelTwoComponents.lift_unique π TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk _ _ hLY2 hLY'2 h
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rw [inf_eq_left.mpr hLC, inf_eq_left.mpr hL'C] at h4
    exact conjugate_ne_of_not_mem_normalizer hyL h4.symm
  have hne : conjSub (π s)⁻¹ Ab ≠ Ab := fun h => hAneB (by rw [hB, h])
  have hAB : ⁅Ab, conjSub (π s)⁻¹ Ab⁆ = ⊥ := commutator_conjSub_eq_bot hAb hne
  refine ⟨hAB, ?_⟩
  have hAq := assembly_isQuasisimple_of_isComponent hAb
  have hperf : ⁅(IDiag y L).subgroupOf C, (IDiag y L).subgroupOf C⁆ = (IDiag y L).subgroupOf C :=
    TwoThin.commutator_self_of_isTwoComponent hΛC hΛ2
  have hne0 : (IDiag y L).subgroupOf C ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hΛ2
  have hIne : Ib ≠ ⊥ := TwoThin.map_barMk_ne_bot_of_perfect hperf hne0
  have hIperf : ⁅Ib, Ib⁆ = Ib := by
    rw [hIbdef, ← Subgroup.map_commutator, hperf]
  have hIAB : Ib ≤ Ab ⊔ Bb := by
    rw [hAbdef, hBbdef, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLC hL'C]
    exact Subgroup.map_mono (fun z hz => IDiag_le_sup y L hz)
  have hIZ : Ib ≤ centralizer ({π s} : Set (TwoThin.barQ ↥C)) :=
    (Subgroup.map_mono hΛC).trans (TwoThin.map_centralizer_barMk hso).le
  have hIΔ : Ib ≤ (swapDiag hAB).range := by
    calc Ib = ⁅Ib, Ib⁆ := hIperf.symm
      _ ≤ ⁅(Ab ⊔ conjSub (π s)⁻¹ Ab) ⊓ centralizer ({π s} : Set (TwoThin.barQ ↥C)),
            (Ab ⊔ conjSub (π s)⁻¹ Ab) ⊓ centralizer ({π s} : Set (TwoThin.barQ ↥C))⁆ := by
          refine Subgroup.commutator_mono ?_ ?_ <;>
            exact le_inf (hB ▸ hIAB) hIZ
      _ = (swapDiag hAB).range := commutator_fixed_eq_range_swapDiag hAB hinv hAq
  have hΔZ : (swapDiag hAB).range ≤ centralizer ({π s} : Set (TwoThin.barQ ↥C)) := by
    rintro _ ⟨a, rfl⟩
    exact swapDiag_mem_centralizer hAB hinv a
  have hIcomp := TwoThin.isTwoComponent_map_barMk hso hΛC hΛ2
  have hIsub : (Ib.subgroupOf (centralizer ({π s} : Set (TwoThin.barQ ↥C)))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hIcomp.1 Subgroup.IsSubnormal.top
  have hIΔsub : (Ib.subgroupOf (swapDiag hAB).range).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hIsub hΔZ
  have hΔq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 (isQuasisimple_range_swapDiag hAB hAq)
  have hΔcomp : CFSG.IsComponent (⊤ : Subgroup ↥(swapDiag hAB).range) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hΔq,
      Subgroup.IsSubnormal.top⟩
  refine le_antisymm hIΔ ?_
  rcases CFSG.LocalCores.component_subnormal_subgroup hΔcomp hIΔsub with h | h
  · intro d hd
    have := h (Subgroup.mem_top (⟨d, hd⟩ : ↥(swapDiag hAB).range))
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    apply hIne
    rw [eq_bot_iff, ← hIperf, Subgroup.commutator_le]
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨a, hIΔ ha⟩ : ↥(swapDiag hAB).range))
      (Subgroup.mem_subgroupOf.mpr hb : (⟨b, hIΔ hb⟩ : ↥(swapDiag hAB).range) ∈
        Ib.subgroupOf (swapDiag hAB).range)
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    simpa [commutatorElement_def] using h2

end CFSG.GH74.GLS.Bg.Pu5.BalA
