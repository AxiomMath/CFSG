module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X20
public import CFSG.ClassicalInvolution.Q3.Q3T7P25U01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X19

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Asc77.CX (TwinGroup DiagTriv DiagRel TwinIso centTG fixSubgroup)
open scoped MatrixGroups


section Bar

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] noncomputable def eBar (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : ↥R → BarQ Ω w := fun r => barEquiv Ω w (eSec hyp hw2 hwA r)

@[expose] noncomputable def eBar' (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : ↥R' → BarQ Ω w := fun r => barEquiv Ω w (eSec' hyp hw2 hwA r)

@[expose] noncomputable def zBar (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : BarQ Ω w := barEquiv Ω w (zSec hyp hw2 hwA)

@[expose] noncomputable def actBar (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1) :
    Subgroup (MulAut (BarQ Ω w)) :=
  ((cA S R R').subgroupOf (Subgroup.centralizer ({w} : Set G))).map (actOf hyp hw2)

theorem z_mem_core (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : z ∈ TwinDisc.coreLayer Ω w :=
  ⟨⟨z, z_centralizes hyp hwA⟩, z_mem_hull hyp hw2 hwA, rfl⟩

theorem R_mem_core (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') {r : G} (hr : r ∈ R) : r ∈ TwinDisc.coreLayer Ω w :=
  ⟨⟨r, R_centralizes hwA (Subgroup.mem_sup_left hr)⟩, R_mem_hull hyp hw2 hwA hr, rfl⟩

theorem R'_mem_core (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') {r : G} (hr : r ∈ R') : r ∈ TwinDisc.coreLayer Ω w :=
  ⟨⟨r, R_centralizes hwA (Subgroup.mem_sup_right hr)⟩, R'_mem_hull hyp hw2 hwA hr, rfl⟩

theorem twinLiftBar (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwA : w ∈ cA S R R') (hno : SecNoExitAt Ω w) (h6 : LayerLie Ω w 6) :
    Nonempty (TwinLift (eBar hyp hw2 hwA) (eBar' hyp hw2 hwA) (zBar hyp hw2 hwA) (actBar hyp hw2)) := by
  obtain ⟨T⟩ := twinLiftSec hyp hw2 hw1 hwA hno h6
  exact ⟨T.map (barEquiv Ω w) (fun r => rfl) (fun r => rfl) rfl (actImage_eq hyp hw2)⟩

end Bar

section Vertex

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] noncomputable def subLayer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w w' : G} (hw2 : w * w = 1)
    (hw'C : w' ∈ Subgroup.centralizer ({w} : Set G)) : Subgroup (BarQ Ω w) :=
  Goldschmidt75.perfRes (fixSubgroup (actOf hyp hw2 ⟨w', hw'C⟩))

theorem perfRes_normalizes_core (hΩ : HypOmegaGen Ω) {w w' n h : G}
    (hc2' : IsPGroup 2 (Subgroup.zpowers w')) 
    (hn : n ∈ Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G)))
    (hh : h ∈ Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G))) :
    n * h * n⁻¹ ∈
      Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hn' := Goldschmidt75.perfRes_le _ hn
  have hnC' : n ∈ Subgroup.centralizer ({w'} : Set G) := hn'.2
  have hnC : n ∈ Subgroup.centralizer ({w} : Set G) := TwinDisc.coreLayer_le_centralizer hn'.1
  have hconj : conjSub n (TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) =
      TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G) := by
    unfold conjSub
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective]
    change conjSub n (TwinDisc.coreLayer Ω w') ⊓ conjSub n (Subgroup.centralizer ({w} : Set G)) = _
    rw [TwinDisc.conjSub_coreLayer hΩ hc2' hnC', conjSub_eq_self_of_mem hnC]
  have hnN := Goldschmidt75.normalizer_le_normalizer_perfRes _
    (mem_normalizer_iff_conjSub_eq.mpr hconj)
  exact (Subgroup.mem_normalizer_iff.mp hnN h).mp hh

theorem conj_mem_oddCoreOf_core (hΩ : HypOmegaGen Ω) {w' n o : G}
    (hc2' : IsPGroup 2 (Subgroup.zpowers w')) (hn : n ∈ Subgroup.centralizer ({w'} : Set G))
    (ho : o ∈ oddCoreOf (TwinDisc.coreLayer Ω w')) :
    n * o * n⁻¹ ∈ oddCoreOf (TwinDisc.coreLayer Ω w') := by
  have h1 : n * o * n⁻¹ ∈ conjSub n (oddCoreOf (TwinDisc.coreLayer Ω w')) := conj_mem_conjSub ho
  rwa [← CFSG.ClassicalInvolution.Asc77.Thompson.oddCoreOf_conjSub_eq,
    TwinDisc.conjSub_coreLayer hΩ hc2' hn] at h1

end Vertex

section VertexIso

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem card_subgroupOf_lift {Y : Type} [Group Y] [Finite Y] {E E' : Type} {e : E → Y} {e' : E' → Y} {zb : Y}
    {P : Subgroup (MulAut Y)} (T : TwinLift e e' zb P) {H : Subgroup Y} (hA : T.A ≤ H) :
    Nat.card ↥(T.A.subgroupOf H) = 24 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, Nat.card_congr T.eA.toEquiv]
  exact natCard_sl2Three

theorem card_subgroupOf_lift' {Y : Type} [Group Y] [Finite Y] {E E' : Type} {e : E → Y} {e' : E' → Y} {zb : Y}
    {P : Subgroup (MulAut Y)} (T : TwinLift e e' zb P) {H : Subgroup Y} (hA : T.A' ≤ H) :
    Nat.card ↥(T.A'.subgroupOf H) = 24 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, Nat.card_congr T.eA'.toEquiv]
  exact natCard_sl2Three

theorem vertexIso (hom5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om5StabDiag)
    (hcent5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C25W.Cent5)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w w' : G} (hw2 : w * w = 1) (hw'2 : w' * w' = 1)
    (hwA : w ∈ cA S R R') (hw'A : w' ∈ cA S R R')
    (hw'C : w' ∈ Subgroup.centralizer ({w} : Set G)) (hwC : w ∈ Subgroup.centralizer ({w'} : Set G))
    (T : TwinLift (eBar hyp hw2 hwA) (eBar' hyp hw2 hwA) (zBar hyp hw2 hwA) (actBar hyp hw2))
    (T' : TwinLift (eBar hyp hw'2 hw'A) (eBar' hyp hw'2 hw'A) (zBar hyp hw'2 hw'A) (actBar hyp hw'2))
    (hA : T.A ≤ subLayer hyp hw2 hw'C) (hA' : T.A' ≤ subLayer hyp hw2 hw'C)
    (hB : T'.A ≤ subLayer hyp hw'2 hwC) (hB' : T'.A' ≤ subLayer hyp hw'2 hwC)
    (h5 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5
      (centTG T.A T.A' (actOf hyp hw2 ⟨w', hw'C⟩) hA hA'))
    (h5' : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.IsOm5
      (centTG T'.A T'.A' (actOf hyp hw'2 ⟨w, hwC⟩) hB hB')) :
    ∃ ψ : ↥(subLayer hyp hw2 hw'C) ≃* ↥(subLayer hyp hw'2 hwC),
      (T.A.subgroupOf (subLayer hyp hw2 hw'C)).map ψ.toMonoidHom = T'.A.subgroupOf (subLayer hyp hw'2 hwC) ∧
      (T.A'.subgroupOf (subLayer hyp hw2 hw'C)).map ψ.toMonoidHom = T'.A'.subgroupOf (subLayer hyp hw'2 hwC) ∧
      (∀ r : ↥R, ((ψ ⟨eBar hyp hw2 hwA r, hA (T.he r)⟩ : ↥(subLayer hyp hw'2 hwC)) : BarQ Ω w') =
        eBar hyp hw'2 hw'A r) ∧
      (∀ r : ↥R', ((ψ ⟨eBar' hyp hw2 hwA r, hA' (T.he' r)⟩ : ↥(subLayer hyp hw'2 hwC)) : BarQ Ω w') =
        eBar' hyp hw'2 hw'A r) := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  have hc2' : IsPGroup 2 (Subgroup.zpowers w') := isPGroup_zpowers_of_sq_eq_one hw'2
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzX := z_mem_core hyp hw2 hwA
  have hzX' := z_mem_core hyp hw'2 hw'A
  have hbX : conjSub w' (TwinDisc.coreLayer Ω w) = TwinDisc.coreLayer Ω w :=
    TwinDisc.conjSub_coreLayer hΩ hc2 hw'C
  have hbX' : conjSub w (TwinDisc.coreLayer Ω w') = TwinDisc.coreLayer Ω w' :=
    TwinDisc.conjSub_coreLayer hΩ hc2' hwC
  have hNT : ((Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G))).subgroupOf
      (TwinDisc.coreLayer Ω w)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w))) =
      subLayer hyp hw2 hw'C :=
    CFSG.ClassicalInvolution.Asc77.CX.map_perfRes_fix_eq hw'2 hbX
  have hNT' : ((Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G))).subgroupOf
      (TwinDisc.coreLayer Ω w')).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w'))) =
      subLayer hyp hw'2 hwC :=
    CFSG.ClassicalInvolution.Asc77.CX.map_perfRes_fix_eq hw2 hbX'
  have hNX : Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G)) ≤
      TwinDisc.coreLayer Ω w := (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hNX' : Goldschmidt75.perfRes (TwinDisc.coreLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      TwinDisc.coreLayer Ω w' := (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hTs : IsSimpleGroup ↥(subLayer hyp hw2 hw'C) := by
    obtain ⟨Φ₂, z₂, a₂, b₂, hd⟩ := h5
    exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isSimpleGroup_of_om5Data hd
  have hT's : IsSimpleGroup ↥(subLayer hyp hw'2 hwC) := by
    obtain ⟨Φ₂, z₂, a₂, b₂, hd⟩ := h5'
    exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.isSimpleGroup_of_om5Data hd
  have hzmem : (QuotientGroup.mk ⟨z, hzX⟩ : BarQ Ω w) ∈ subLayer hyp hw2 hw'C := by
    have h1 : T.z' ∈ T.A := T.om6.twin.hzA.mem
    rw [T.hz] at h1
    exact hA h1
  have hzmem' : (QuotientGroup.mk ⟨z, hzX'⟩ : BarQ Ω w') ∈ subLayer hyp hw'2 hwC := by
    have h1 : T'.z' ∈ T'.A := T'.om6.twin.hzA.mem
    rw [T'.hz] at h1
    exact hB h1
  obtain ⟨φ, hφ⟩ := Q3T7P25.U.exists_equiv_of_twin_layers hNX hNX' hNT hNT'
    (fun n hn h hh => perfRes_normalizes_core hΩ hc2' hn hh)
    (fun n hn h hh => perfRes_normalizes_core hΩ hc2 hn hh)
    (fun n hn o ho => conj_mem_oddCoreOf_core hΩ hc2' ((Goldschmidt75.perfRes_le _ hn).2) ho)
    (fun n hn o ho => conj_mem_oddCoreOf_core hΩ hc2 ((Goldschmidt75.perfRes_le _ hn).2) ho)
    hTs hT's hzX hzX' hz2 (Q3T7P25.U.mem_preimgOdd.mpr ⟨hzX, hzmem⟩)
    (Q3T7P25.U.mem_preimgOdd.mpr ⟨hzX', hzmem'⟩) (mk_ne_one_of_involution hzX hz2 hz1)
    (mk_ne_one_of_involution hzX' hz2 hz1)
  have hψR : ∀ r : ↥R, ((φ ⟨eBar hyp hw2 hwA r, hA (T.he r)⟩ : ↥(subLayer hyp hw'2 hwC)) : BarQ Ω w') =
      eBar hyp hw'2 hw'A r := by
    intro r
    exact hφ r.1 (R_mem_core hyp hw2 hwA r.2) (R_mem_core hyp hw'2 hw'A r.2)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨R_mem_core hyp hw2 hwA r.2, hA (T.he r)⟩)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨R_mem_core hyp hw'2 hw'A r.2, hB (T'.he r)⟩)
      ⟨eBar hyp hw2 hwA r, hA (T.he r)⟩ rfl
  have hψR' : ∀ r : ↥R', ((φ ⟨eBar' hyp hw2 hwA r, hA' (T.he' r)⟩ : ↥(subLayer hyp hw'2 hwC)) : BarQ Ω w') =
      eBar' hyp hw'2 hw'A r := by
    intro r
    exact hφ r.1 (R'_mem_core hyp hw2 hwA r.2) (R'_mem_core hyp hw'2 hw'A r.2)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨R'_mem_core hyp hw2 hwA r.2, hA' (T.he' r)⟩)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨R'_mem_core hyp hw'2 hw'A r.2, hB' (T'.he' r)⟩)
      ⟨eBar' hyp hw2 hwA r, hA' (T.he' r)⟩ rfl
  have hle := lift_preserved_le hom5 hcent5 T T' hA hA' hB hB' h5' φ hψR'
  have hle' := lift_preserved_le' hom5 hcent5 T T' hA hA' hB hB' h5' φ hψR
  refine ⟨φ, Subgroup.eq_of_le_of_card_ge hle ?_, Subgroup.eq_of_le_of_card_ge hle' ?_, hψR, hψR'⟩
  · rw [Subgroup.card_map_of_injective φ.injective, card_subgroupOf_lift T hA,
      card_subgroupOf_lift T' hB]
  · rw [Subgroup.card_map_of_injective φ.injective, card_subgroupOf_lift' T hA',
      card_subgroupOf_lift' T' hB']

end VertexIso

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
