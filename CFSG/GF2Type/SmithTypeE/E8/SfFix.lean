module

public import CFSG.GF2Type.SmithTypeE.E8.SfAct
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


theorem torusGroup_eq_bot_zmod2 : torusGroup .E7 (ZMod 2) = ⊥ :=
  torusGroup_eq_bot_of_forall_units_eq_one (by decide)

theorem borel_eq_posUnipotent : borelGroup .E7 (ZMod 2) = posUnipotent .E7 (ZMod 2) := by
  rw [borelGroup, torusGroup_eq_bot_zmod2, bot_sup_eq]

theorem posUnipotent_le_adjointGroup_E7 {K : Type} [Field K] :
    posUnipotent .E7 K ≤ adjointGroup .E7 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem xC_mem_posUnipotent {K : Type} [Field K] (i : Fin (Tag.rank .E7)) (c : K) :
    ((xC .E7 K i c : adjointGroup .E7 K) : ModGL .E7 K) ∈ posUnipotent .E7 K := by
  have h1 : ((xC .E7 K i c : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K (Pi.single i 1) c := (pinnedX_single .E7 K i c).symm
  have hpos : IsRoot .E7 (Pi.single i 1) ∧ 0 < height (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) := by
    refine ⟨isRoot_single .E7 i, ?_⟩
    simp [height]
  rw [h1]
  exact le_biSup (rootSubgroup .E7 K) hpos (Subgroup.subset_closure ⟨c, rfl⟩)

set_option maxRecDepth 20000 in
theorem eq_zero_or_eq_e7Y56 (w : Fin e7Data.d →₀ ZMod 2)
    (hw : ∀ u : ↥(adjointGroup .E7 (ZMod 2)),
      (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) → e7Rep56 (ZMod 2) u w = w) :
    w = 0 ∨ w = e7Y56 := by
  have hv : ∀ i, e7Data.rootOp (ZMod 2) (Pi.single i 1) w = 0 := by
    intro i
    have h := hw (xC .E7 (ZMod 2) i 1) (xC_mem_posUnipotent i 1)
    rw [e7Rep56, pullRep_apply, e7Psi_xC, minRep_xm] at h
    simp only [LinearMap.add_apply, Module.End.one_apply, one_smul] at h
    exact add_eq_left.1 h
  have h := eq_smul_of_rootOp_eq_zero e7Data_valid e7_dominant hv
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc (w ⟨0, by decide⟩) with h0 | h1
  · left
    rw [h, h0, zero_smul]
  · right
    rw [h, h1, one_smul]
    rfl

@[expose] def stabY : Subgroup ↥(adjointGroup .E7 (ZMod 2)) where
  carrier := {g | e7Rep56 (ZMod 2) g e7Y56 = e7Y56}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : e7Rep56 (ZMod 2) (a⁻¹ * a) e7Y56 = e7Y56 := by simp
    rw [map_mul, Module.End.mul_apply, ha] at h
    exact h

theorem mem_stabY {g : ↥(adjointGroup .E7 (ZMod 2))} :
    g ∈ stabY ↔ e7Rep56 (ZMod 2) g e7Y56 = e7Y56 := Iff.rfl

theorem e7Rep56_posUnipotent_e7Y56 (g : ↥(adjointGroup .E7 (ZMod 2)))
    (hg : (g : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) :
    e7Rep56 (ZMod 2) g e7Y56 = e7Y56 :=
  ((e7Datum (K := ZMod 2)).mem_fixU (e7Rep56 (ZMod 2))).1 (e7Y56_mem_fixU (K := ZMod 2)) g hg

@[expose] def stabYGL : Subgroup (ModGL .E7 (ZMod 2)) :=
  stabY.map (adjointGroup .E7 (ZMod 2)).subtype

theorem stabYGL_le : stabYGL ≤ adjointGroup .E7 (ZMod 2) := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem mem_stabYGL {g : ModGL .E7 (ZMod 2)} :
    g ∈ stabYGL ↔ ∃ h : g ∈ adjointGroup .E7 (ZMod 2), e7Rep56 (ZMod 2) ⟨g, h⟩ e7Y56 = e7Y56 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨g, h⟩, h2, rfl⟩

theorem borelGroup_le_stabYGL : borelGroup .E7 (ZMod 2) ≤ stabYGL := by
  rw [borel_eq_posUnipotent]
  intro g hg
  have hga : g ∈ adjointGroup .E7 (ZMod 2) := posUnipotent_le_adjointGroup_E7 hg
  exact mem_stabYGL.2 ⟨hga, e7Rep56_posUnipotent_e7Y56 ⟨g, hga⟩ hg⟩

theorem e7Data_weyl_zero (i : Fin (Tag.rank .E7)) : e7Data_valid.sRefl i ⟨0, by decide⟩ = ⟨0, by decide⟩ ↔
    i ≠ e7n6 := by
  constructor
  · intro h hi
    subst hi
    exact e7Data_valid.sRefl_ne_self (a := ⟨0, by decide⟩) (by rw [e7_wt_one]; decide) h
  · intro hi
    refine e7Data_valid.sRefl_eq_self ?_
    rw [e7_wt_zero, if_neg hi]

theorem nC_mem_stabY_iff (i : Fin (Tag.rank .E7)) :
    nC .E7 (ZMod 2) i ∈ stabY ↔ i ≠ e7n6 := by
  rw [mem_stabY]
  have h : e7Rep56 (ZMod 2) (nC .E7 (ZMod 2) i) e7Y56 =
      Finsupp.single (e7Data_valid.sRefl i ⟨0, by decide⟩) 1 := e7Rep56_nC_single i _
  rw [h, ← e7Data_weyl_zero]
  have h1 : (e7Y56 : Fin e7Data.d →₀ ZMod 2) = Finsupp.single ⟨0, by decide⟩ 1 := rfl
  rw [h1, Finsupp.single_left_inj one_ne_zero]

theorem e7Rep56_e7Y56_eq_iff (g : ↥(adjointGroup .E7 (ZMod 2))) :
    e7Rep56 (ZMod 2) g e7Y56 = e7Y56 ↔
      (g : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6} := by
  have hcl := (borel_overgroup_classification .E7 (ZMod 2)).1 stabYGL borelGroup_le_stabYGL
    stabYGL_le
  have hJ : {i | weylElt .E7 (ZMod 2) i 1 ∈ stabYGL} = {i | i ≠ e7n6} := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [← nC_mem_stabY_iff]
    constructor
    · intro h
      obtain ⟨_, h2⟩ := mem_stabYGL.1 h
      exact h2
    · intro h
      exact mem_stabYGL.2 ⟨weylElt_mem_adjointGroup i 1, h⟩
  rw [hJ] at hcl
  rw [← hcl]
  constructor
  · intro h
    exact mem_stabYGL.2 ⟨g.2, h⟩
  · intro h
    obtain ⟨_, h2⟩ := mem_stabYGL.1 h
    exact h2

end CFSG.GF2Type.SmithTypeE.E8
