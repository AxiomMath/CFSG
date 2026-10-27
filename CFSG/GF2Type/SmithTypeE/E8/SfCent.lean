module

public import CFSG.GF2Type.SmithTypeE.E8.PairNF

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


abbrev e7n1 : Fin (Tag.rank .E7) := ⟨0, by decide⟩

theorem reflect_highRoot_of_ne (i : Fin (Tag.rank .E7)) (hi : i ≠ e7n1) :
    reflect .E7 i (highRoot .E7) = highRoot .E7 := by
  have h : ∀ j : Fin 7, j ≠ 0 → reflect .E7 j (highRoot .E7) = highRoot .E7 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals decide
  exact h i (fun e => hi (Fin.ext (by simpa using congrArg Fin.val e)))

set_option maxRecDepth 20000 in
theorem pinnedElt_reflect_n1_ne :
    pinnedElt .E7 (reflect .E7 e7n1 (highRoot .E7)) (1 : ZMod 2) ≠
      pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) := by
  intro h
  have hθ := isRoot_highRoot .E7
  have hβ : IsRoot .E7 (reflect .E7 e7n1 (highRoot .E7)) := IsRoot.reflect _ hθ
  have hop : e7Data.rootOp (ZMod 2) (reflect .E7 e7n1 (highRoot .E7)) =
      e7Data.rootOp (ZMod 2) (highRoot .E7) := by
    have h1 := congrArg (e7Rep56 (ZMod 2)) h
    rw [e7Rep56_pinnedElt hβ, e7Rep56_pinnedElt hθ] at h1
    simpa using h1
  obtain ⟨a, ha⟩ : ∃ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = -1 := by decide +kernel
  rcases rootOp_single_cases (K := ZMod 2) hθ a with ⟨h1, -⟩ | ⟨-, b, hb, hEb⟩
  · exact h1 ha
  rcases rootOp_single_cases (K := ZMod 2) hβ a with ⟨-, h0⟩ | ⟨-, b', hb', hEb'⟩
  · rw [hop, hEb] at h0
    exact Finsupp.single_ne_zero.2 one_ne_zero h0
  · rw [hop, hEb] at hEb'
    have hbb : b = b' := (Finsupp.single_left_injective one_ne_zero) hEb'
    subst hbb
    have h2 : MinData.toWeight (highRoot .E7) =
        MinData.toWeight (reflect .E7 e7n1 (highRoot .E7)) :=
      add_left_cancel (hb.symm.trans hb')
    have h3 : MinData.toWeight (reflect .E7 e7n1 (highRoot .E7)) ≠
        MinData.toWeight (highRoot .E7) := by decide +kernel
    exact h3 h2.symm

@[expose] def centTheta : Subgroup ↥(adjointGroup .E7 (ZMod 2)) where
  carrier := {g | g * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
    pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * g}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc a⁻¹ * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)
        = a⁻¹ * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * a⁻¹ := by rw [← ha]
      _ = pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * a⁻¹ := by group

@[expose] def centThetaGL : Subgroup (ModGL .E7 (ZMod 2)) :=
  centTheta.map (adjointGroup .E7 (ZMod 2)).subtype

theorem mem_centThetaGL {g : ModGL .E7 (ZMod 2)} :
    g ∈ centThetaGL ↔ ∃ x : ↥(adjointGroup .E7 (ZMod 2)), (x : ModGL .E7 (ZMod 2)) = g ∧
      x * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
        pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * x := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, h⟩
    exact ⟨x, h, rfl⟩

theorem centThetaGL_le : centThetaGL ≤ adjointGroup .E7 (ZMod 2) := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem borelGroup_le_centThetaGL : borelGroup .E7 (ZMod 2) ≤ centThetaGL := by
  rw [borel_eq_posUnipotent]
  intro g hg
  have hga : g ∈ adjointGroup .E7 (ZMod 2) := posUnipotent_le_adjointGroup_E7 hg
  exact mem_centThetaGL.2 ⟨⟨g, hga⟩, rfl, commute_posUnipotent_xtheta ⟨g, hga⟩ hg⟩

theorem weylElt_mem_centThetaGL_iff (i : Fin (Tag.rank .E7)) :
    weylElt .E7 (ZMod 2) i 1 ∈ centThetaGL ↔ i ≠ e7n1 := by
  have hn : nC .E7 (ZMod 2) i = nWC .E7 (ZMod 2) (simple .E7 i) :=
    Subtype.ext (canonicalRep_simple (coxeterSystem .E7) (ZMod 2) i).symm
  have hconj := nWC_mul_xtheta_mul_inv (simple .E7 i)
  rw [← hn, simple_smul] at hconj
  rw [mem_centThetaGL]
  constructor
  · rintro ⟨x, hx, h2⟩ hi
    subst hi
    have hxn : x = nC .E7 (ZMod 2) e7n1 := Subtype.ext hx
    subst hxn
    have h3 : nC .E7 (ZMod 2) e7n1 * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) *
        (nC .E7 (ZMod 2) e7n1)⁻¹ = pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h2
    exact pinnedElt_reflect_n1_ne (hconj.symm.trans h3)
  · intro hi
    refine ⟨nC .E7 (ZMod 2) i, rfl, ?_⟩
    rw [reflect_highRoot_of_ne i hi] at hconj
    exact mul_inv_eq_iff_eq_mul.1 hconj

theorem centralizer_xtheta_iff (g : ↥(adjointGroup .E7 (ZMod 2))) :
    g * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * g⁻¹ =
        pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) ↔
      (g : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n1} := by
  have hcl := (borel_overgroup_classification .E7 (ZMod 2)).1 centThetaGL
    borelGroup_le_centThetaGL centThetaGL_le
  have hJ : {i | weylElt .E7 (ZMod 2) i 1 ∈ centThetaGL} = {i | i ≠ e7n1} := by
    ext i
    exact weylElt_mem_centThetaGL_iff i
  rw [hJ] at hcl
  rw [← hcl, mem_centThetaGL, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact ⟨g, rfl, h⟩
  · rintro ⟨x, hx, h⟩
    have hxg : x = g := Subtype.ext hx
    subst hxg
    exact h

end CFSG.GF2Type.SmithTypeE.E8
