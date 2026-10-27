module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem isAutConj_linearPilot_rootSL2 {K : Type*} [Field K] [Finite K] {m : ℕ} (hm : 3 ≤ m)
    (a b : Fin m) : IsAutConj (LinearPilot.rootSL2 (K := K) a b) :=
  fun β => LinearPilot.map_rootSL2_of_mulAut hm β a b

theorem e6RepPreHigh_zero_eq : e6RepPreHigh 0 = a5Root 0 5 := by
  decide

theorem a5Root_five_zero : a5Root 5 0 = -a5Root 0 5 := by
  decide

theorem e6RepWeyl_zero_smul_highRoot :
    e6RepWeyl 0 • highRoot .E6 = (Pi.single (0 : Fin 6) 1 : Fin (Tag.rank .E6) → ℤ) := by
  have h := e6RepWeyl_smul_e6ASFrame 0
  simpa [e6ASFrame, e6RepFrame] using h

theorem blockSpecialLinear_pair_eq_sup {n : ℕ} {K : Type*} [Field K] {a b : Fin n} (hab : a ≠ b) :
    LinearPilot.blockSpecialLinear (K := K) ({a, b} : Finset (Fin n)) =
      (Matrix.SpecialLinearGroup.transvectionHom (A := K) hab).range ⊔
        (Matrix.SpecialLinearGroup.transvectionHom (A := K) hab.symm).range := by
  rw [LinearPilot.blockSpecialLinear_eq_closure]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact absurd rfl hij
    · exact mem_sup_left ⟨Multiplicative.ofAdd c, by
        rw [Matrix.SpecialLinearGroup.transvectionHom_apply]; rfl⟩
    · exact mem_sup_right ⟨Multiplicative.ofAdd c, by
        rw [Matrix.SpecialLinearGroup.transvectionHom_apply]; rfl⟩
    · exact absurd rfl hij
  · refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨a, b, hab, Multiplicative.toAdd c, by simp, by simp,
        (Matrix.SpecialLinearGroup.transvectionHom_apply hab c).symm⟩
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨b, a, hab.symm, Multiplicative.toAdd c, by simp, by simp,
        (Matrix.SpecialLinearGroup.transvectionHom_apply hab.symm c).symm⟩

section Model

variable {K : Type} [Field K]

theorem map_conj_e6RepConj_zero_rootSpan_perpRoots :
    (rootSpan .E6 K (EPilot.perpRoots .E6)).map
        (MulAut.conj (e6RepConj K 0 : ModGL .E6 K)).toMonoidHom =
      rootSpan .E6 K (EPilot.rootPerp .E6 (Pi.single (0 : Fin 6) 1)) := by
  rw [coe_e6RepConj, EPilot.map_conj_rootSpan_perpRoots (Or.inl rfl),
    e6RepWeyl_zero_smul_highRoot]

variable [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def xLeviHom : Matrix.SpecialLinearGroup (Fin 6) K →* adjointGroup .E6 K :=
  (MulAut.conj (e6RepConj K 0)).toMonoidHom.comp (slToAdjointE6 K)

theorem map_slToAdjointE6_blockSpecialLinear_pair {i j : Fin 6} (hij : i ≠ j) :
    (LinearPilot.blockSpecialLinear (K := K) ({i, j} : Finset (Fin 6))).map
        ((adjointGroup .E6 K).subtype.comp (slToAdjointE6 K)) =
      rootSubgroup .E6 K (a5Root i j) ⊔ rootSubgroup .E6 K (a5Root j i) := by
  rw [blockSpecialLinear_pair_eq_sup hij, Subgroup.map_sup, ← Subgroup.map_map,
    ← Subgroup.map_map, map_slToAdjointE6_transvectionHom_range hij,
    map_slToAdjointE6_transvectionHom_range hij.symm, subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup _),
    inf_of_le_left (rootSubgroup_le_adjointGroup _)]

theorem ker_xLeviHom : (xLeviHom K).ker = LinearFlag.scalars 6 K := by
  rw [LinearFlag.scalars_eq_center, ← ker_slToAdjointE6]
  ext g
  simp only [MonoidHom.mem_ker, xLeviHom, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro h
    have : slToAdjointE6 K g = (e6RepConj K 0)⁻¹ * 1 * e6RepConj K 0 := by
      rw [← h]
      group
    rw [this]
    group
  · intro h
    rw [h]
    group

theorem range_xLeviHom :
    (xLeviHom K).range = EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) := by
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [EPilot.rootPerpLevi, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _),
    ← map_conj_e6RepConj_zero_rootSpan_perpRoots,
    ← a5LeviRoots_eq_perpRoots, ← map_subtype_a5Levi, ← range_slToAdjointE6, xLeviHom,
    MonoidHom.range_comp, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable (K) in
@[expose] noncomputable def xLeviEquiv :
    LinearFlag.projectiveSL 6 K ≃* EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_xLeviHom (K := K)).symm).trans
    ((QuotientGroup.quotientKerEquivRange (xLeviHom K)).trans
      (MulEquiv.subgroupCongr range_xLeviHom))

theorem subtype_comp_xLeviHom :
    (adjointGroup .E6 K).subtype.comp (xLeviHom K) =
      (MulAut.conj (e6RepConj K 0 : ModGL .E6 K)).toMonoidHom.comp
        ((adjointGroup .E6 K).subtype.comp (slToAdjointE6 K)) := by
  ext g
  rfl

theorem map_rootSL2_xLeviEquiv :
    ((LinearPilot.rootSL2 (K := K) (0 : Fin 6) 5).map (xLeviEquiv K).toMonoidHom).map
        (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).subtype =
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) := by
  have h05 : (0 : Fin 6) ≠ 5 := by decide
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [subgroupOf_map_subtype, inf_of_le_left EPilot.highRootSL2_le_adjointGroup,
    LinearPilot.rootSL2_eq, LinearPilot.blockSL, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  have hcomp : (((adjointGroup .E6 K).subtype.comp
      (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).subtype).comp
        (xLeviEquiv K).toMonoidHom).comp (LinearFlag.proj 6 K) =
      (adjointGroup .E6 K).subtype.comp (xLeviHom K) := by
    ext g
    rfl
  rw [hcomp, subtype_comp_xLeviHom, ← Subgroup.map_map,
    map_slToAdjointE6_blockSpecialLinear_pair h05,
    Subgroup.map_sup, map_conj_e6RepConj_rootSubgroup 0 (isRoot_a5Root h05),
    map_conj_e6RepConj_rootSubgroup 0 (isRoot_a5Root h05.symm), a5Root_five_zero, smul_neg,
    ← e6RepPreHigh_zero_eq, e6RepWeyl_smul_e6RepPreHigh]
  rfl

theorem isAutConjIn_rootPerpLevi_highRootSL2 :
    IsAutConjIn (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1))
      ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)) := by
  rw [← map_rootSL2_xLeviEquiv]
  exact (isAutConj_linearPilot_rootSL2 (by norm_num) 0 5).isAutConjIn_map (xLeviEquiv K)

end Model

end CFSG.SeitzReduction.E6Pilot
