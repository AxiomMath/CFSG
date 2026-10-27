module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank


section Iso

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_slToAdjointE6 :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 6) K →* adjointGroup .E6 K,
      (∀ (i j : Fin 6) (hij : i ≠ j) (c : K),
        (φ (Matrix.SpecialLinearGroup.transvection hij c) : ModGL .E6 K) =
          pinnedX .E6 K (a5Root i j) c) ∧
      φ.ker = center (Matrix.SpecialLinearGroup (Fin 6) K) ∧ φ.range = a5Levi K :=
  ⟨slToAdjointE6 K, fun _ _ hij c => coe_slToAdjointE6_transvection hij c, ker_slToAdjointE6,
    range_slToAdjointE6⟩

variable (K) in
@[expose] noncomputable def a5LeviEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 6) K ≃* ↥(a5Levi K) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_slToAdjointE6 (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivRange (slToAdjointE6 K))).trans
    (MulEquiv.subgroupCongr range_slToAdjointE6)

theorem coe_a5LeviEquiv_mk (A : Matrix.SpecialLinearGroup (Fin 6) K) :
    ((a5LeviEquiv K (QuotientGroup.mk A) : a5Levi K) : adjointGroup .E6 K) = slToAdjointE6 K A :=
  rfl

theorem coe_a5LeviEquiv_mk_transvection {i j : Fin 6} (hij : i ≠ j) (c : K) :
    (((a5LeviEquiv K (QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection hij c)) :
        a5Levi K) : adjointGroup .E6 K) : ModGL .E6 K) = pinnedX .E6 K (a5Root i j) c :=
  coe_slToAdjointE6_transvection hij c

theorem map_slToAdjointE6_transvectionHom_range {i j : Fin 6} (hij : i ≠ j) :
    (Matrix.SpecialLinearGroup.transvectionHom (A := K) hij).range.map (slToAdjointE6 K) =
      (rootSubgroup .E6 K (a5Root i j)).subgroupOf (adjointGroup .E6 K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_rootSubgroup]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c.toAdd, by
      rw [Matrix.SpecialLinearGroup.transvectionHom_apply, coe_slToAdjointE6_transvection]⟩
  · rintro ⟨c, hc⟩
    refine ⟨_, ⟨Multiplicative.ofAdd c, rfl⟩, Subtype.ext ?_⟩
    rw [Matrix.SpecialLinearGroup.transvectionHom_apply, coe_slToAdjointE6_transvection, ← hc]
    rfl

@[expose] noncomputable def slToA5Levi :
    Matrix.SpecialLinearGroup (Fin 6) K →* ↥(a5Levi K) :=
  (slToAdjointE6 K).codRestrict (a5Levi K) slToAdjointE6_mem_a5Levi

theorem slToA5Levi_surjective : Function.Surjective (slToA5Levi (K := K)) := by
  rintro ⟨g, hg⟩
  rw [← range_slToAdjointE6] at hg
  obtain ⟨A, rfl⟩ := hg
  exact ⟨A, rfl⟩

theorem ker_slToA5Levi :
    (slToA5Levi (K := K)).ker = center (Matrix.SpecialLinearGroup (Fin 6) K) := by
  rw [← ker_slToAdjointE6]
  ext A
  simp only [MonoidHom.mem_ker, slToA5Levi]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isQuasisimple_a5Levi : CFSG.IsQuasisimple (a5Levi K) := by
  have hne : (0 : Fin 6) ≠ 1 := by decide
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num))
    slToA5Levi_surjective ⟨Matrix.SpecialLinearGroup.transvection hne 1, fun h => ?_⟩
  exact slToAdjointE6_transvection_ne_one hne one_ne_zero (congrArg Subtype.val h)

theorem center_a5Levi_eq_bot : center (a5Levi K) = ⊥ := by
  have hne : (0 : Fin 6) ≠ 1 := by decide
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num))
    slToA5Levi_surjective ker_slToA5Levi.le, ← ker_slToA5Levi, eq_bot_iff]
  rintro _ ⟨A, hA, rfl⟩
  exact hA

theorem isSimpleGroup_a5Levi : IsSimpleGroup (a5Levi K) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 6 (by norm_num) (.inl (by norm_num))
      (.inl (by norm_num))
  exact (a5LeviEquiv K).symm.isSimpleGroup

theorem isQuasisimple_open_a5Levi : CFSG.Open.IsQuasisimple (a5Levi K) :=
  ⟨(isQuasisimple_a5Levi (K := K)).1.commutator_eq_top, (isQuasisimple_a5Levi (K := K)).2.1⟩

end Iso

section Model

variable {K : Type} [Field K] {f : ℕ}

theorem lieModel_a5Levi (hK : Nat.card K = 2 ^ f) :
    CFSG.Blueprint.LieModel (a5Levi K) .PSL 6 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hadm : StatedLieAdmissible .PSL (5 + 1) 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp,
    by simp⟩
  have hmodel :
      CFSG.Blueprint.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) .PSL 6 2 f :=
    Or.inl ⟨by decide,
      CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 5 K hadm hK⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (a5LeviEquiv K) hmodel

end Model

end CFSG.SeitzReduction.E6Pilot
