module

public import CFSG.ClassicalInvolution.Q3.Q3VF4CNodes
public import CFSG.ClassicalInvolution.Q3.Q3VRowModel

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic
  (Commutes FundamentalSingleClass fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane stdPlane)
open scoped MatrixGroups


theorem f4_cartan_01 : Tag.cartan .F4 (f4Node 0) (f4Node 1) = -1 := by decide
theorem f4_cartan_10 : Tag.cartan .F4 (f4Node 1) (f4Node 0) = -1 := by decide
theorem f4Node_zero_ne_one : f4Node 0 ≠ f4Node 1 := by decide
theorem f4_sl3_witness_01 :
    ¬ (3 : ℤ) ∣ Tag.cartan .F4 (f4Node 0) (f4Node 2) +
      2 * Tag.cartan .F4 (f4Node 1) (f4Node 2) := by
  decide

theorem nonempty_extModel3_F4 (hC : Q3Z.V6Collapse) :
    Nonempty (Q3W.ExtModel3 .F4 0 .PSp 3 1) := by
  set F := GaloisField 3 1 with hF
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .F4 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : StatedLieAdmissible .PSp 3 3 1 := statedLieAdmissible_psp_rank (by norm_num)
  obtain ⟨Θ, hΘker, hΘrange, hΘblk⟩ := exists_psi_C3_F4_three hC
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum F).isFiniteType
    (Dv := (f4Datum F).divisible) rfl
  obtain ⟨C, -, hC'⟩ := f4_commutatorFormula F O
  have hE := f4_chevalleyExtras F O C hC'
  obtain ⟨-, W₀, hW₀⟩ := ModelFacts.standardPair_of_chevalleyExtras hE rfl
    (i := f4Node 0) (j := f4Node 1) (k := f4Node 2) f4Node_zero_ne_one f4_cartan_01 f4_cartan_10
    f4_sl3_witness_01
  have hpT := (Q3W.pow3_of_stdPair Q3W.card_gf3 hW₀).1
  have hR₀T : rankOne (f4Datum F).rootGroup (f4Node 0) ∈
      fundamentalSubgroups .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    rankOne_mem_fund (F := F) (k := f4Node 0) (by decide)
  have hscT : FundamentalSingleClass .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .F4 0 3 1 hp trivial hadm (by decide) (by decide)
  have hscY : FundamentalSingleClass .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D :=
    fundamentalSingleClass_psp_rank 3 (by norm_num)
  have hR₀Y : (longBlock F 3 (Fin.last 2)).range ∈
      fundamentalSubgroups .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D :=
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadmY _).2
      ⟨stdPlane F 3 (Fin.last 2), isHyperbolicPlane_stdPlane _, (planeGroup_stdPlane _).symm⟩
  have hΘ₀ : (longBlock F 3 (Fin.last 2)).range.map Θ ∈
      fundamentalSubgroups .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D := by
    have h1 : (longBlock F 3 (Fin.last 2)).range.map Θ =
        rankOne (f4Datum F).rootGroup (f4Node 1) := by
      rw [Models.SymplecticPairs.range_longBlock_eq_rankOne (by show ¬ 2 + 1 < 3; omega)]
      exact hΘblk (Fin.last 2)
    rw [h1]
    exact rankOne_mem_fund (F := F) (k := f4Node 1) (by decide)
  have hRθ : rankOneHiF4 F ∈ fundamentalSubgroups .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    rankOneHiF4_mem_fund
  have hcomm : Commutes Θ.range (rankOneHiF4 F) := by
    rw [hΘrange]
    refine commutes_iSup_left.mpr fun k => ?_
    refine (commutes_rankOneHiF4 (F := F) (j := c3Node k) ?_).symm
    fin_cases k <;> decide
  have hcopT : ∀ z ∈ Subgroup.center (modelUniv .F4 0 3 1 Nat.prime_three).K,
      ¬ 3 ∣ orderOf z := by
    intro z hz
    have hz1 : z = 1 := by
      have hz' : (z : ↥(adjointGroup .F4 (GaloisField 3 1))) ∈
          Subgroup.center ↥(adjointGroup .F4 (GaloisField 3 1)) := hz
      rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot] at hz'
      exact Subgroup.mem_bot.mp hz'
    rw [hz1, orderOf_one]
    omega
  exact Q3W.nonempty_extModel3U_one hscT hscY hR₀T hpT hR₀Y
    (Q3W.pow3_range_sl2 Q3W.card_gf3 _) hRθ Θ hΘker hΘ₀ hcomm hcopT
    (fun _ hz => Q3Z.orderOf_not_dvd_three_of_center_sp (by omega) hz)

end CFSG.ClassicalInvolution.Q3.Q3V
