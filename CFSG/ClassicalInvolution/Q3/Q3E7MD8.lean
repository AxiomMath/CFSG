module

public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.ModelFacts.E8D8AdjPair
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.LieType.Universal.Spin
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Model

theorem yData3_D8 (hadm : StatedLieAdmissible .POmegaPlus 8 3 1) : YData3 .POmegaPlus 8 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 8 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField 3 1)
    (by norm_num : 3 ≤ 8) (by norm_num : 4 ≤ 8)
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 8 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .POmegaPlus)
    (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 8; decide⟩) (hl ⟨0, by show 0 < 8; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .POmegaPlus)
    (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D
    (k := ⟨1, by show 1 < 8; decide⟩) (hl ⟨1, by show 1 < 8; decide⟩ trivial)
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    fun w hw h3 => absurd (h3.trans (orderOf_dvd_of_pow_eq_one
      (pow_four_of_mem_center_spinPlus (by norm_num : 3 ≤ 8) hw))) (by norm_num)⟩

theorem centralQuot3_plus8 :
    CentralQuot3 (spinAction (quadPlus 8 (GaloisField 3 1)))
      (fundamentalSubgroups .POmegaPlus (plusDatum 8 (GaloisField 3 1) (by norm_num)))
      (fundSet (quadPlus 8 (GaloisField 3 1)))
      (scalars (GaloisField 3 1) (Fin 8 ⊕ Fin 8 → GaloisField 3 1)) := by
  have hm3 : 3 ≤ 8 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 8 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := yData3_D8 hadm
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  have hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 8 (GaloisField 3 1) hm3),
      Pow3 R := by
    have := hY.pow3
    rw [e] at this
    exact this
  have hcentral : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 8 (GaloisField 3 1) hm3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 8 (GaloisField 3 1))) → r = 1 := by
    have := hY.central
    rw [e] at this
    exact this
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum 8 (GaloisField 3 1) hm3) := by
    have := hY.sc
    rw [e] at this
    exact this
  have hker := ker_spinAction_le_center (quadPlus 8 (GaloisField 3 1))
  exact
    { ker_le := hker
      cop := fun z hz h3 => by
        have h2 : z ^ 2 = 1 := by
          rw [pow_two]
          exact ModelFacts.OrthAut.plus_hker2 8 z hz
        have := orderOf_dvd_of_pow_eq_one h2
        have := h3.trans this
        omega
      center_le := fun z hz => spinAction_center_mem_scalars hm3 hz
      pow3 := hpow
      inj := fun R hR r hr h1 => hcentral R hR r hr (hker h1)
      map_mem := fun R hR => map_mem_fundSet hm3 hsc hR
      surj := fun L hL => exists_map_eq hm3 odd_gf3 hL }

end Model

theorem d8NoThreeAdj3 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1 := by
  have hdim : Module.finrank (GaloisField 3 1) (Fin 8 ⊕ Fin 8 → GaloisField 3 1) = 16 := by
    rw [finrank_plus]
  unfold TypeE8.D8NoThreeAdjPairs
  rw [RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num : 3 ≤ 8)]
  intro P hfund hadj hcomm
  choose ι hι using fun i j => centralQuot3_plus8.map_mem _ (hfund i j)
  exact ModelFacts.E8D8.false_of_three_adjacent_pairs odd_gf3 (by omega) (by omega)
    (fun i j => (P i j).map (spinAction (quadPlus 8 (GaloisField 3 1)))) ι hι
    (fun i => centralQuot3_plus8.modelAdj (hfund i 0) (hfund i 1) (hadj i).1)
    (fun i i' h j j' => (centralQuot3_plus8.commutes_iff (hfund i j)).mpr (hcomm i i' h j j'))

end CFSG.ClassicalInvolution.Q3.Q3W
