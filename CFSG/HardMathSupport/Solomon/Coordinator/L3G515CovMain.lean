module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovTab
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovQ8
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier GriessAllModelsStatement GLAPComponent GLAPPrimeCore)
open CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns CFSG.RankThree.PartTwo.Sec4

theorem center_ne_bot_of_type {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hT : IsExtremalType Y ∨ IsSLThreeEps Y) (hZ : Subgroup.center Y ≠ ⊥) {α : MulAut Y}
    (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) {S : Subgroup Y}
    (hS : GLAPComponent 3 (fixSub α) S) : Subgroup.center (barOf 3 S) ≠ ⊥ := by
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hfd := fixData_of_type hq hT h3 hf
  obtain ⟨S0, comp, -, -, -, hO, hcen, hZS⟩ := layer_of_fixData hfd
  have hSS : S = S0 := (comp S).1 hS
  subst hSS
  intro hZ'
  have hzS : (z : Y) ∈ S := hZS z.2
  have hzcen : (⟨(z : Y), hzS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.1 z.2) w)
  have hZS' : Subgroup.center ↥S = ⊥ := center_eq_bot_of_mulEquiv' (barEquivOfCore hO) hZ'
  rw [hZS', Subgroup.mem_bot] at hzcen
  have h' : (z : Y) = 1 := by
    have := congrArg (fun w : ↥S => (w : Y)) hzcen
    simpa using this
  exact hz1 (Subtype.ext h')

theorem inputCoverFixedCentre_of_griess (hG : GriessAllModelsStatement) :
    InputCoverFixedCentre := by
  intro Y _ _ hq hO hZ α h3 hf S hS
  have hZp := isPGroup_center_of_core_eq_bot hO
  have hf0 := hf
  have key1 : α = 1 → Subgroup.center (barOf 3 S) ≠ ⊥ := by
    rintro rfl
    rw [fixSub_one] at hS
    exact center_ne_bot_of_comp_top hq hO hZ hS
  have hT_of : (IsExtremalType Y ∨ IsSLThreeEps Y) → Subgroup.center (barOf 3 S) ≠ ⊥ :=
    fun hT => center_ne_bot_of_type hq hT hZ h3 hf0 hS
  rcases hf with h1 | hL | hU
  · exact key1 h1
  · obtain ⟨K, hKf, hKfin, θ, -⟩ := hL
    exact hT_of (lbi_L3 hG hq hZp (cov_mod_three_L3 hG hq hZp hZ θ) θ)
  · obtain ⟨K, hKf, hKfin, q, θ, σ, φ, γ, hcard, -⟩ := hU
    obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    by_cases h2 : p ^ f = 2
    · exact (lbi_U3_two hq (h2 ▸ hcard) (h2 ▸ θ)).elim
    have hadm : StatedLieAdmissible .PSU 3 p f :=
      ⟨hF.prime, hF.one_le, le_refl 3, by simpa using h2⟩
    have hq3 : p ^ f % 3 = 2 := cov_mod_three_U3 hG hq hZp hZ hadm hcard θ
    by_cases h8 : p ^ f = 8
    · have hK : PiField false p f K :=
        ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
      have hmod : ModThree false (p ^ f) := hq3
      let e' := θ.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
      rcases eq_one_or_isSolvable_fix_q8 hq hK h8 e' h3 hf0 with h1 | hsol
      · exact key1 h1
      · exact (false_of_comp_of_solvable hsol hS).elim
    · exact hT_of (lbi_U3 hG hq hZp hcard hq3 h8 θ)

end CFSG.HardMathSupport.Solomon.Coordinator
