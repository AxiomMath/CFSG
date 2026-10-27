module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_frobModel {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {β : MulAut Y} (hβ : IsFieldAutPSL3 β ∨ IsFieldAutPSU3 β) :
    ∃ (π : Bool) (p f : ℕ) (F : Type) (_ : Field F) (hF : PiField π p f F)
      (e : (Y ⧸ Subgroup.center Y) ≃*
        (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F))) (σ : F ≃+* F),
      (π = false → 2 < p ^ f) ∧ (π = false → Odd (orderOf σ)) ∧
        MulAut.congr e (centerDescend Y β) = centerDescend _ (frobSL hF σ) := by
  rcases hβ with hL | hU
  · obtain ⟨F, _, hfin, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    obtain ⟨p, f, hK⟩ := exists_piField_true F
    refine ⟨true, p, f, F, inferInstance, hK,
      (e.trans (γ⁻¹ : MulAut (projectiveSL 3 F))).trans (etaTrue (p ^ f) F).symm, σ,
      fun h => absurd h (by simp), fun h => absurd h (by simp), ?_⟩
    have h1 : MulAut.congr (e.trans (γ⁻¹ : MulAut (projectiveSL 3 F)))
        (centerDescend Y β) = fieldAut 3 F σ := by
      rw [congr_trans', he, congr_self]
      group
    rw [congr_trans', h1, ← congr_etaTrue_frob hK σ, congr_symm_congr]
  · obtain ⟨p, f, F, _, hF, e, σ, γ, hodd, he⟩ := fieldAutPSU3_data hU
    have hfin := hF.finite
    have hq : 2 < p ^ f := two_lt_pow_of_quasisimple hY hF e
    have hK : PiField false p f F :=
      ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false, ← pow_mul, mul_comm f 2]; exact hF.card⟩
    refine ⟨false, p, f, F, inferInstance, hK,
      (e.trans (γ⁻¹ : MulAut (unitaryPSU hF 3))).trans (etaFalse hK hq).symm, σ,
      fun _ => hq, fun _ => hodd, ?_⟩
    have h1 : MulAut.congr (e.trans (γ⁻¹ : MulAut (unitaryPSU hF 3)))
        (centerDescend Y β) = psuField hF σ := by
      rw [congr_trans', he, congr_self]
      group
    rw [congr_trans', h1, ← congr_eta_false_frob hK hq σ, congr_symm_congr]

end CFSG.HardMathSupport.Solomon.Coordinator
