module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityOddEll
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityModel
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRot

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_outer_three_normal_form)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ellQ1Lower : EllQ1Lower := ellQ1Lower_of_rotLang rotLang_holds

theorem minusEllLower (h : MinusToralLower) : MinusEllLower :=
  minusEllLower_of_rotLang rotLang_holds h

theorem twentySeven_dvd_fixedSubgroup_odd_q1 {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hα1 : α ≠ 1 := fun h => hαin ⟨1, by rw [h]; exact map_one _⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨g, hg, hφ | hφ⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ α hαord hαin
  · rw [hφ]
    exact twentySeven_dvd_cocycle_q1 ellQ1Lower hp hp2 hp3 hf hq hK σ hσ g hg
  · have := twentySeven_dvd_cocycle_q1 ellQ1Lower hp hp2 hp3 hf hq hK σ hσ g hg
    rwa [← hφ, oddFixedSubgroup_inv] at this

theorem twentySeven_dvd_fixedSubgroup_trialityD4_q1_model {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) (K : Type) [Group K] [Finite K]
    (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (p ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmodel
  have hcard' : Nat.card K' = (p ^ f) ^ 3 := hcard
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  exact twentySeven_dvd_fixedSubgroup_odd_q1 hp hp5 hf hq hcard' hσ hβ3 hβout

theorem twentySeven_dvd_fixedSubgroup_trialityD4_q2_model (h2 : MinusToralLower) {p f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (K : Type) [Group K] [Finite K]
    (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (p ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    27 ∣ Nat.card (fixedSubgroup α) :=
  twentySeven_dvd_fixedSubgroup_trialityD4_odd_model ellQ1Lower h2 (minusEllLower h2) hp hp5 hf K
    hmodel α hα3 hαin

end CFSG.HardMathSupport.Lang.E27Lie
