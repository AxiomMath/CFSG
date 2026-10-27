module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityOdd

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem twentySeven_dvd_fixedSubgroup_trialityD4_two_model {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Group K] [Finite K]
    (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (2 ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmodel
  have hcard' : Nat.card K' = (2 ^ f) ^ 3 := hcard
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : MulAut.congr e α ∉ inner (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  exact twentySeven_dvd_fixedSubgroup_trialityD4_two hf hcard' hσ hβ3 hβout

theorem twentySeven_dvd_fixedSubgroup_trialityD4_odd_model (h1 : EllQ1Lower)
    (h2 : MinusToralLower) (h3 : MinusEllLower) {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (K : Type) [Group K] [Finite K]
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
  exact twentySeven_dvd_fixedSubgroup_odd h1 h2 h3 hp hp5 hf hcard' hσ hβ3 hβout

end CFSG.HardMathSupport.Lang.E27Lie
