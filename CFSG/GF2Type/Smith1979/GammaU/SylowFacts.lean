module

public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol

structure SylowFacts (i : ℕ) : Prop where
  theta_comm : ∀ u ∈ genGrp (pGens i), ∀ v, u (theta0 v) = theta0 (u v)
  exists_noncomm_27 : ∃ T : Subgroup (V12 ≃ₗ[ZMod 2] V12), T ≤ genGrp (pGens i) ∧
    Nat.card T = 27 ∧ ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a
  card_normalizer_five_dvd : ∀ F : Subgroup (genGrp (pGens i)), Nat.card F = 5 →
    Nat.card (Subgroup.normalizer (F : Set (genGrp (pGens i)))) ∣ 30

end CFSG.GF2Type.Smith1979.GammaU.SigmaP

end
