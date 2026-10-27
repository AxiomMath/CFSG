module

public import CFSG.GF2Type.Smith1979.GammaU.Step5Census
public import CFSG.GF2Type.Smith1979.GammaU.Step6

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem false_of_model
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (h4 : Step4Hyp i M) (hrep : N2Rep i M)
    (hconfig : ∀ r ∈ unitaryElts i, ∀ u₁ ∈ M, ∀ u₂ ∈ M, Viol.InFrame (compOf i) u₁ r →
      Viol.InFrame (compOf i) u₂ r → Viol.F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0)) →
        HasConfig i M r)
    (hisom : ∀ m ∈ M, ∀ v, q0 (m v) = q0 v)
    (hcanon : ∀ m ∈ M, m (vecOf a0) = vecOf a0 → m ∈ gammaU)
    (hirr : ∀ W : Submodule (ZMod 2) V12, (∀ m ∈ M, ∀ w ∈ W, m w ∈ W) → W = ⊥ ∨ W = ⊤)
    {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hL : ∀ l, l ∈ L ↔ RowsSet (compOf i) l)
    (HL : Hyp (vecOf a0) (spanOf d0) L) : False := by
  have hn2 : ResPair.n2 i ≤ M := by
    obtain ⟨r₁, hr₁, r₂, hr₂, hne, Le₁, Le₂, hC₁, hC₂, heq⟩ := hrep
    obtain ⟨-, -, -, -, -, -, hle₁, -⟩ := hC₁
    obtain ⟨-, -, -, -, -, -, hle₂, -⟩ := hC₂
    rw [← heq]
    exact sup_le (candGrp_le h4 hle₁) (candGrp_le h4 hle₂)
  have h5 : Step5Hyp i M := { toStep4Hyp := h4, n2_le := hn2, config := hconfig }
  exact false_of_step6Hyp hi (M := M) ⟨hisom, h4.theta, hn2, fun k hkM hkU =>
    step5 hi h5 hrep (frameCensus_holds hi) (residualPairs_holds hi) hL HL hkM hkU, hcanon, hirr⟩

end CFSG.GF2Type.Smith1979.GammaU.StepA
