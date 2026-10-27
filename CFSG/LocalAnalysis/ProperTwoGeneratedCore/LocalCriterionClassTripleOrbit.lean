module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbitConjugation

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

theorem class_triple_transporter
    {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]
    (z : G) (alpha : Ω)
    (hunique : ∀ x : Ω, rightAct x z = x ↔ x = alpha)
    (hcentralizer : ∀ x y : Ω, x ≠ alpha → y ≠ alpha →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct x c = y)
    {s s' : G}
    (hs : s ∈ {t : G | ∃ a : G, rightConjugateElem z a = t})
    (hs' : s' ∈ {t : G | ∃ b : G, rightConjugateElem z b = t})
    {gamma delta gamma' delta' : Ω}
    (hgamma : rightAct gamma s = gamma) (hgamma' : rightAct gamma' s' = gamma')
    (hdelta : delta ≠ gamma) (hdelta' : delta' ≠ gamma') :
    ∃ g : G,
      rightAct gamma g = gamma' ∧ rightAct delta g = delta' ∧
      rightAct (rightAct delta s) g = rightAct delta' s' ∧ rightConjugateElem s g = s' := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := hs'
  have hgammaa : gamma = rightAct alpha a :=
    (unique_fixed_point_rightConjugateElem hunique a gamma).mp hgamma
  have hgammab : gamma' = rightAct alpha b :=
    (unique_fixed_point_rightConjugateElem hunique b gamma').mp hgamma'
  have hdelta0 : rightAct delta a⁻¹ ≠ alpha := by
    intro heq
    apply hdelta
    calc
      delta = rightAct (rightAct delta a⁻¹) a := by
        rw [rightAct_mul, inv_mul_cancel, rightAct_one]
      _ = rightAct alpha a := by rw [heq]
      _ = gamma := hgammaa.symm
  have hdelta0' : rightAct delta' b⁻¹ ≠ alpha := by
    intro heq
    apply hdelta'
    calc
      delta' = rightAct (rightAct delta' b⁻¹) b := by
        rw [rightAct_mul, inv_mul_cancel, rightAct_one]
      _ = rightAct alpha b := by rw [heq]
      _ = gamma' := hgammab.symm
  obtain ⟨c, hc, hdc⟩ := hcentralizer _ _ hdelta0 hdelta0'
  have hca : rightAct alpha c = alpha := centralizer_fixes_unique_point hunique c hc
  have hgamma0 : rightAct gamma a⁻¹ = alpha := by
    rw [hgammaa, rightAct_inv_cancel]
  have hgammamap : rightAct gamma (a⁻¹ * c * b) = gamma' := by
    rw [← rightAct_mul, ← rightAct_mul, hgamma0, hca]
    exact hgammab.symm
  have hdeltamap : rightAct delta (a⁻¹ * c * b) = delta' := by
    rw [← rightAct_mul, ← rightAct_mul, hdc, rightAct_mul, inv_mul_cancel, rightAct_one]
  have hcomm : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hzc : rightConjugateElem z c = z := by
    change c⁻¹ * z * c = z
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  have hconj : rightConjugateElem (rightConjugateElem z a) (a⁻¹ * c * b) =
      rightConjugateElem z b := by
    calc
      rightConjugateElem (rightConjugateElem z a) (a⁻¹ * c * b) =
          rightConjugateElem (rightConjugateElem z c) b := by
        simp only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      _ = rightConjugateElem z b := by rw [hzc]
  refine ⟨a⁻¹ * c * b, hgammamap, hdeltamap, ?_, hconj⟩
  calc
    rightAct (rightAct delta (rightConjugateElem z a)) (a⁻¹ * c * b) =
        rightAct (rightAct delta (a⁻¹ * c * b))
          (rightConjugateElem (rightConjugateElem z a) (a⁻¹ * c * b)) :=
      (rightAct_rightConjugateElem delta (rightConjugateElem z a) (a⁻¹ * c * b)).symm
    _ = rightAct delta' (rightConjugateElem z b) := by rw [hdeltamap, hconj]

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
