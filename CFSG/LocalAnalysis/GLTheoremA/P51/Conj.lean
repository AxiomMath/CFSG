module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P51

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_pQuot_gLBConj (p : ℕ) (g : G) (K : Subgroup G) :
    Nonempty (PQuot p (GLBConj g K) ≃* PQuot p K) :=
  ⟨(CFSG.LocalAnalysis.GLTheoremB.conjQuotEquiv p g K).symm⟩

theorem commutator_le_normalizer_of_forall {p : ℕ} {X J D Q : Subgroup G}
    (hJ : GLAPComponent p X J) (hQX : Q ≤ X)
    (hD : ∀ K : Subgroup G, GLAPComponent p X K → Nonempty (PQuot p K ≃* PQuot p J) →
      D ≤ Subgroup.normalizer (K : Set G)) :
    (⁅D, Q⁆ : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := by
  refine Subgroup.commutator_le.2 fun d hd q hq => ?_
  have hqX : q ∈ X := hQX hq
  have hXq : GLBConj q X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hqX)
  have hK : GLAPComponent p X (GLBConj q J) := by
    have h := glaPComponent_gLBConj hJ q
    rwa [hXq] at h
  have hDK : D ≤ Subgroup.normalizer (GLBConj q J : Set G) :=
    hD (GLBConj q J) hK (nonempty_pQuot_gLBConj p q J)
  have hDJ : D ≤ Subgroup.normalizer (J : Set G) := hD J hJ ⟨MulEquiv.refl _⟩
  have hdJ : GLBConj d J = J := mem_normalizer_iff_gLBConj_eq.1 (hDJ hd)
  have hdK : GLBConj d⁻¹ (GLBConj q J) = GLBConj q J :=
    mem_normalizer_iff_gLBConj_eq.1 (inv_mem (hDK hd))
  have hqK : GLBConj q⁻¹ (GLBConj q J) = J := by
    rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
  rw [mem_normalizer_iff_gLBConj_eq, commutatorElement_def,
    ← gLBConj_gLBConj q⁻¹ (d * q * d⁻¹) J, ← gLBConj_gLBConj d⁻¹ (d * q) J,
    ← gLBConj_gLBConj q d J, hdJ, hdK, hqK]

end CFSG.LocalAnalysis.GLTheoremA.P51
