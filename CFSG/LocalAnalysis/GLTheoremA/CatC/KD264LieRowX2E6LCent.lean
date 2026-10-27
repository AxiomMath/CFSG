module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent
open CFSG.StandardType CFSG.StandardType.NoOffTwE6Three
open CFSG.RankThree.Classical2 (twistE6)

section Cent


variable {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem baseChange_rgrpConjAut (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (r : TwistedDiag.Rgrp Ω Fr) (c : twistedE6RootGroup K σ) :
    (baseChangeGL (algebraMap K Ω)
        ((rgrpConjAut le_rfl hK σ hσ Fr hFr r c : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) =
      (r : ModGL Tag.E6 Ω) *
        (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) *
        (r : ModGL Tag.E6 Ω)⁻¹ := by
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp le_rfl hK σ hσ Fr hFr).surjective r
  rw [rgrpConjAut_apply_baseChange]
  rw [RecipeExcLang.coe_twConj]
  have h1 : baseChangeGL (algebraMap K Ω) ((w : ModGL TwistTag.E6.tag K) *
        (c : ModGL TwistTag.E6.tag K) * (w : ModGL TwistTag.E6.tag K)⁻¹) =
      baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) *
        baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) *
        (baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  exact h1

theorem mem_fixSubgroup_torusAut_iff [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (u : Multiplicative (Fin 6 → ZMod 3)) (c : twistedE6RootGroup K σ) :
    c ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (torusAut hK σ hσ Fr hFr hg hgn hζ u) ↔
      (g * Psi6 hζ u * g⁻¹) *
          (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) =
        (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) *
          (g * Psi6 hζ u * g⁻¹) := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
  let r : TwistedDiag.Rgrp Ω Fr :=
    ⟨g * Psi6 hζ u * g⁻¹, (kappa Fr hg hgn ⟨Psi6 hζ u, sylP_le_thetaFixed Fr
      (Psi_mem_sylP Fr (fun c => by simpa using hFr c) hζ u)⟩).2⟩
  have hu : torusAut hK σ hσ Fr hFr hg hgn hζ u = rgrpConjAut le_rfl hK σ hσ Fr hFr r := rfl
  rw [hu]
  have h := baseChange_rgrpConjAut hK σ hσ Fr hFr r c
  have hinj : Function.Injective (baseChangeGL (algebraMap K Ω) :
      ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag Ω) :=
    baseChangeGL_injective (algebraMap K Ω)
  have hr : (r : ModGL Tag.E6 Ω) = g * Psi6 hζ u * g⁻¹ := rfl
  rw [hr] at h
  constructor
  · intro hc
    rw [hc] at h
    exact mul_inv_eq_iff_eq_mul.1 h.symm
  · intro hc
    have h2 : (baseChangeGL (algebraMap K Ω)
        ((rgrpConjAut le_rfl hK σ hσ Fr hFr r c : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) =
        (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) := by
      rw [h, hc, mul_inv_cancel_right]
    exact Subtype.ext (hinj h2)

theorem mem_iInf_fixSubgroup_torusAut_iff [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))) (c : twistedE6RootGroup K σ) :
    c ∈ (⨅ f ∈ G.map (torusAut hK σ hσ Fr hFr hg hgn hζ),
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup f) ↔
      ∀ u ∈ G, (g * Psi6 hζ u * g⁻¹) *
          (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) =
        (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) *
          (g * Psi6 hζ u * g⁻¹) := by
  simp only [Subgroup.mem_iInf, Subgroup.mem_map]
  constructor
  · intro h u hu
    exact (mem_fixSubgroup_torusAut_iff hK σ hσ Fr hFr hg hgn hζ u c).1 (h _ ⟨u, hu, rfl⟩)
  · rintro h _ ⟨u, hu, rfl⟩
    exact (mem_fixSubgroup_torusAut_iff hK σ hσ Fr hFr hg hgn hζ u c).2 (h u hu)

end Cent

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
