module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolarDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnG1

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

include hφ in
theorem A2Core.unSlFix_torus {t : ↥(foldFix (a2Phi h φ))}
    (ht : t ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N) :
    ∃ χ : (UnK σ)ˣ, ∀ a : UnK σ,
      t * unSlFix h φ hφ (sl2Upper a) * t⁻¹ = unSlFix h φ hφ (sl2Upper ((χ : UnK σ) * a)) ∧
      t * unSlFix h φ hφ (sl2Lower a) * t⁻¹ =
        unSlFix h φ hφ (sl2Lower (((χ⁻¹ : (UnK σ)ˣ) : UnK σ) * a)) := by
  have hBN := ((unD_spec h φ hφ).BN t).1 ht
  have htf : a2Phi h φ (t : twistedGroup σ.toRingHom) = (t : twistedGroup σ.toRingHom) :=
    mem_foldFix.1 t.2
  obtain ⟨χ, hσχ, hχ0, hχ⟩ := un_torus_slShort h φ hφ hBN htf
  have hχ0' : (⟨χ, hσχ⟩ : UnK σ) ≠ 0 := fun h0 => hχ0 (congrArg Subtype.val h0)
  refine ⟨Units.mk0 ⟨χ, hσχ⟩ hχ0', fun a => ?_⟩
  obtain ⟨hu, hl⟩ := hχ (a : K) a.2
  constructor
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_unSlFix, unSl_upper]
    exact hu
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_unSlFix, unSl_lower]
    exact hl

include hφ in
theorem A2Core.unSlFix_tau (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ μ : (UnK σ)ˣ, ∀ a : UnK σ,
      unTauX h φ ε hcomm (unSlFix h φ hφ (sl2Upper a)) =
        unSlFix h φ hφ (sl2Lower ((μ : UnK σ) * unEps ε hεσ a)) ∧
      unTauX h φ ε hcomm (unSlFix h φ hφ (sl2Lower a)) =
        unSlFix h φ hφ (sl2Upper (((μ⁻¹ : (UnK σ)ˣ) : UnK σ) * unEps ε hεσ a)) := by
  obtain ⟨μ, hμ, hu, hl⟩ := un_tauGamma_slShort h ε hεσ
  have hσμ : σ (μ : K) = (μ : K) := hμ σ.toRingHom
  have hμ0 : (⟨(μ : K), hσμ⟩ : UnK σ) ≠ 0 := fun h0 => μ.ne_zero (congrArg Subtype.val h0)
  refine ⟨Units.mk0 ⟨(μ : K), hσμ⟩ hμ0, fun a => ?_⟩
  constructor
  · refine Subtype.ext ?_
    rw [coe_unTauX, coe_unSlFix, coe_unSlFix, unSl_upper, unSl_lower, hu (a : K) a.2]
    rfl
  · refine Subtype.ext ?_
    rw [coe_unTauX, coe_unSlFix, coe_unSlFix, unSl_upper, unSl_lower, hl (a : K) a.2]
    have hmul : (((((Units.mk0 (⟨(μ : K), hσμ⟩ : UnK σ) hμ0)⁻¹ : (UnK σ)ˣ) : UnK σ) *
        unEps ε hεσ a : UnK σ) : K) = ((μ⁻¹ : Kˣ) : K) * ε (a : K) := by
      rw [Subfield.coe_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
      rfl
    rw [hmul]

include hφ in
theorem A2Core.unSlFix_field (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ δ y)) (a : UnK σ) :
    unFieldX h φ δ hcomm (unSlFix h φ hφ (sl2Upper a)) =
      unSlFix h φ hφ (sl2Upper (unEps δ hδσ a)) := by
  refine Subtype.ext ?_
  rw [coe_unFieldX, coe_unSlFix, coe_unSlFix, unSl_upper, unSl_upper,
    (un_fieldActor_slShort h δ hδσ (a : K)).1]
  rfl

end CFSG.GH74.GLS.Stage2.Bender.Thm1
