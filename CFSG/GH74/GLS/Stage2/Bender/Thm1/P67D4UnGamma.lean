module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnRoot
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnS1

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.un_tauGamma_slShort (h : A2Core σ d q) (ε : K ≃+* K)
    (hεσ : ∀ c, ε (σ c) = σ (ε c)) :
    ∃ μ : Kˣ, (∀ f : K →+* K, f μ = μ) ∧
      (∀ c : K, σ c = c → a2Phi h (unTau σ ε) (slShort σ.toRingHom h.cube_apply (sl2Upper c)) =
        slShort σ.toRingHom h.cube_apply (sl2Lower ((μ : K) * ε c))) ∧
      (∀ c : K, σ c = c → a2Phi h (unTau σ ε) (slShort σ.toRingHom h.cube_apply (sl2Lower c)) =
        slShort σ.toRingHom h.cube_apply (sl2Upper (((μ⁻¹ : Kˣ) : K) * ε c))) := by
  obtain ⟨μ, hμ, hu, hl⟩ := un_tau_slShort (σ := σ.toRingHom) h.cube_apply ε hεσ
  refine ⟨μ, hμ, fun c hc => ?_, fun c hc => ?_⟩
  · refine Subtype.ext (Subtype.ext (Units.ext ?_))
    have := congrArg Units.val (hu c hc)
    rw [← coe_a2Phi_unTau] at this
    exact this
  · refine Subtype.ext (Subtype.ext (Units.ext ?_))
    have := congrArg Units.val (hl c hc)
    rw [← coe_a2Phi_unTau] at this
    exact this

theorem A2Core.coe_a2Phi_fieldActor (h : A2Core σ d q) (δ : K ≃+* K)
    (x : twistedGroup σ.toRingHom) :
    (((a2Phi h (fieldActor (t := TwistTag.D4) σ δ) x : twistedGroup σ.toRingHom) :
        adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      Units.map (entrywiseHom δ.toRingHom)
        (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  show ((((a2Equiv h).symm (fieldActor (t := TwistTag.D4) σ δ (a2Equiv h x)) :
    twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = _
  rw [coe_a2Equiv_symm, coe_fieldActor, coe_a2Equiv]

theorem A2Core.un_fieldActor_slShort (h : A2Core σ d q) (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (c : K) :
    a2Phi h (fieldActor (t := TwistTag.D4) σ δ) (slShort σ.toRingHom h.cube_apply (sl2Upper c)) =
        slShort σ.toRingHom h.cube_apply (sl2Upper (δ c)) ∧
      a2Phi h (fieldActor (t := TwistTag.D4) σ δ)
          (slShort σ.toRingHom h.cube_apply (sl2Lower c)) =
        slShort σ.toRingHom h.cube_apply (sl2Lower (δ c)) := by
  have hδσ' : ∀ c, δ.toRingHom (σ.toRingHom c) = σ.toRingHom (δ.toRingHom c) := hδσ
  constructor
  · refine Subtype.ext (Subtype.ext ?_)
    rw [coe_a2Phi_fieldActor, un_coe_slShort_upper h.cube_apply, un_coe_slShort_upper h.cube_apply,
      map_mul, map_mul, units_map_entrywiseHom_xUnit, units_map_entrywiseHom_xUnit,
      units_map_entrywiseHom_xUnit]
    simp only [hδσ']
    rfl
  · refine Subtype.ext (Subtype.ext ?_)
    rw [coe_a2Phi_fieldActor, un_coe_slShort_lower h.cube_apply, un_coe_slShort_lower h.cube_apply,
      map_mul, map_mul, units_map_entrywiseHom_yUnit, units_map_entrywiseHom_yUnit,
      units_map_entrywiseHom_yUnit]
    simp only [hδσ']
    rfl

theorem A2Core.un_tauGamma_comm (h : A2Core σ d q) (ε : K ≃+* K)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) (x : twistedGroup σ.toRingHom) :
    a2Phi h (unTau σ ε) (a2Phi h φ x) = a2Phi h φ (a2Phi h (unTau σ ε) x) := by
  simp only [a2Phi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hcomm]

@[expose] def unRestrictAut {X : Type*} [Group X] (ψ : X ≃* X) (S : Subgroup X)
    (hS : ∀ x, x ∈ S ↔ ψ x ∈ S) : S ≃* S where
  toFun x := ⟨ψ x, (hS x).1 x.2⟩
  invFun x := ⟨ψ.symm x, by
    have := (hS (ψ.symm x)).2
    rw [MulEquiv.apply_symm_apply] at this
    exact this x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul ψ (x : X) (y : X))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
