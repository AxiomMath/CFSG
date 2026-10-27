module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.SP.Identify
public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.GH74.GLS.Stage4.HexRev
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.RankTwo.ModelG2Words

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

section Mult

variable {K : Type} [Field K]

theorem un_conj_xUnit (j : Fin TwistTag.D4.tag.rank) :
    ∃ μ : Kˣ, ∀ c : K, trialityOpposition K * xUnit TwistTag.D4.tag K j c *
      (trialityOpposition K)⁻¹ = yUnit TwistTag.D4.tag K j ((μ : K) * c) := by
  obtain ⟨μ, hμ⟩ := conj_pinnedX_of_smul_eq_neg
    (trialityOpposition_mem_monomialSubgroup (K := K)) weylQuotientHom_trialityOpposition_smul
    (isRoot_single TwistTag.D4.tag j)
  refine ⟨μ, fun c => ?_⟩
  have h := hμ c
  rwa [pinnedX_single, pinnedX_neg_single] at h

theorem un_yUnit_injective (j : Fin TwistTag.D4.tag.rank) :
    Function.Injective (yUnit TwistTag.D4.tag K j) := fun a b hab =>
  pinnedX_injective (R := K) (τ := TwistTag.D4.tag) (-Pi.single j 1)
    (by rwa [pinnedX_neg_single, pinnedX_neg_single])

theorem un_mu_fixed_x (j : Fin TwistTag.D4.tag.rank) (f : K →+* K) {μ : Kˣ}
    (hμ : ∀ c : K, trialityOpposition K * xUnit TwistTag.D4.tag K j c *
      (trialityOpposition K)⁻¹ = yUnit TwistTag.D4.tag K j ((μ : K) * c)) : f μ = μ := by
  have h1 := congrArg (Units.map (entrywiseHom f)) (hμ 1)
  rw [map_mul, map_mul, map_inv, units_map_entrywiseHom_trialityOpposition,
    units_map_entrywiseHom_xUnit, units_map_entrywiseHom_yUnit] at h1
  have h2 := hμ (f 1)
  rw [h2] at h1
  have h3 := un_yUnit_injective j h1
  simpa using h3.symm

theorem un_diag_conj_xUnit (j : Fin TwistTag.D4.tag.rank) (c : K) :
    diagramMap TwistTag.D4 K * xUnit TwistTag.D4.tag K j c * (diagramMap TwistTag.D4 K)⁻¹ =
      xUnit TwistTag.D4.tag K (TwistTag.D4.perm j) c := by
  have h := twistHom_xUnit (t := TwistTag.D4) (K := K) (σ := RingHom.id K) j c
  rw [twistHom_apply] at h
  have e : Units.map (entrywiseHom (RingHom.id K)) (xUnit TwistTag.D4.tag K j c) =
      xUnit TwistTag.D4.tag K j c := Units.ext (entrywise_id _)
  rw [e] at h
  simpa using h

theorem un_diag_conj_yUnit (j : Fin TwistTag.D4.tag.rank) (c : K) :
    diagramMap TwistTag.D4 K * yUnit TwistTag.D4.tag K j c * (diagramMap TwistTag.D4 K)⁻¹ =
      yUnit TwistTag.D4.tag K (TwistTag.D4.perm j) c := by
  have h := twistHom_yUnit (t := TwistTag.D4) (K := K) (σ := RingHom.id K) j c
  rw [twistHom_apply] at h
  have e : Units.map (entrywiseHom (RingHom.id K)) (yUnit TwistTag.D4.tag K j c) =
      yUnit TwistTag.D4.tag K j c := Units.ext (entrywise_id _)
  rw [e] at h
  simpa using h

theorem un_mu_perm_x (j : Fin TwistTag.D4.tag.rank) {μ μ' : Kˣ}
    (hμ : ∀ c : K, trialityOpposition K * xUnit TwistTag.D4.tag K j c *
      (trialityOpposition K)⁻¹ = yUnit TwistTag.D4.tag K j ((μ : K) * c))
    (hμ' : ∀ c : K, trialityOpposition K * xUnit TwistTag.D4.tag K (TwistTag.D4.perm j) c *
      (trialityOpposition K)⁻¹ = yUnit TwistTag.D4.tag K (TwistTag.D4.perm j) ((μ' : K) * c)) :
    μ' = μ := by
  have hP := diagramMap_comm_trialityOpposition (L := K)
  have h1 := hμ' 1
  rw [← un_diag_conj_xUnit j 1] at h1
  set P := diagramMap TwistTag.D4 K
  set z := trialityOpposition K
  have e : z * (P * xUnit TwistTag.D4.tag K j 1 * P⁻¹) * z⁻¹ =
      P * (z * xUnit TwistTag.D4.tag K j 1 * z⁻¹) * P⁻¹ := by
    calc z * (P * xUnit TwistTag.D4.tag K j 1 * P⁻¹) * z⁻¹
        = (z * P) * xUnit TwistTag.D4.tag K j 1 * (z * P)⁻¹ := by group
      _ = (P * z) * xUnit TwistTag.D4.tag K j 1 * (P * z)⁻¹ := by rw [← hP]
      _ = P * (z * xUnit TwistTag.D4.tag K j 1 * z⁻¹) * P⁻¹ := by group
  rw [e, hμ 1, un_diag_conj_yUnit] at h1
  have h2 := un_yUnit_injective (TwistTag.D4.perm j) h1.symm
  exact Units.ext (by simpa using h2)

theorem un_conj_xOuter :
    ∃ μ : Kˣ, (∀ f : K →+* K, f μ = μ) ∧
      (∀ c d e : K, trialityOpposition K * (xUnit TwistTag.D4.tag K (nd 0) c *
          xUnit TwistTag.D4.tag K (nd 1) d * xUnit TwistTag.D4.tag K (nd 3) e) *
          (trialityOpposition K)⁻¹ = yUnit TwistTag.D4.tag K (nd 0) ((μ : K) * c) *
          yUnit TwistTag.D4.tag K (nd 1) ((μ : K) * d) *
          yUnit TwistTag.D4.tag K (nd 3) ((μ : K) * e)) ∧
      (∀ c d e : K, trialityOpposition K * (yUnit TwistTag.D4.tag K (nd 0) c *
          yUnit TwistTag.D4.tag K (nd 1) d * yUnit TwistTag.D4.tag K (nd 3) e) *
          (trialityOpposition K)⁻¹ = xUnit TwistTag.D4.tag K (nd 0) (((μ⁻¹ : Kˣ) : K) * c) *
          xUnit TwistTag.D4.tag K (nd 1) (((μ⁻¹ : Kˣ) : K) * d) *
          xUnit TwistTag.D4.tag K (nd 3) (((μ⁻¹ : Kˣ) : K) * e)) := by
  obtain ⟨μ₀, h₀⟩ := un_conj_xUnit (K := K) (nd 0)
  obtain ⟨μ₁, h₁⟩ := un_conj_xUnit (K := K) (nd 1)
  obtain ⟨μ₃, h₃⟩ := un_conj_xUnit (K := K) (nd 3)
  have e1 : μ₁ = μ₀ := un_mu_perm_x (nd 0) h₀ h₁
  have e3 : μ₃ = μ₀ := by
    rw [← e1]
    exact un_mu_perm_x (nd 1) h₁ h₃
  rw [e1] at h₁
  rw [e3] at h₃
  have hzz : trialityOpposition K * trialityOpposition K = 1 := by
    have := trialityOpposition_sq (K := K)
    rwa [pow_two] at this
  have hz1 : (trialityOpposition K)⁻¹ = trialityOpposition K := inv_eq_of_mul_eq_one_right hzz
  have hy : ∀ j : Fin TwistTag.D4.tag.rank, (∀ c : K, trialityOpposition K *
      xUnit TwistTag.D4.tag K j c * (trialityOpposition K)⁻¹ =
        yUnit TwistTag.D4.tag K j ((μ₀ : K) * c)) → ∀ c : K, trialityOpposition K *
      yUnit TwistTag.D4.tag K j c * (trialityOpposition K)⁻¹ =
        xUnit TwistTag.D4.tag K j (((μ₀⁻¹ : Kˣ) : K) * c) := by
    intro j hj c
    have h := hj (((μ₀⁻¹ : Kˣ) : K) * c)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    set z := trialityOpposition K
    calc z * (z * xUnit TwistTag.D4.tag K j (((μ₀⁻¹ : Kˣ) : K) * c) * z⁻¹) * z⁻¹
        = (z * z) * xUnit TwistTag.D4.tag K j (((μ₀⁻¹ : Kˣ) : K) * c) * (z * z)⁻¹ := by group
      _ = _ := by rw [hzz]; simp
  refine ⟨μ₀, fun f => un_mu_fixed_x (nd 0) f h₀, fun c d e => ?_, fun c d e => ?_⟩
  · calc trialityOpposition K * (xUnit TwistTag.D4.tag K (nd 0) c *
          xUnit TwistTag.D4.tag K (nd 1) d * xUnit TwistTag.D4.tag K (nd 3) e) *
          (trialityOpposition K)⁻¹
        = (trialityOpposition K * xUnit TwistTag.D4.tag K (nd 0) c * (trialityOpposition K)⁻¹) *
          (trialityOpposition K * xUnit TwistTag.D4.tag K (nd 1) d * (trialityOpposition K)⁻¹) *
          (trialityOpposition K * xUnit TwistTag.D4.tag K (nd 3) e * (trialityOpposition K)⁻¹) := by
          group
      _ = _ := by rw [h₀, h₁, h₃]
  · calc trialityOpposition K * (yUnit TwistTag.D4.tag K (nd 0) c *
          yUnit TwistTag.D4.tag K (nd 1) d * yUnit TwistTag.D4.tag K (nd 3) e) *
          (trialityOpposition K)⁻¹
        = (trialityOpposition K * yUnit TwistTag.D4.tag K (nd 0) c * (trialityOpposition K)⁻¹) *
          (trialityOpposition K * yUnit TwistTag.D4.tag K (nd 1) d * (trialityOpposition K)⁻¹) *
          (trialityOpposition K * yUnit TwistTag.D4.tag K (nd 3) e * (trialityOpposition K)⁻¹) := by
          group
      _ = _ := by rw [hy _ h₀, hy _ h₁, hy _ h₃]

end Mult

section Slice

variable {K : Type} [Field K]

theorem un_coe_xPar_single (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K j c := by
  rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]

theorem un_coe_xPar_neg_single (j : Fin d4.rank) (c : K) :
    ((xPar (rootOperatorFamily d4) (-Pi.single j 1) c : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K j c := by
  rw [xPar_neg_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_neg_simple]

theorem un_coe_xOuter_one (c d e : K) :
    ((xOuter 1 c d e : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K (nd 0) c * xUnit d4 K (nd 1) d * xUnit d4 K (nd 3) e := by
  rw [xOuter, Subgroup.coe_mul, Subgroup.coe_mul, one_smul, one_smul, one_smul,
    un_coe_xPar_single, un_coe_xPar_single, un_coe_xPar_single]

theorem un_coe_xOuter_neg_one (c d e : K) :
    ((xOuter (-1) c d e : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K (nd 0) c * yUnit d4 K (nd 1) d * yUnit d4 K (nd 3) e := by
  rw [xOuter, Subgroup.coe_mul, Subgroup.coe_mul, neg_one_smul, neg_one_smul, neg_one_smul,
    un_coe_xPar_neg_single, un_coe_xPar_neg_single, un_coe_xPar_neg_single]

end Slice

section E1

variable {K : Type} [Field K] {σ : K →+* K}

theorem un_coe_slShort_upper (hσ3 : ∀ c, σ (σ (σ c)) = c) (c : K) :
    (((slShort σ hσ3 (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) : ModGL d4 K) =
      xUnit d4 K (nd 0) c * xUnit d4 K (nd 1) (σ c) * xUnit d4 K (nd 3) (σ (σ c)) := by
  rw [slShort_upper, un_coe_xOuter_one]

theorem un_coe_slShort_lower (hσ3 : ∀ c, σ (σ (σ c)) = c) (c : K) :
    (((slShort σ hσ3 (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) : ModGL d4 K) =
      yUnit d4 K (nd 0) c * yUnit d4 K (nd 1) (σ c) * yUnit d4 K (nd 3) (σ (σ c)) := by
  rw [slShort_lower, un_coe_xOuter_neg_one]

theorem un_tau_slShort (hσ3 : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hεσ : ∀ c, ε (σ c) = σ (ε c)) :
    ∃ μ : Kˣ, (∀ f : K →+* K, f μ = μ) ∧
      (∀ c : K, σ c = c → trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
          (((slShort σ hσ3 (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) :
            ModGL d4 K) * (trialityOpposition K)⁻¹ =
        (((slShort σ hσ3 (sl2Lower ((μ : K) * ε.toRingHom c)) : twistedGroup σ) :
            adjointGroup d4 K) : ModGL d4 K)) ∧
      (∀ c : K, σ c = c → trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
          (((slShort σ hσ3 (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) :
            ModGL d4 K) * (trialityOpposition K)⁻¹ =
        (((slShort σ hσ3 (sl2Upper (((μ⁻¹ : Kˣ) : K) * ε.toRingHom c)) : twistedGroup σ) :
            adjointGroup d4 K) : ModGL d4 K)) := by
  obtain ⟨μ, hμ, hxy, hyx⟩ := un_conj_xOuter (K := K)
  refine ⟨μ, hμ, fun c hc => ?_, fun c hc => ?_⟩
  · have hσεc : σ (ε.toRingHom c) = ε.toRingHom c := by
      change σ (ε c) = ε c
      rw [← hεσ, hc]
    have hσμ : σ ((μ : K) * ε.toRingHom c) = (μ : K) * ε.toRingHom c := by
      rw [map_mul, hμ σ, hσεc]
    rw [un_coe_slShort_upper hσ3, un_coe_slShort_lower hσ3, hc, map_mul, map_mul,
      units_map_entrywiseHom_xUnit, units_map_entrywiseHom_xUnit, units_map_entrywiseHom_xUnit]
    rw [hxy]
    simp only [hσμ, hc]
  · have hσεc : σ (ε.toRingHom c) = ε.toRingHom c := by
      change σ (ε c) = ε c
      rw [← hεσ, hc]
    have hσμ : σ (((μ⁻¹ : Kˣ) : K) * ε.toRingHom c) = ((μ⁻¹ : Kˣ) : K) * ε.toRingHom c := by
      have h1 : σ ((μ⁻¹ : Kˣ) : K) = ((μ⁻¹ : Kˣ) : K) := by
        have := hμ σ
        rw [Units.val_inv_eq_inv_val, map_inv₀, this]
      rw [map_mul, h1, hσεc]
    rw [un_coe_slShort_lower hσ3, un_coe_slShort_upper hσ3, hc, map_mul, map_mul,
      units_map_entrywiseHom_yUnit, units_map_entrywiseHom_yUnit, units_map_entrywiseHom_yUnit]
    rw [hyx]
    simp only [hσμ, hc]

end E1

end CFSG.GH74.GLS.Stage2.Bender.Thm1
