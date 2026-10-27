module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnDefs

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

section Tau

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem unz_conj_rootDiagUnit (a : Fin TwistTag.D4.tag.rank → Kˣ) :
    trialityOpposition K * rootDiagUnit TwistTag.D4.tag a * (trialityOpposition K)⁻¹ =
      rootDiagUnit TwistTag.D4.tag a⁻¹ :=
  conj_rootDiagUnit_of_smul_eq_neg trialityOpposition_mem_monomialSubgroup
    weylQuotientHom_trialityOpposition_smul a

theorem coe_unTau (σ ε : K ≃+* K) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ((unTau σ ε y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      trialityOpposition K * Units.map (entrywiseHom ε.toRingHom) (y : ModGL TwistTag.D4.tag K) *
        (trialityOpposition K)⁻¹ := by
  rw [unTau_apply]
  rfl


omit
  [Finite K] in
theorem unVec_aux (ε : K ≃+* K) (b : Kˣ) (hb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹)
    (i : Fin 4) : Units.map ε.toRingHom.toMonoidHom (![1, 1, b, 1] i) = (![1, 1, b, 1] i)⁻¹ := by
  fin_cases i
  · simp
  · simp
  · simpa using hb
  · simp

theorem coe_toralPhi (σ : K ≃+* K) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    (((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      (s : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom σ.toRingHom)
        (y : ModGL TwistTag.D4.tag K) * (s : ModGL TwistTag.D4.tag K)⁻¹ := by
  rfl

theorem unTau_comm_phi (σ ε : K ≃+* K) (hcomm : ∀ c, σ (ε c) = ε (σ c)) (b : Kˣ)
    (hb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1])
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    unTau σ ε ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) y) =
      (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) (unTau σ ε y) := by
  refine Subtype.ext ?_
  rw [coe_unTau, coe_toralPhi, coe_toralPhi, coe_unTau]
  set z := trialityOpposition K with hz
  set Y := (y : ModGL TwistTag.D4.tag K) with hY
  set S := (s : ModGL TwistTag.D4.tag K) with hS
  obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.tag.rank → Kˣ, a = ![1, 1, b, 1] := ⟨_, rfl⟩
  have hs' : S = rootDiagUnit TwistTag.D4.tag a := by rw [ha]; exact hs
  have hcomp : Units.map (entrywiseHom σ.toRingHom) (Units.map (entrywiseHom ε.toRingHom) Y) =
      Units.map (entrywiseHom ε.toRingHom) (Units.map (entrywiseHom σ.toRingHom) Y) := by
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp,
      show σ.toRingHom.comp ε.toRingHom = ε.toRingHom.comp σ.toRingHom from RingHom.ext hcomm]
  have hSz : Units.map (entrywiseHom σ.toRingHom) z = z :=
    units_map_entrywiseHom_trialityOpposition _
  have hEs : Units.map (entrywiseHom ε.toRingHom) S = S⁻¹ := by
    rw [hs', units_map_entrywiseHom_rootDiagUnit (t := TwistTag.D4),
      rootDiagUnit_inv (τ := TwistTag.D4.tag)]
    congr 1
    funext i
    rw [ha]
    exact unVec_aux ε b hb i
  have hzs : z * S⁻¹ * z⁻¹ = S := by
    rw [hs', rootDiagUnit_inv (τ := TwistTag.D4.tag), hz, unz_conj_rootDiagUnit, inv_inv]
  have hzs' : z * S * z⁻¹ = S⁻¹ := by
    rw [hs', hz, unz_conj_rootDiagUnit, rootDiagUnit_inv (τ := TwistTag.D4.tag)]
  simp only [map_mul, map_inv, hSz, hEs, inv_inv, hcomp]
  generalize Units.map (entrywiseHom ε.toRingHom) (Units.map (entrywiseHom σ.toRingHom) Y) = E
  clear_value z S
  have e1 : z * (S⁻¹ * E * S) * z⁻¹ = (z * S⁻¹ * z⁻¹) * (z * E * z⁻¹) * (z * S * z⁻¹) := by
    simp [mul_assoc]
  rw [e1, hzs, hzs']

theorem unTau_sq_apply (σ ε : K ≃+* K) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    unTau σ ε (unTau σ ε y) = fieldActor (t := TwistTag.D4) σ (ε * ε) y := by
  refine Subtype.ext ?_
  rw [coe_unTau, coe_unTau, coe_fieldActor]
  set z := trialityOpposition K with hz
  have hEz : Units.map (entrywiseHom ε.toRingHom) z = z :=
    units_map_entrywiseHom_trialityOpposition _
  have hzz : z * z = 1 := by
    have := trialityOpposition_sq (K := K)
    rwa [pow_two] at this
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  rw [units_map_entrywiseHom_mul_ringEquiv]
  simp only [map_mul, hEz, hz1]
  generalize Units.map (entrywiseHom ε.toRingHom) (Units.map (entrywiseHom ε.toRingHom)
    (y : ModGL TwistTag.D4.tag K)) = E
  clear_value z
  calc z * (z * E * z) * z = (z * z) * E * (z * z) := by simp [mul_assoc]
    _ = E := by rw [hzz]; simp

theorem unTau_pow_four (σ ε : K ≃+* K) (hε : ∀ c, ε (ε (ε (ε c))) = c) :
    unTau σ ε ^ 4 = 1 := by
  have h2 : unTau σ ε ^ 2 = fieldActor (t := TwistTag.D4) σ (ε * ε) := by
    ext y : 1
    rw [pow_two, MulAut.mul_apply, unTau_sq_apply]
  have h4 : fieldActor (t := TwistTag.D4) σ (ε * ε) * fieldActor (t := TwistTag.D4) σ (ε * ε) =
      1 := by
    rw [← fieldActor_mul]
    have : (ε * ε) * (ε * ε) = (1 : RingAut K) := RingEquiv.ext fun c => hε c
    rw [this, fieldActor_one]
  calc unTau σ ε ^ 4 = (unTau σ ε ^ 2) * (unTau σ ε ^ 2) := by rw [← pow_add]
    _ = 1 := by rw [h2, h4]


end Tau

end CFSG.GH74.GLS.Stage2.Bender.Thm1
