module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Plus
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem not_cube_dvd_card_L34 {q : ℕ} (hq : 5 ≤ q) (h : q ^ 3 ∣ 20160) : False := by
  have hle : q ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hq27 : q ≤ 27 := by
    by_contra hcon
    push Not at hcon
    have h28 : 28 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hcon 3
    omega
  interval_cases q <;> norm_num at h


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

set_option maxHeartbeats 400000 in
theorem noL34Layer_a2_plus (h : A2Std σ d q) (hq5 : 5 ≤ q)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    NoL34Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  set φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφdef
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  haveI := a2_finite h
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv _ (a2Equiv h).toEquiv
  have hFD := a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  obtain ⟨S, hSn, hsol, hperf, hsimple, hUS⟩ := fold_residual_simple hFD hgen
    (fun g _ hcomm => a2_hZ h hcomm) (fun x hx => a2_hz h φ hφ x hx) (a2_hC h φ hφ)
    (a2SlFixHom h φ hφ).range (a2SlFixHom_range_perfect h φ hφ) (a2_root_one_le_range h φ hφ)
  let e0 : ↥(foldFix (a2Phi h φ)) ≃* ↥(fixSub φ) :=
    (MulEquiv.subgroupMap (a2Equiv h) (foldFix (a2Phi h φ))).trans
      (MulEquiv.subgroupCongr (a2_foldFix_map h φ hφ))
  let ef : ↥(fixSubgroup φ) ≃* ↥(fixSub φ) := MulEquiv.subgroupCongr (by
    ext x
    rfl)
  let e : ↥(fixSubgroup φ) ≃* ↥(foldFix (a2Phi h φ)) := ef.trans e0.symm
  have hSne : S ≠ ⊥ := by
    haveI := hsimple
    exact (Subgroup.nontrivial_iff_ne_bot S).1 IsSimpleGroup.toNontrivial
  have hnab := exists_noncomm_of_perfect S hSne hperf
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := hFD.exists_rgd2
  have hcardU := a2_card_U_fix h φ hφ R'
  have hxS : q ^ 3 ∣ Nat.card ↥S := by
    have hle : ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ)).subgroupOf
        (foldFix (a2Phi h φ)) ≤ S := by
      intro g hg
      obtain ⟨hu, hgS⟩ := hUS g.1 hg
      exact hgS
    have hc : Nat.card ↥(((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
        foldFix (a2Phi h φ)).subgroupOf (foldFix (a2Phi h φ))) = q ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
          foldFix (a2Phi h φ) ≤ foldFix (a2Phi h φ))).toEquiv]
      exact hcardU
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  refine noL34Layer_of_equiv_normal_simple φ e S hsol hsimple hnab fun hT => ?_
  have h1 := card_eq_of_isLThreeFour hT
  rw [h1] at hxS
  exact not_cube_dvd_card_L34 hq5 hxS

end CFSG.HardMathSupport.Dickson.Sec6.OutTri
