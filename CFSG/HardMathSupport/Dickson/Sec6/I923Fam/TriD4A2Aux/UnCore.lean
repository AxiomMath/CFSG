module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnResidual
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddOne

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair


section CoreR

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

include hφ in
theorem A2Core.un_polarity_core_R {p f : ℕ} [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (hf : 1 ≤ f) (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2.SimpleCore ↥(foldFix (unTauX h φ ε hcomm)) ((p ^ f) ^ 3) ((p ^ f) ^ 5) := by
  have hσ' : ∀ c, σ c = c ^ ((p ^ f) ^ 4) := fun c => by rw [h.frob c, hq]
  have hK : Nat.card K = ((p ^ f) ^ 4) ^ 3 := by rw [h.card, hq]
  have hεσ : ∀ c, ε (σ c) = σ (ε c) := un_eps_sigma hσ' hε
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := un_eps_four hK hε
  have : CharP (UnK σ) p := un_charP_unK σ
  have hk : Nat.card (UnK σ) = (p ^ f) ^ 4 := un_card_unK hf hK hσ'
  have hεk : ∀ a : UnK σ, unEps ε hεσ a = a ^ (p ^ f) := un_eps_frob hσ' hε hεσ
  have hεε : ∀ c, (ε * ε) (σ c) = σ ((ε * ε) c) := fun c => by
    show ε (ε (σ c)) = σ (ε (ε c))
    rw [hεσ, hεσ]
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁', -⟩ := (unD_spec h φ hφ).lifts
  have hn₁X : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W :=
    Subtype.ext (hn₁'.trans (unSlFix_w h φ hφ).symm)
  obtain ⟨κ, hκ⟩ := unRho_tau h φ hφ hn₂ ε hεσ hcomm
  have hτ := un_isOpposition h φ hφ ε hεσ hcomm
  have hτe := un_tauX_tauX h φ ε hcomm hcommε
  have hBsolv : Group.IsSolvable ↥(unD h φ hφ).B := by
    haveI := (d4RGD2 σ.toRingHom h.cube_apply).isSolvable_B
    let f₀ : ↥(unD h φ hφ).B →*
        ↥((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) :=
      ((foldFix (a2Phi h φ)).subtype.comp (unD h φ hφ).B.subtype).codRestrict _
        (fun x => ((unD_spec h φ hφ).B x.1).1 x.2)
    exact solvable_of_solvable_injective (f := f₀) fun a b hab => by
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
  refine CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2.un_residual hp5 (by omega) (unD h φ hφ) hBsolv (unTauX h φ ε hcomm)
    (unFieldX h φ (ε * ε) hcommε) hτ hτe
    (fun b hb => by rw [← hτe b]; exact hτ.tau_sq_mem_B hb)
    (un_tauX_four h φ ε hε4 hcomm) hk (unEps ε hεσ) hεk (unRho h φ hφ n₂)
    (unRho_injective h φ hφ n₂) κ (fun a => (hκ a).1) (fun a => (hκ a).2)
    (unRho_upper_mem h φ hφ hn₂) (fun y hy => unRho_upper_surj h φ hφ hn₂ hy)
    (unRho_lower_mem h φ hφ hn₂) (unRho_N h φ hφ hn₂ hn₁ hn₁X) (unRho_H h φ hφ hn₂)
    (unX1 h φ hφ) (unX1_injective h φ hφ) (unX1_mem h φ hφ) (fun y hy => unX1_surj h φ hφ hy)
    (unX1_torus h φ hφ) ?_ (un_hab h φ hφ (Or.inl rfl)) (un_hab h φ hφ (Or.inr rfl))
    (un_hTor h φ hφ) (un_chat_X h φ hφ ε hεσ hcomm)
  intro a
  rw [unX1_field h φ hφ (ε * ε) hεε hcommε a, unEps_mul ε ε hεσ hεσ hεε a]

end CoreR

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual




section PolarityR

theorem un_polarity_R {p f : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2)
    {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ p] (hK₄ : Nat.card K₄ = ((p ^ f) ^ 4) ^ 3)
    (σ₄ ε : K₄ ≃+* K₄) (hσ₄ : ∀ c, σ₄ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (b : K₄ˣ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    SimpleCore ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ((p ^ f) ^ 3) ((p ^ f) ^ 5) := by
  have hp2 : p ≠ 2 := by omega
  have hA : A2Std σ₄ b ((p ^ f) ^ 4) := un_a2Std hp2 hf hq hK₄ hσ₄ hb3 hb1
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  have hNo := A2Core.un_polarity_core_R hA.toCore _ hφ₄ hp5 hf rfl ε hε hcomm hcommε
  obtain ⟨e', -⟩ := un_fixfix_equiv hA _ ε hcomm
  exact SimpleCore.of_equiv e' hNo

end PolarityR

section Toral

theorem noL2Layer_a2_minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : D4MinusToral p f hp K σ s) :
    NoL2Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  have : Fact p.Prime := ⟨hp⟩
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  have hp3 : p % 3 = 2 := un_mod3_of_pow hf hq
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  have hSC := un_polarity_R hp5 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have ef : ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) ≃*
      ↥(fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)).symm
  have hq5 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hxpp : (p ^ f) ^ 3 = 1 ∨ IsPrimePow ((p ^ f) ^ 3) := by
    rw [← pow_mul]
    exact isPrimePow_or_one hp
  have hkey := key_of_le_pow_five (q := p ^ f) (C := (p ^ f) ^ 5) (by omega) le_rfl
  exact noL2Layer_of_simpleCore _ (ef.trans e) hSC hxpp hkey

end Toral

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
