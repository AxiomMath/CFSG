module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinusPolar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolar

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

theorem un_polarity_core_card {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
    (h : A2Std σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    ∃ m : ℕ, m ∣ (p ^ f) ^ 2 - 1 ∧
      Nat.card ↥(foldFix (unTauX h φ ε hcomm)) = ((p ^ f) ^ 3 * m) * (1 + (p ^ f) ^ 3) := by
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
  refine un_final_card hp2 (by omega) (unD h φ hφ) (unTauX h φ ε hcomm)
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

end CFSG.GH74.GLS.Stage2.Bender.Thm1
