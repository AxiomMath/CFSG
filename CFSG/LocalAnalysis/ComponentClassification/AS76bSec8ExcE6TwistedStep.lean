module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedAutFix
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.ComponentClassification.RankTwoExceptional.Exc CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

variable {K : Type} [Field K]

theorem twReps_mem_subsystemGroup
    [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) :
    ∀ x ∈ twReps σ hσσ, (x : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨eT, eU, eV⟩ := twFrameProd_eq_realize (K := K) h2
  intro x hx
  simp only [twReps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · change twFrameProd (K := K) frT ∈ _
    rw [eT]
    exact E6EvenInvolution.realize_mem h2 _
  · change twFrameProd (K := K) frU ∈ _
    rw [eU]
    exact E6EvenInvolution.realize_mem h2 _
  · change twFrameProd (K := K) frV ∈ _
    rw [eV]
    exact E6EvenInvolution.realize_mem h2 _

theorem step814_twistedE6
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) : Step814 .twistedE6 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | twistedE6 m hm K₀ hK₀ σ₀ hσ₀ e₀ =>
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have hmodel : ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 m :=
      ⟨⟨Nat.prime_two, hm, rfl⟩, K₀, inferInstance, inferInstance, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_twistedE6 hmodel)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hmodel
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hm hK
    have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have hσ2 := CFSG.SeitzReduction.twistedE6_sigma_pow_order hK hσ
    have hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
      have h := congrArg (fun g : K ≃+* K => g c) hσ2
      simpa [TwistTag.order, pow_two] using h
    have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ m := hσ
    have hZC : center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
      exceptional_fixed_center_trivial TwistTag.E6 K σ
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    refine exists_config814_of_torus h32 h33 h4 h34 (ExcModel.twistedE6 m hm K₀ hK₀ σ₀ hσ₀ e₀) hA
      hZA hZC e hOut (2 ^ m) rfl hq2 (reps := twReps σ.toRingHom hσσ)
      (classesCover_twReps hm hK hσ hσσ) (residualMem_twReps hm hK hσ hσσ)
      (charTwo_twReps hK hσ hσσ) (fun hq x hx => ?_) (fun hq x hx => ?_)
      (fun _ => EvenOddRadical.centralizerOTwoFree_graphFixedRootGroupE6 σ hσ2)
      (fun h => by simp [ExcModel.IsTrialityFour] at h)
    ·
      have hm1 : m = 1 := by
        by_contra h
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hm1
      exact Or.inl (card_zx_twReps_two (by rw [hK]; norm_num) (fun c => by rw [hσ]; norm_num) hσσ
        x hx)
    ·
      have hm2 : 2 ≤ m := by
        by_contra h
        have hm1 : m = 1 := by omega
        rw [hm1] at hq
        norm_num at hq
      set k := GaloisField 2 m
      have hk : Nat.card k = 2 ^ m := GaloisField.card 2 m (by omega)
      obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hm hk hK
      let _ : Algebra k K := ι.toAlgebra
      exact ⟨_, _, _, _,
        { levi := leviData_twisted (k := k) hm2 hk hK hσ' (twReps_mem_subsystemGroup _ hσσ x hx)
          autFix := autFix_twisted (k := k) hm2 hk hK hσ
          type := fun L₀ ⟨f⟩ => Or.inl (statedClassicalModel_of_mulEquiv_twisted (k := k) hm hk hK
            hσ' f)
          diag := fun h => by simp [ExcModel.IsTrialityFour] at h }⟩
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
