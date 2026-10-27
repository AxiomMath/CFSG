module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_conj)
open scoped commutatorElement

theorem open_pRank_top_le_two_of_rankLE2 {S : Type} [Group S] [Finite S]
    (h : CFSG.LieType.SeitzGeneration.RankLE2 3 S) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 := by
  apply csSup_le'
  rintro k ⟨E, -, hE, hk⟩
  have h1 : 3 ^ k ≤ 3 ^ 2 := hk ▸ h E hE
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem commutator_le_inner_of_ker {Γ A : Type*} [Group Γ] [Group A] [IsCyclic A]
    (Θ : MulAut Γ →* A) (hΘ : Θ.ker = (MulAut.conj : Γ →* MulAut Γ).range) :
    commutator (MulAut Γ) ≤ inner Γ := by
  letI : CommGroup A := IsCyclic.commGroup
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have h : ⁅g₁, g₂⁆ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [hΘ] at h
  exact h

set_option linter.unusedSectionVars false


theorem false_of_i1433SCfg_trialityD4 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (r : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 r).Valid) (hr3 : r.p ≠ 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hv⟩).Group))
    {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ} (c : I1433SCfg Q x J q) :
    False := by
  haveI := hs
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨e0⟩ := he
  obtain ⟨K, _, _, σ, -, -, ⟨Θ, hΘ⟩, ⟨e1⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 r hv
  haveI := CFSG.RankThree.PartTwo.KFacts.isCyclic_ringEquiv_of_finite K
  have hin : ∀ α ∈ Q, ∃ g : S, α = MulAut.conj g := fun α hα =>
    exists_conj_of_mem_commutator_of_le (e0.trans e1) (commutator_le_inner_of_ker Θ hΘ)
      (c.derived hα)
  have h3 := c.three_le_pRank_of_inner hZ hin (IsSL3EpsOver.exists_noncentral_order_three c.sl3)
  have hR : CFSG.LieType.SeitzGeneration.RankLE2 3 S :=
    CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e0.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 r hv hr3)
  have h2 := open_pRank_top_le_two_of_rankLE2 hR
  omega

theorem false_of_i1433Cfg_trialityD4 {X : Type} [Group X] [Finite X] {K Q₁ Q J : Subgroup X}
    {t : X} {q : ℕ} (c : I1433Cfg K Q₁ Q J t q) (r : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 r).Valid) (hr3 : r.p ≠ 3)
    (he : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃*
      (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hv⟩).Group)) : False := by
  obtain ⟨x, Q', J', hcfg⟩ := c.exists_sCfg
  have hq := c.setup.quasisimple
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq
  exact false_of_i1433SCfg_trialityD4 hq.2.1 ⟨a, b, hab⟩ r hv hr3 he hcfg

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
