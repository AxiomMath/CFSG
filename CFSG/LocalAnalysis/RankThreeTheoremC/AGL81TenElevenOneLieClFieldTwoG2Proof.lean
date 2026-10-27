module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoG2Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoG2E9
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcG2Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


namespace LieClAut

theorem three_le_pRank_adjointG2 {X K : Type} [Group X] [Finite X] [Field K] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : X ≃* ↥(adjointGroup .G2 K))
    (hc : center X = ⊥) {H : Subgroup (MulAut X)}
    (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X} (hαH : α ∈ H)
    (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  haveI : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).2
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  set Ψ : MulAut X ≃* MulAut ↥(adjointGroup .G2 K) := MulAut.congr e with hΨ
  have hΨapp : ∀ (γ : MulAut X) (y : ↥(adjointGroup .G2 K)), Ψ γ y = e (γ (e.symm y)) :=
    fun γ y => rfl
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  refine three_le_pRank_of_fixesPair hc hinn (Θ.comp Ψ.toMonoidHom) (fun x => ?_)
    (fun δ hδ => ?_) (fun τ hτ3 _ => ?_) (fun γ hγ3 hγn => ?_)
    (fun E F hE hEc hF hFc => ?_) hαH hα hαn hEH hE hEc
  · change Θ (Ψ (MulAut.conj x)) = 1
    rw [hΨconj, ← MonoidHom.mem_ker, hker]
    exact ⟨e x, rfl⟩
  · have h : Ψ δ ∈ Θ.ker := hδ
    rw [hker] at h
    obtain ⟨p, hp⟩ := h
    refine ⟨e.symm p, ?_⟩
    rw [← hΨinv, hp, Ψ.symm_apply_apply]
  · refine ⟨Ψ.symm (entrywiseAdjointAut .G2 τ), ?_, ?_⟩
    · rw [← map_pow, ← entrywiseAdjointAut_pow, hτ3, entrywiseAdjointAut_one, map_one]
    · change Θ (Ψ (Ψ.symm _)) = τ
      rw [Ψ.apply_symm_apply]
      exact hΘ _ 1 τ fun h => by
        rw [coe_entrywiseAdjointAut]
        simp
  · have hout : Ψ γ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup .G2 K) := by
      rintro ⟨p, hp⟩
      apply hγn
      refine ⟨e.symm p, ?_⟩
      rw [← hΨinv, hp, Ψ.symm_apply_apply]
    obtain ⟨y₁, y₂, hc12, h1, h2, hind, hf1, hf2⟩ :=
      KFactProofs.Stroth.AlmostSimple.fixesPair_adjointG2_three hf K hK
        (by rw [← map_pow, hγ3, map_one]) hout
    have hfix : ∀ y, Ψ γ y = y → γ (e.symm y) = e.symm y := fun y hy => by
      rw [hΨapp] at hy
      have h := congrArg e.symm hy
      rwa [e.symm_apply_apply] at h
    refine ⟨e.symm y₁, e.symm y₂, ?_, by rw [← map_pow, h1, map_one],
      by rw [← map_pow, h2, map_one], fun i j hij => hind i j ?_, hfix _ hf1, hfix _ hf2⟩
    · change e.symm y₁ * e.symm y₂ = e.symm y₂ * e.symm y₁
      rw [← map_mul, ← map_mul, hc12.eq]
    · apply e.symm.injective
      rw [map_mul, map_zpow, map_zpow, hij, map_one]
  · have hEm : IsElemAbelian 3 (E.map e.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hE _
    have hFm : IsElemAbelian 3 (F.map e.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hF _
    obtain ⟨g, hg⟩ := exists_conj_e9_adjointG2 hEm
      (by rw [Subgroup.card_map_of_injective e.injective, hEc]) hFm
      (by rw [Subgroup.card_map_of_injective e.injective, hFc])
    refine ⟨e.symm g, fun x hx => ?_⟩
    obtain ⟨y, hy, hye⟩ := hg (e x) ⟨x, hx, rfl⟩
    have : e.symm g * x * (e.symm g)⁻¹ = y := e.injective (by simpa using hye.symm)
    rw [this]
    exact hy

end LieClAut

theorem kFactOuterThreeRankTwoG2_holds : KFactOuterThreeRankTwoG2 := by
  intro X _ _ q hv hp h3 he hc H hinn hα E hEH hE hEc
  obtain ⟨e⟩ := he
  obtain ⟨K, _, _, hK, -, ⟨e'⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hKn : Nat.card K = 2 ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def, hp]
  have hf : 2 ≤ q.exponent := by
    have := q.exponent_pos
    obtain ⟨m, hm⟩ := h3
    omega
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  exact LieClAut.three_le_pRank_adjointG2 hf hKn (e.trans e') hc hinn hαH hαk hαn hEH hE hEc

theorem kFactTenElevenOneLieAutFieldTwo_holds : KFactTenElevenOneLieAutFieldTwo :=
  kFactTenElevenOneLieAutFieldTwo_of_g2 kFactOuterThreeRankTwoG2_holds

end CFSG.LocalAnalysis.RankThreeTheoremC
