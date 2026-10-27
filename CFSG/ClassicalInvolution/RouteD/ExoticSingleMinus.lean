module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFixed
public import CFSG.ClassicalInvolution.RouteD.GapsToralB
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Same

variable {F : Type} [Field F] [Finite F]

theorem quadMinus_four_same_involution (hodd : Odd (Nat.card F)) {b c₀ : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) (h4 : 4 ≤ Nat.card F)
    {R₀ R₁ : Subgroup (_ ≃ₗ[F] _)} {i₀ i₁ : _ ≃ₗ[F] _}
    (h₀ : IsFundamental (quadMinus 4 F b c₀) R₀ i₀)
    (h₁ : IsFundamental (quadMinus 4 F b c₀) R₁ i₁) (hc : Commutes R₀ R₁) : i₁ = i₀ := by
  rcases orth_or_twin hodd h₀ h₁ hc with horth | heq
  swap
  · exact heq
  exfalso
  obtain ⟨F₀, rfl, rfl⟩ := h₀
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  exact false_of_orth_quadMinus_four (IsFundamental.two_ne_zero_of_odd hodd) hirr h4 F₀ F₁
    (span_le_perp_of_negSpace hodd horth)

theorem fundSet_hubUnique_of_same {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    (hodd : Odd (Nat.card F))
    (hsame : ∀ (R₀ R₁ : Subgroup (V ≃ₗ[F] V)) (i₀ i₁ : V ≃ₗ[F] V), IsFundamental Q R₀ i₀ →
      IsFundamental Q R₁ i₁ → Commutes R₀ R₁ → i₁ = i₀) : FundHubUnique (fundSet Q) := by
  intro R hR S₁ hS₁ S₂ hS₂ h₁ h₂
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j₁, hj₁⟩ := hS₁
  obtain ⟨j₂, hj₂⟩ := hS₂
  have hinv : ∀ (S : Subgroup (V ≃ₗ[F] V)) (j : V ≃ₗ[F] V), IsFundamental Q S j →
      IsHub (fundSet Q) R S → j = i := fun S j hj hh => hsame R S i j hi hj hh.2.1.symm
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd hi
  have e₁ : S₁ = L' := (huniq S₁ (hinv S₁ j₁ hj₁ h₁ ▸ hj₁)).resolve_left h₁.1
  have e₂ : S₂ = L' := (huniq S₂ (hinv S₂ j₂ hj₂ h₂ ▸ hj₂)).resolve_left h₂.1
  rw [e₁, e₂]

end Same

section Generation

variable {p f : ℕ} [Fact p.Prime]

theorem top_le_iSup_fund_minus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaMinus m p f)
    (hstd : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') :
    (⊤ : Subgroup (modelUniv .POmegaMinus m p f Fact.out).K) ≤
      ⨆ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D, R := by
  have hqs : CFSG.Open.IsQuasisimple (modelUniv .POmegaMinus m p f Fact.out).K :=
    (ModelFacts.modelClauseZero .POmegaMinus m p f Fact.out trivial hadm).1
  set S := ⨆ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D, R
    with hS
  have hnormal : S.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hmapS : S.map (MulAut.conj g).toMonoidHom ≤ S := by
      rw [hS, Subgroup.map_iSup]
      refine iSup_le fun R => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hR => ?_
      exact le_iSup₂_of_le (conjSub g R) (conjSub_mem_fundamentalSubgroups hR g) le_rfl
    exact hmapS ⟨x, hx, rfl⟩
  obtain ⟨R₀, hR₀⟩ := nonempty_fund_minus (p := p) (f := f) hm
  obtain ⟨R', hR', W, hW⟩ := hstd _ hR₀
  refine Gaps.top_le_of_normal_of_not_le_center hqs hnormal fun hle => ?_
  have hR₀S : R₀ ≤ Subgroup.center (modelUniv .POmegaMinus m p f Fact.out).K :=
    (le_iSup₂_of_le _ hR₀ le_rfl).trans hle
  refine not_commutes_of_linearBlockStandardPair hW fun a ha b _ => ?_
  exact (Subgroup.mem_center_iff.mp (hR₀S ha) b).symm

theorem range_le_iSup_fund_minus {m : ℕ} (hm : 4 ≤ m)
    (hadm : StatedLieAdmissible .POmegaMinus m p f)
    (hstd : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') {X : Type} [Group X]
    (ψ : (modelUniv .POmegaMinus m p f Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
      R.map ψ := by
  have h := Subgroup.map_mono (f := ψ) (top_le_iSup_fund_minus hm hadm hstd)
  rw [← MonoidHom.range_eq_map, Subgroup.map_iSup] at h
  refine h.trans (iSup_le fun R => ?_)
  rw [Subgroup.map_iSup]
  exact iSup_le fun hR => le_iSup₂_of_le R hR le_rfl

end Generation

section Minus

variable {p f : ℕ} [Fact p.Prime]

theorem minusTwinFixed_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p f) {X : Type} [Group X]
    (ψ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →* X)
    (hψker : ψ.ker ≤ Subgroup.center
      (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ x, σ (σ x) = x) (hσr : ∀ k, σ (ψ k) ∈ ψ.range)
    {R R' : Subgroup
      (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum 4 (minusCoeffs_irr p f)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum 4 (minusCoeffs_irr p f)))
    (htw : IsFundTwin
      (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum 4 (minusCoeffs_irr p f))) R R')
    (hfixR : ∀ r ∈ R, σ (ψ r) = ψ r) : ∀ r ∈ R', σ (ψ r) = ψ r := by
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ 4 := le_refl 4
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_card_galoisField hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hK]; omega
  have hirr := minusCoeffs_irr p f
  have hQuot := centralQuot_minus hp2 hq hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField p f) hirr
  obtain ⟨α, g, hαψ, hα⟩ :=
    ModelFacts.OrthAut.exists_isConj_lift_minus hp2 hn4 hf hK hirr ψ hψker σ hσ2 hσr
  have : Group.IsPerfect
      (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) :=
    isPerfect_spinGroup_quadMinus hn4 hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) →* _).comp
        (α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) →* _)) (MonoidHom.id _) (fun x => by
      apply hψker
      rw [MonoidHom.mem_ker]
      change ψ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαψ, hαψ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨i, fr, hRfr, -⟩ := hQuot.map_mem R hR
  have htwin := IsFundTwin.to_map _ hQuot.ker_le hQuot.perf hQuot.surj hR hR' htw
  rw [hRfr] at htwin
  have hsame : ∀ (R₀ R₁ : Subgroup (_ ≃ₗ[GaloisField p f] _)) (i₀ i₁ : _ ≃ₗ[GaloisField p f] _),
      IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) R₀ i₀ →
      IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) R₁ i₁ →
      Commutes R₀ R₁ → i₁ = i₀ :=
    fun R₀ R₁ i₀ i₁ h₀ h₁ hc => quadMinus_four_same_involution hodd hirr h4 h₀ h₁ hc
  have hR'fr : R'.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) = fr.swap.La.range :=
    eq_swap_of_isFundTwin hodd hsame fr (hQuot.map_mem R' hR') htwin
  have hfix : ∀ r ∈ R, α r = r := fixes_of_perfect_of_central (hQuot.perf R hR).ge α
    fun r hr => hψker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ, hfixR r hr, inv_mul_cancel])
  have hfixR' := fixes_twin_of_isConj hQ (by rw [hdim]; omega) hα hα2
    (ker_spinAction_le_center _) fr (hQuot.perf R' hR').ge hRfr hR'fr hfix
    (fun g' hg hskew ⟨c, hc, hsq⟩ =>
      false_of_skewRoot_quadMinus_four h2 hodd hirr h4 ⟨hg, hskew, hsq, hc⟩)
  intro r' hr'
  rw [← hαψ, hfixR' r' hr']

theorem minusTwinsExist_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p f) :
    FundTwinsExist (modelFund p f .POmegaMinus 4) := by
  have hQuot := centralQuot_minus hp2 hq hadm
  have key : FundTwinsExist (fundamentalSubgroups .POmegaMinus
      (Twisted.minusDatum 4 (minusCoeffs_irr p f))) :=
    FundTwinsExist.of_central _ hQuot.ker_le hQuot.perf hQuot.map_mem hQuot.surj
      fun _ hL => exists_isFundTwin_fundSet (odd_card_galoisField hp2 hq) hL
  exact key

theorem minusHubUnique_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p f) :
    FundHubUnique (modelFund p f .POmegaMinus 4) := by
  have hQuot := centralQuot_minus hp2 hq hadm
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hK]; omega
  have key : FundHubUnique (fundamentalSubgroups .POmegaMinus
      (Twisted.minusDatum 4 (minusCoeffs_irr p f))) :=
    FundHubUnique.of_central _ hQuot.ker_le hQuot.perf hQuot.map_mem hQuot.surj
      (fundSet_hubUnique_of_same (odd_card_galoisField hp2 hq) fun R₀ R₁ i₀ i₁ h₀ h₁ hc =>
        quadMinus_four_same_involution (odd_card_galoisField hp2 hq) (minusCoeffs_irr p f) h4
          h₀ h₁ hc)
  exact key

theorem rowSingleMinusSmall : RowPiece p f ShapeSingleMinusSmall := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl, rfl⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : 4 ≤ 4 := le_refl 4
  have hY := RouteD.yData_minus hn S.odd hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .POmegaMinus 4 (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := CFSG.ClassicalInvolution.RouteD.oddCoverSL3_of_five_le S.five, hY := hY }
  have hL : FundTwinFixed (modelFund p f .POmegaMinus 4) := by
    intro X _ ψ hψker σ hσ2 hσr R hR R' hR' htw hfixR
    exact minusTwinFixed_spin S.odd S.five hadm ψ hψker σ hσ2 hσr hR hR' htw hfixR
  exact false_of_twin_fixed c (single_class K) hshape (RouteD.nonempty_fund_minus hn)
    (range_le_iSup_fund_minus hn hadm hY.std c.d.ψ) (minusTwinsExist_four S.odd S.five hadm)
    (minusHubUnique_four S.odd S.five hadm) hL

end Minus

end CFSG.ClassicalInvolution.RouteD.Exotic
