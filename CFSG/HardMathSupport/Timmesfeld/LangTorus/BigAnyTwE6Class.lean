module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwHex
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRhoHex

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false


section Class

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def LangSetup.IsTwE6SixClass (S : LangSetup TwistTag.E6.tag L p) : Prop :=
  ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr ∧
    S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord)

@[expose] def TwE6HexGamma : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup TwistTag.E6.tag L p),
    S.IsTwE6SixClass → 7 ≤ p → S.IsAlgebraic → S.HexGroupInGamma

theorem twE6SixMat_rel :
    toMat TwistTag.E6.tag.rank twE6SixMat * toMat TwistTag.E6.tag.rank twE6SixMat =
      toMat TwistTag.E6.tag.rank twE6SixMat - 1 := by
  decide +kernel

theorem LangSetup.hexStep_of_twE6SixClass (S : LangSetup TwistTag.E6.tag L p)
    (h : S.IsTwE6SixClass) : S.HexStep := by
  obtain ⟨Fr, hFr, hΦ, hn⟩ := h
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
      toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  exact hexStep_of_twist S hFr hΦ hn hv
    (fun x => CFSG.RankThree.E6.permLattice_e6Rho_e6Rho x) twE6SixMat_rel

theorem LangSetup.bigAnyPBig_of_twE6SixClass (S : LangSetup TwistTag.E6.tag L p)
    (h : S.IsTwE6SixClass) (hp7 : 7 ≤ p) (hΓ : S.HexGroupInGamma) : BigAnyPBig S :=
  bigAnyPBig_of_hexStep S (S.hexStep_of_twE6SixClass h) (Or.inr (Or.inl rfl)) hp7 hΓ

end Class

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_twistedE6_of_pbig (hAK : AnyKindCommute)
    (hAF : AnyKindNoFrobenius) {K : Type} [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup TwistTag.E6.tag L p) (_hp7 : 7 ≤ p)
    (hq4 : 4 ≤ S.D.q)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hAlg : S.IsAlgebraic) (hPS : BigAnyPBig S) : SetupRigid S :=
  setupRigid_twistedE6 S hΦ hAlg
    (fun D₁ hD₁ hc => hAF _ L p S (by decide) (Or.inr (Or.inr (Or.inl rfl))) D₁ hD₁
      (hasBigAnyComponent_of_pbig S hq4 hPS hD₁ hc))
    (fun D₁ hD₁ hc => centralizerTrivial_of_bigAnyGenerate hAK S (by decide) (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc))
    (fun D₁ hD₁ hc => cosetCentralizerEmpty_of_bigAnyGenerate (K := K) hAK S (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc))

end Rigid

section Classes


theorem innerPlaneBalanceAt_twistedE6_six_of_class (hcp : LangComponentPieces)
    (hHex : TwE6HexGamma) (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hsmall : InnerPlaneBalanceSmall .twistedE6 6) : InnerPlaneBalanceAt .twistedE6 6 := by
  intro q hv p hp hp7 _ hpq he
  by_cases h4 : 4 ≤ q.card
  · obtain ⟨K, _, σ, hK, hσ, ⟨eq⟩⟩ := exists_catEquiv_twistedE6 q hv
    have hpK : ¬ p ∣ q.p ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def]
      exact not_dvd_card_of_ne hp hpq
    have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 6 := by
      rw [← TauCeti.PrimePower.card_def]
      exact he
    obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
      springer_exists_langSetup_twistedE6_six frobeniusOnRoots_proved q.prime_p q.exponent_pos K
        hK σ hσ hp hp7 hpK he'
    have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
    have hK0 : Nat.card K ≠ 0 := by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
    have : Finite K := Nat.finite_of_card_ne_zero hK0
    have hq : S.D.q = q.p ^ q.exponent := by rw [hSD]; rfl
    have hq4 : 4 ≤ S.D.q := by rw [hq, ← TauCeti.PrimePower.card_def]; exact h4
    have hΦ : ∃ Fr' : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr' c = c ^ S.D.q) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr' :=
      ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; rfl⟩
    have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq])
    have hcl : S.IsTwE6SixClass := ⟨Fr, fun c => by rw [hq]; exact hFr c, by rw [hSD]; rfl,
      by rw [hSD]; rfl⟩
    have hPS : BigAnyPBig S :=
      S.bigAnyPBig_of_twE6SixClass hcl hp7 (hHex _ p S hcl hp7 hAlg)
    have hrig := setupRigid_twistedE6_of_pbig hAK hAF (K := K) S hp7 hq4 hΦ hAlg hPS
    have hC : Function.Injective
        (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
      CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
        (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
    have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv ε hC
    exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
      (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)
  · exact hsmall q hv p hp hp7 hpq he (by omega)

end Classes

end CFSG.HardMathSupport.Timmesfeld.LangTorus
