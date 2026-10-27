module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33R

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerSmallDegreeInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X) (n : ℕ), Sol78.IsSolomonPair t J n → (n = 9 ∨ n = 11) →
    ∀ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X), E ≤ J →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
    ∀ D : Finset (Fin n), D.card = 4 → (∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) →
      (∀ y : X, orderOf y = 2 → y ∈ centralizer (E : Set X) →
        y ∈ UnbalancedLayer.coreActionKernel J → y ∉ J →
        ∀ a ∈ E ⊔ zpowers y, a ≠ 1 → ∀ b ∈ E ⊔ zpowers y, b ≠ 1 →
          SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤
            SolAltLit.thetaFunctor E b) ∧
      ∀ F : Subgroup X, F ≤ J →
        Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
        E ≤ centralizer (F : Set X) → ∀ DF : Finset (Fin n), DF.card = 4 → Disjoint D DF →
        (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
          ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
            ω) →
        ∀ f ∈ F, f ≠ 1 → ∀ b ∈ E, b ≠ 1 →
          SolAltLit.thetaFunctor F f ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b

variable {X : Type} [Group X]

theorem eq_nine_or_eleven {n : ℕ} (hodd : Odd n) (h9 : 9 ≤ n) (hn : ¬ 13 ≤ n) :
    n = 9 ∨ n = 11 := by
  obtain ⟨k, hk⟩ := hodd
  omega

theorem ne_bot_of_klein {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) : E ≠ ⊥ := by
  intro h
  have h4 := (card_sq_of_klein hE).1
  rw [h, Subgroup.card_bot] at h4
  omega

theorem balanceLemmaInput_of_smallDegree (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) :
    Sol78.BalanceLemmaInput := by
  intro X _ _ _ hnab hKP hunb hnU t J n hpair θ E hEJ hE hD y hy hyE hyK hyJ a ha ha1 b hb hb1
  obtain ⟨D, hD4, hsupp⟩ := hD
  by_cases hn : 13 ≤ n
  · exact balanceLemma_of_large hbal hPump hN1 hnab hKP hunb hnU hpair hn θ hEJ hE hD4
      hsupp hy hyE hyK hyJ ha ha1 hb hb1
  · exact (hsmall X hnab hKP hunb hnU t J n hpair
      (eq_nine_or_eleven hpair.2.1 hpair.2.2.1 hn) θ E hEJ hE D hD4 hsupp).1 y hy hyE hyK hyJ
      a ha ha1 b hb hb1

theorem completion_le_of_smallDegree (hbal : Sol78.BalanceTwoComponentInput)
    (hsmall : SignalizerSmallDegreeInput) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hpair : Sol78.IsSolomonPair t J n) (h911 : n = 9 ∨ n = 11)
    (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E F : Subgroup X} (hEJ : E ≤ J)
    (hFJ : F ≤ J) (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEF : E ≤ centralizer (F : Set X)) {DE DF : Finset (Fin n)} (hDE : DE.card = 4)
    (hDF : DF.card = 4) (hdisj : Disjoint DE DF)
    (hsE : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ DE,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    (hsF : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    Sol78.signalizerCompletion F F ≤ Sol78.signalizerCompletion E E := by
  have h := (hsmall X hnab hKP hunb hnU t J n hpair h911 θ E hEJ hE DE hDE hsE).2 F hFJ hF hEF
    DF hDF hdisj hsF
  refine completion_le_of_balance hbal hE hF hEF fun e he he1 f hf hf1 => ?_
  have h1 := h f hf hf1 e he he1
  rwa [thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hF) (ne_bot_of_klein hF) hf
    hf1, thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hE) (ne_bot_of_klein hE)
    he he1] at h1

theorem signalizerLemma35_of_smallDegree (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) : SignalizerLemma35 := by
  intro X _ _ _ hnab hKP hunb hnU t J n hpair θ E F hEJ hFJ hE hF hEF DE DF hDE hDF hdisj hsE hsF
  by_cases hn : 13 ≤ n
  · exact signalizerLemma35_of_large hbal hPump hN1 hnab hKP hunb hnU hpair.1 hn hpair.2.1 θ hEJ
      hFJ hE hF hEF hDE hDF hdisj hsE hsF
  · have h911 := eq_nine_or_eleven hpair.2.1 hpair.2.2.1 hn
    have hFE : F ≤ centralizer (E : Set X) := le_centralizer_iff.mp hEF
    exact le_antisymm
      (completion_le_of_smallDegree hbal hsmall hnab hKP hunb hnU hpair h911 θ hFJ hEJ hF hE hFE
        hDF hDE hdisj.symm hsF hsE)
      (completion_le_of_smallDegree hbal hsmall hnab hKP hunb hnU hpair h911 θ hEJ hFJ hE hF hEF
        hDE hDF hdisj hsE hsF)

end CFSG.ComponentClassification.SolMax
