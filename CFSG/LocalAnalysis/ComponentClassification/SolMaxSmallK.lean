module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallJ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33S

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerSmallDegreeAt (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X), Sol78.IsSolomonPair t J n →
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

@[expose] def SignalizerSmallDegreeNineInput : Prop := SignalizerSmallDegreeAt 9

@[expose] def SignalizerSmallDegreeElevenInput : Prop := SignalizerSmallDegreeAt 11

theorem signalizerSmallDegreeInput_of_degrees (h9 : SignalizerSmallDegreeNineInput)
    (h11 : SignalizerSmallDegreeElevenInput) : SignalizerSmallDegreeInput := by
  intro X _ _ _ hnab hKP hunb hnU t J n hpair hn e E hEJ hE D hD hsupp
  rcases hn with rfl | rfl
  · exact h9 X hnab hKP hunb hnU t J hpair e E hEJ hE D hD hsupp
  · exact h11 X hnab hKP hunb hnU t J hpair e E hEJ hE D hD hsupp

variable {X : Type} [Group X]

theorem signalizerLemma35Eleven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 11) (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11))
    {E F : Subgroup X} (hEJ : E ≤ J) (hFJ : F ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEF : E ≤ centralizer (F : Set X)) {D DF : Finset (Fin 11)} (hD : D.card = 4)
    (hDF : DF.card = 4) (hdisj : Disjoint D DF)
    (hsE : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) ω = ω)
    (hsF : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) ω = ω)
    {f : X} (hf : f ∈ F) (hf1 : f ≠ 1) {b : X} (hb : b ∈ E) (hb1 : b ≠ 1) :
    SolAltLit.thetaFunctor F f ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  rw [thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hF) (ne_bot_of_klein hF) hf
    hf1, thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hE) (ne_bot_of_klein hE)
    hb hb1]
  have hb2 : b * b = 1 := by rw [← sq]; exact (card_sq_of_klein hE).2 b hb
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hF).2 f hf
  have hbf : b * f = f * b := (mem_centralizer_iff.mp (hEF hb) f hf).symm
  have hsb := support_coreImage_subset θ hsE (hEJ hb) hb
  have hsf := support_coreImage_subset θ hsF (hFJ hf) hf
  exact core_inf_centralizer_le_of_eleven hbal hPump hN1 hnab hKP hunb hnU hpair.1 θ (hEJ hb)
    (hFJ hf) hb2 hf2 hb1 hf1 hbf ((Finset.card_le_card hsb).trans hD.le)
    ((Finset.card_le_card hsf).trans hDF.le)
    (Finset.disjoint_of_subset_left hsb (Finset.disjoint_of_subset_right hsf hdisj))

end CFSG.ComponentClassification.SolMax
