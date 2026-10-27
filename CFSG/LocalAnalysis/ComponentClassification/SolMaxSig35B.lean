module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem support_coreImage_subset {J E : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {D : Finset (Fin n)}
    (hsupp : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    {e : X} (he : e ∈ J) (heE : e ∈ E) : (coreImage θ he).support ⊆ D := by
  intro ω hω
  by_contra hωD
  exact (Perm.mem_support.mp hω) (hsupp ⟨e, he⟩ heE ω hωD)

theorem completion_le_of_large (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n) (hn : 13 ≤ n) (hnodd : Odd n)
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
  have hE2 := (card_sq_of_klein hE).2
  have hF2 := (card_sq_of_klein hF).2
  refine completion_le_of_balance hbal hE hF hEF fun e he he1 f hf hf1 => ?_
  have heJ := hEJ he
  have hfJ := hFJ hf
  have hef : e * f = f * e := mem_centralizer_iff.mp (hEF he) f hf |>.symm
  have hse := support_coreImage_subset θ hsE heJ he
  have hsf := support_coreImage_subset θ hsF hfJ hf
  exact core_inf_centralizer_le_of_large hbal hPump hN1 hnab hKP hunb hnU hJ θ hn hnodd heJ hfJ
    (by rw [← sq]; exact hE2 e he) (by rw [← sq]; exact hF2 f hf) he1 hf1 hef
    ((Finset.card_le_card hse).trans hDE.le) ((Finset.card_le_card hsf).trans hDF.le)
    (Finset.disjoint_of_subset_left hse (Finset.disjoint_of_subset_right hsf hdisj))

theorem signalizerLemma35_of_large (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n) (hn : 13 ≤ n) (hnodd : Odd n)
    (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E F : Subgroup X} (hEJ : E ≤ J)
    (hFJ : F ≤ J) (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEF : E ≤ centralizer (F : Set X)) {DE DF : Finset (Fin n)} (hDE : DE.card = 4)
    (hDF : DF.card = 4) (hdisj : Disjoint DE DF)
    (hsE : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ DE,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    (hsF : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    Sol78.signalizerCompletion E E = Sol78.signalizerCompletion F F := by
  have hFE : F ≤ centralizer (E : Set X) := le_centralizer_iff.mp hEF
  exact le_antisymm
    (completion_le_of_large hbal hPump hN1 hnab hKP hunb hnU hJ hn hnodd θ hFJ hEJ hF hE hFE hDF
      hDE hdisj.symm hsF hsE)
    (completion_le_of_large hbal hPump hN1 hnab hKP hunb hnU hJ hn hnodd θ hEJ hFJ hE hF hEF hDE
      hDF hdisj hsE hsF)

end CFSG.ComponentClassification.SolMax
