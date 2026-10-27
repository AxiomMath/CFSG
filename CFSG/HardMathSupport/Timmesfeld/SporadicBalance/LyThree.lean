module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreThreeBFinal

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Sporadic.Recognition.LyonsSims CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem gLAPPrimeCoreOf_centralizer_eq_bot_of_forall {S : Type*} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) {g : S}
    (h : ∀ W : Subgroup S, W ≤ Subgroup.centralizer ({g} : Set S) →
      (∀ c : S, c * g = g * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W) → Nat.Coprime (Nat.card W) p →
        W = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({g} : Set S)) = ⊥ :=
  h _ (GLAPPrimeCoreOf_le _)
    (fun c hc w hw => GLAPPrimeCoreOf_conj_mem c (Subgroup.mem_centralizer_singleton_iff.2 hc) w hw)
    (coprime_card_GLAPPrimeCoreOf hp _).symm

theorem oPrimeCoreTrivialAt_Ly_three
    (S : Type) [Group S] [Finite S] (hS : Nonempty (S ≃* NativeSporadic.Carrier .Ly)) :
    OPrimeCoreTrivialAt 3 S := by
  obtain ⟨eT⟩ := hS
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have h3B := LyCore.lyThreeBCore_of_order LyCore.lyThreeBOrder_thm
  intro g hg
  refine gLAPPrimeCoreOf_centralizer_eq_bot_of_forall Nat.prime_three fun W hWC hWn hcop => ?_
  rcases (lemma45_classes_of_certificate D St).1 g hg with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact LyCore.eq_bot_of_conj_core hc (LyCore.three_a_core D St) hWC hWn hcop
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact LyCore.eq_bot_of_conj_core hc (h3B S ⟨eT⟩ t ρ D x₁ x₂ x₃ St) hWC hWn hcop

theorem sporadicOPrimeHolds_Ly_three :
    SporadicOPrimeHolds .Ly 3 :=
  fun S _ _ _ hS => oPrimeCoreTrivialAt_Ly_three S hS

theorem sporadicOnePairHolds_Ly_three :
    SporadicOnePairHolds .Ly 3 :=
  ⟨sporadicOPrimeHolds_Ly_three, sporadicOuterHolds_Ly 3⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
