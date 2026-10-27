module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.CartanConj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace F4FourSL2Aux

theorem transport {G S F : Type} [Group G] [Group S] [Field F] (e : G ≃* S)
    (ι : Fin 4 → (SL(2, F) →* G)) (hinj : ∀ i, Function.Injective (ι i))
    (hc : ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A) :
    ∃ ψ : Fin 4 → SL(2, F) →* S, (∀ i, Function.Injective (ψ i)) ∧
      ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) :=
  ⟨fun i => e.toMonoidHom.comp (ι i), fun i => e.injective.comp (hinj i),
    fun i j hij A B => by
      show e (ι i A) * e (ι j B) = e (ι j B) * e (ι i A)
      rw [← map_mul, ← map_mul, hc i j hij A B]⟩

end F4FourSL2Aux

section Main


theorem f4FourSL2_holds : F4FourSL2 := by
  intro S _ _ d q hd hq hiso
  obtain ⟨eL⟩ := hiso
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = TauCeti.LieTypeIndex.F4 q := hd
  subst hd'
  obtain ⟨hq1, hq2⟩ := hq
  have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq1 (GaloisField 2 2) hK4
  let eZ : AdjointQuotient Tag.F4 (GaloisField 2 2) ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 2)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := Tag.F4) (K := GaloisField 2 2))).trans
      QuotientGroup.quotientBot
  let eS : ↥(adjointGroup Tag.F4 (GaloisField 2 2)) ≃* S := eZ.symm.trans (eB.trans eL.symm)
  obtain ⟨ι, hinj, hc⟩ :=
    CFSG.RankThree.Chevalley.even_higher_ordinary_exceptional_four_commuting_faithful_SL2
      (GaloisField 2 2) Tag.F4 (Or.inl rfl)
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
  · rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  · exact F4FourSL2Aux.transport eS ι hinj hc

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
