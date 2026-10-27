module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamLie
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem not_isChevSimple_of_card_eq_orderON (hb : LieOrderBridge) {q : ℕ} {Q : Type} [Group Q]
    [Finite Q] (hQ : Nat.card Q = orderON) :
    ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q Q := by
  have hLie : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group) →
      False := by
    intro d hf
    have h := hb d Q hf
    rw [hQ] at h
    exact GFR2Lie.lieOrderFormula_ne_onOrd d.2 (by rw [← h]; unfold GFR2Lie.onOrd orderON; norm_num)
  rintro (⟨i, hi, hf⟩ | ⟨i, hi, hf⟩)
  · cases i with
    | lie d => exact hLie d hf
    | _ => exact False.elim hi
  · cases i with
    | lie d => exact hLie d hf
    | alternating n hn =>
      obtain ⟨f⟩ := hf
      have hc : Nat.card Q = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr f.toEquiv
      rw [hQ] at hc
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
        unfold orderON at hc
        norm_num [Nat.factorial] at hc
    | _ => exact False.elim hi

theorem center_eq_bot_or_three_dvd {Y : Type} [Group Y] [Finite Y]
    (hcore : GLAPPrimeCore 3 Y = ⊥) :
    Subgroup.center Y = ⊥ ∨ 3 ∣ Nat.card (Subgroup.center Y) := by
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center Y)
  · exact Or.inr h3
  · left
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center Y)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have hle : Subgroup.center Y ≤ GLAPPrimeCore 3 Y :=
      le_sSup (show Subgroup.center Y ∈
          {M : Subgroup Y | M.Normal ∧ Nat.Coprime 3 (Nat.card M)} from ⟨inferInstance, hcop⟩)
    rw [hcore] at hle
    exact le_bot_iff.1 hle

theorem lieNoHatSix_of_lieComp (h : LieComp) : LieNoHatSix := by
  intro Y _ _ hq _ hcore ⟨idx, ⟨e⟩⟩ x hxo J₁ hJ₁ hSix
  have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
  obtain ⟨hperf, hZ3, ⟨a6⟩⟩ := hSix
  have hna := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  rcases center_eq_bot_or_three_dvd hcore with hZ | hZ
  · let eY : Y ≃* Y ⧸ Subgroup.center Y :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
    have hs : IsSimpleGroup Y := (MulEquiv.isSimpleGroup_congr eY).2 inferInstance
    have hna' : ∃ a b : Y, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hna
      refine ⟨eY.symm a, eY.symm b, fun hh => hab ?_⟩
      have := congrArg eY hh
      simpa using this
    obtain ⟨hD, -⟩ := h Y hs hna' idx ⟨eY.trans e⟩ x hx3 J₁ hJ₁
    exact hD.centre ⟨a6⟩ (by rw [hZ3])
  · obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := YS08.component_to_simple hx3 hJ₁
    obtain ⟨-, hM⟩ := h (Y ⧸ Subgroup.center Y) hq.2 hna idx ⟨e⟩ β hβ J' hJ'
    obtain ⟨f⟩ := nonempty_centralQuotient_mulEquiv hperf ψ hψ hψk
    exact hM ⟨f.symm.trans a6⟩ Y hq ⟨MulEquiv.refl _⟩ hZ

theorem lieDownChev_of_lieComp (h : LieComp) (hb : LieOrderBridge)
    (hOG : UniquenessMaximal.InputONGroup) : LieDownChev := by
  intro Y _ _ hq hK hcore idx he x hxo J₁ hJ₁ hty
  exfalso
  rcases hty with hON | hSix
  · have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
    obtain ⟨hperf, -, ⟨g⟩⟩ := hON
    obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := YS08.component_to_simple hx3 hJ₁
    obtain ⟨hD, -⟩ := h (Y ⧸ Subgroup.center Y) hq.2
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq) idx he β hβ
      J' hJ'
    obtain ⟨f⟩ := nonempty_centralQuotient_mulEquiv hperf ψ hψ hψk
    refine not_isChevSimple_of_card_eq_orderON hb ?_ hD.chev
    rw [← Nat.card_congr f.toEquiv, Nat.card_congr g.toEquiv]
    exact hOG.2
  · exact lieNoHatSix_of_lieComp h Y hq hK hcore ⟨idx, he⟩ x hxo J₁ hJ₁ hSix

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
