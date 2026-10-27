module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.NoUp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.TwoSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

structure Fi3Inputs : Type 1 where
  pinned : FiPinned
  section_ : Link5bSection
  lemma33 : ∀ (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H], Lemma33Two IsK IsL H
  hypOne22 : ∀ (Y : Type) [Group Y], IsSporadic Y .Fi22 → HypothesisOne Y
  tmem22 : TMemOfNotMax [.Fi22] (fun _ => fiLoc 18393661440)
  row22 : Stage3Row [.Fi22] (fun _ => fiLoc 18393661440)
  row23 : Stage3Row [.Fi23] (fun _ => fiLoc (2 * 64561751654400))
  row24 : Stage3Row [.Fi24Prime] (fun _ => fiLoc (2 * 64561751654400))
  hyp31_22 : FiHyp31 row22.IsK [.Fi22] fiTypes [.Fi23, .Fi24Prime]
  hyp31_23 : FiHyp31 row23.IsK [.Fi23] fiTypes [.Fi24Prime]
  hyp31_24 : FiHyp31 row24.IsK [.Fi24Prime] fiTypes [.Fi23]
  variantThree : FiVariantThree
  coexist : FiCoexist

theorem fiStage3Main_of_inputs (I : Fi3Inputs) : FiStage3Main := by
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 L hL hLc
  obtain ⟨s, hs, hcov⟩ := hLc
  obtain ⟨s₀, L₀, hs₀, hL₀, hcov₀, hnb, -⟩ := exists_noBiggerFi hs hL hcov
  have hs₀' : s₀ = .Fi22 ∨ s₀ = .Fi23 ∨ s₀ = .Fi24Prime := by simpa [fiTypes] using hs₀
  rcases hs₀' with rfl | rfl | rfl
  · obtain ⟨L', hc, hout⟩ := fi_caseA I.row22 I.hyp31_22
      (twoSylowStd_fi22 lit.lemma25 (fun X _ hX => (I.row22.hyp31Row.quasi_L X hX).2.2) I.hypOne22)
      I.tmem22 (I.lemma33 _ _ H) lit ih hN hidx hkp hN22 hN23 hN24 hnb
      (fiNoUpA I.section_ I.pinned lit H ih N hN hidx hkp hnb) hL₀ hcov₀
    exact ⟨.Fi22, L', by simp [fiTypes], hc, hout⟩
  · obtain ⟨L', hc, hout⟩ := fi_caseB I.row23 I.hyp31_23 (I.lemma33 _ _ H) lit ih hN hidx hkp hN22
      hN23 hN24 hnb (fiNoUpB I.section_ I.pinned lit H ih N hN hidx hkp hnb) hL₀ hcov₀
    exact ⟨.Fi23, L', by simp [fiTypes], hc, hout⟩
  · by_cases hF : ∃ P : Subgroup H, InL P ∧ IsSporadic (↥P ⧸ center ↥P) .Fi23
    · by_cases hstd : ∃ L₁ : Subgroup H, SolStd L₁ ∧ OddCover .Fi23 L₁
      · exact I.coexist lit H ih N hN hidx hkp hN22 hN23 hN24
          (noBiggerFi_fi24Prime_of_orders I.pinned.orders H) ⟨L₀, hL₀, hcov₀⟩ hstd
      · exact I.variantThree lit H ih N hN hidx hkp hN22 hN23 hN24
          (noBiggerFi_fi24Prime_of_orders I.pinned.orders H) ⟨L₀, hL₀, hcov₀⟩ hF hstd
    · have hup : FiNoUp [.Fi23] H := by
        intro Q hQ s'' hs'' h
        obtain rfl := List.mem_singleton.1 hs''
        exact hF ⟨Q, hQ, h⟩
      obtain ⟨L', hc, hout⟩ := fi_caseC1 I.pinned.orders I.row24 I.hyp31_24 (I.lemma33 _ _ H) lit
        ih hN hidx hkp hN22 hN23 hN24 hup hL₀ hcov₀
      exact ⟨.Fi24Prime, L', by simp [fiTypes], hc, hout⟩

end CFSG.EvenSporadicStandard.Induction.Fi
