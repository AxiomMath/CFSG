module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.D4Residual
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank

private theorem exists_statedClassicalModel_orth {S : Type} [Group S]
    (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t n (lieIndexChar idx.1) f := by
  obtain ⟨d, hv⟩ := idx
  rcases hor with ⟨r, q, hd, hq2, hr3⟩ | ⟨r, q, hd⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaOdd, r, q.exponent, Or.inl rfl,
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr3 e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaPlus, r, q.exponent, Or.inr (Or.inl rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaMinus, r, q.exponent, Or.inr (Or.inr rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e⟩

theorem lieCompCase_orthogonal (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hD4 : D4OuterExport) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1) :
    LieCompExport (lieIndexChar idx.1) β ∨ NoThreeComponents β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact Or.inl (lieCompExport_one hna idx he (isEmpty_mulEquiv_alternating_six hb _ he))
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, ht, hG⟩ := exists_statedClassicalModel_orth idx hor e
  by_cases hin : ∃ a : S, MulAut.conj a = β
  ·
    obtain ⟨a, rfl⟩ := hin
    have ha3 : a ^ 3 = 1 := by
      have hc : a ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj (a ^ 3) = 1 by rw [map_pow]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * a ^ 3 = a ^ 3 * g * (a ^ 3)⁻¹ * a ^ 3 := by rw [h1]
          _ = a ^ 3 * g := by group
      rw [b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    by_cases hℓ3 : lieIndexChar idx.1 = 3
    ·
      right
      have hS : IsChevOfChar 3 S :=
        ⟨idx, YS08.isChevIndexOfChar_of_lieIndexChar_eq hℓ3, ⟨e⟩⟩
      have ha1 : a ≠ 1 := by
        intro h1
        apply hβ1
        rw [h1, map_one]
      exact noThreeComponents_of_conj hQ hs hna hS ha1 ha3
    · left
      exact lieCompExport_conj_omega slFactorFacts_holds slAltSixFacts_holds suFactorFacts_holds
        suAltSixFacts_holds omegaFactorFacts_holds omegaAltSixFacts_holds ht hG hℓ3 a ha3
  ·
    have hout : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    by_cases hd4 : t = .POmegaPlus ∧ n = 4
    · obtain ⟨rfl, rfl⟩ := hd4
      exact hD4 S hG β hβ hout
    · left
      exact lieCompExport_omega_outer omegaFactorFacts_holds omegaAltSixFacts_holds ht hG hd4 β hβ
        hout

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
