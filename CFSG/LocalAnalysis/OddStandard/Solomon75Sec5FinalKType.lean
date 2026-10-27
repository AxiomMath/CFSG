module

public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

theorem isKComp_top_of_equiv [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) {t : X}
    (ht : orderOf t = 2)
    (h : Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly)) : IsKComp (⊤ : Subgroup X) := by
  obtain ⟨hXq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hbot2 : pPrimeCore 2 X = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 X).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
      rw [h1, Subgroup.card_top] at h2
      have h3 : 2 ∣ Nat.card X := ht ▸ orderOf_dvd_natCard t
      exact absurd (Nat.Coprime.eq_one_of_dvd h2 h3) (by norm_num)
  let e1 : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hbot2).trans QuotientGroup.quotientBot
  let e2 : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hXK : IsKType X :=
    ⟨hXq, Or.inr (h.imp (fun ⟨e⟩ => ⟨e2.trans e⟩) (fun ⟨e⟩ => ⟨e2.trans e⟩))⟩
  have hcomp : IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq,
      Subgroup.IsSubnormal.top⟩
  have hPC : IsPComponent 2 (⊤ : Subgroup X) :=
    LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp (fun hle => by
      rw [hbot2] at hle
      exact ht1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_top t))))
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X))
  exact ⟨hPC, IsKType.congr (e1.symm.trans f) hXK⟩

theorem SolCEx.false_of_equiv (hX : SolCEx X) {t : X} (ht : orderOf t = 2)
    (h : Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly)) : False := by
  have := hX.simple
  have hK := isKComp_top_of_equiv hX.nonabelian ht h
  obtain ⟨t', L, -, -, hnot⟩ := hX.witness
  exact hnot (le_top.trans (le_sSup hK))

end CFSG.OddStandard.Solomon75
