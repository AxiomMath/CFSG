module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutRigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutTri
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound
open Subgroup

section Final


theorem g24_card_normalizer :
    Nat.card ↥(normalizer (twoBD : Set PP)) = 503193600 := by
  classical
  obtain ⟨σ, -, hσN, hσD, hC, -⟩ := g24_outer_basic
  have hσ : σ ∈ normalizer (twoBD : Set PP) :=
    mem_normalizer_of_gens (hσN _ xBar_mem) (hσN _ yBar_mem)
  have hle : (twoBD : Subgroup PP) ≤ normalizer (twoBD : Set PP) := Subgroup.le_normalizer
  have hlow : 2 * Nat.card twoBD ≤ Nat.card ↥(normalizer (twoBD : Set PP)) := by
    set N := normalizer (twoBD : Set PP) with hN
    let D' : Subgroup ↥N := twoBD.subgroupOf N
    have hD'card : Nat.card D' = Nat.card twoBD :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hne : D' ≠ ⊤ := fun h => hσD (by
      have : (⟨σ, hσ⟩ : ↥N) ∈ D' := by rw [h]; exact Subgroup.mem_top _
      exact this)
    have hidx : D'.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have hidx0 : D'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Subgroup.card_mul_index D'
    rw [hD'card] at this
    rw [← this]
    have h2 : 2 ≤ D'.index := by omega
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h2
  have hup : Nat.card ↥(normalizer (twoBD : Set PP)) ≤ Nat.card (MulAut ↥twoBD) := by
    have : Finite (MulAut ↥twoBD) :=
      Finite.of_injective (fun α : MulAut ↥twoBD => α.toEquiv) fun α β h => MulEquiv.ext fun x =>
        congrFun (congrArg DFunLike.coe h) x
    exact Nat.card_le_card_of_injective _ (normalizerMonoidHom_injective twoBD hC)
  have h1 := g24_aut_card_le
  rw [card_twoBD] at hlow h1
  omega

theorem g24_fixed_nonsolvable
    (β : MulAut ↥twoBD)
    (h1 : β ≠ 1) (h2 : β * β = 1) (F : Subgroup ↥twoBD) (hF : ∀ x, x ∈ F ↔ β x = x) :
    ¬ Group.IsSolvable ↥F := by
  obtain ⟨tA, htA, -⟩ := g24_classes
  obtain ⟨-, -, -, -, hC, o, ho, -⟩ := g24_outer_basic
  have hN := g24_card_normalizer
  have hfus := g24_outer_fusion htA ho hN
  obtain ⟨ht1, ht2, ht3⟩ := g24_tri htA ho
  have hcard : Nat.card (MulAut ↥twoBD) ≤ Nat.card ↥(normalizer (twoBD : Set PP)) := by
    have := g24_aut_card_le
    rw [card_twoBD] at this
    omega
  refine not_isSolvable_fixed_of_classes twoBD hC hcard {tA, xBar, o} ?_ ?_ β h1 h2 F hF
  · rintro s (rfl | rfl | rfl)
    · exact ht1
    · exact ht2
    · exact ht3
  · intro s hs hs2 hs1
    rcases hfus s hs hs2 hs1 with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
    · exact ⟨tA, Or.inl rfl, n, hn, e⟩
    · exact ⟨xBar, Or.inr (Or.inl rfl), n, hn, e⟩
    · exact ⟨o, Or.inr (Or.inr rfl), n, hn, e⟩

end Final

end CFSG.EvenSporadicStandard.G24Aut
