module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem sec6_lambda2 {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E)
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b)) :
    Odd (Nat.card ↥(⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a))) ∧
    (∀ a ∈ E, a ≠ 1 → (⨆ (c : X) (_ : c ∈ E) (_ : c ≠ 1), oddCoreOf (cen c)) ⊓ cen a =
      oddCoreOf (cen a)) ∧
    ∀ B : Subgroup X, B ≤ E → Nat.card B = 4 →
      (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) =
        ⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a) := by
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hEcen : ∀ a ∈ E, E ≤ cen a := fun a ha y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hEcomm y hy a ha)
  obtain ⟨hWodd, hWE, hWcen, -, -⟩ :=
    CFSG.SignalizerFunctorTheorem.two_signalizer_completion E hE hE8 (fun a => oddCoreOf (cen a))
      (fun a _ _ => oddCoreOf_le _)
      (fun a _ _ => odd_card_oddCoreOf _)
      (fun a ha _ => (hEcen a ha).trans (le_normalizer_oddCoreOf _))
      hbal
  set W : Subgroup X := ⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a) with hW
  refine ⟨hWodd, hWcen, fun B hBE hB4 => le_antisymm ?_ ?_⟩
  · exact iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 =>
      le_iSup₂_of_le (f := fun a (_ : a ∈ E) => ⨆ (_ : a ≠ 1), oddCoreOf (cen a)) b (hBE hb)
        (le_iSup_of_le hb1 le_rfl)
  · have hB : CFSG.Open.IsElemAbelian 2 B :=
      ⟨⟨⟨fun x y => Subtype.ext (hEcomm x (hBE x.2) y (hBE y.2))⟩⟩, fun x hx => hE.2 x (hBE hx)⟩
    have hcop : Nat.Coprime 2 (Nat.card W) := Nat.coprime_two_left.2 hWodd
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
      Nat.prime_two hB (by rw [hB4]; norm_num) (hBE.trans hWE) hcop
    rw [← hgen]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [hWcen b (hBE hb) hb1]
    exact le_iSup₂_of_le (f := fun c (_ : c ∈ B) => ⨆ (_ : c ≠ 1), oddCoreOf (cen c)) b hb
      (le_iSup_of_le hb1 le_rfl)

end CFSG.OddStandard.Solomon75
