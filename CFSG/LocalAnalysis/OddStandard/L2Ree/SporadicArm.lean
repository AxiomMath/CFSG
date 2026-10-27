module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.Common
public import CFSG.LocalAnalysis.OddStandard.L2Ree.SporadicJ3
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyDefs
public import CFSG.LocalAnalysis.OddStandard.ResidualOddLie

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.HarrisLit.T1.SporRow


theorem sporadic_arm_outcome {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : LieModel (L ⧸ center L) .PSL 2 p f)
    (h5 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))) (hs : SporadicRep G)
    (hAny : ∀ s : TauCeti.SporadicName,
      (s ≠ .M11 ∧ s ≠ .M12 ∧ s ≠ .J1 ∧ s ≠ .J2 ∧ s ≠ .J3 ∧ s ≠ .HS) → SporOddCompsAny s) :
    IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS := by
  have hsimple := hS.simple
  obtain ⟨s, ⟨e⟩⟩ := hs
  obtain ⟨hLt, hcomp⟩ := isComponent_of_standard hS.standard ht ht2
  obtain ⟨eB⟩ := nonempty_quotient_center_subgroupOf hLt
  have hmB : LieModel (↥(L.subgroupOf (centralizer ({t} : Set G))) ⧸
      center ↥(L.subgroupOf (centralizer ({t} : Set G)))) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv eB.symm hm
  have hoddB := oddLieOrder_of_lieModel hp hp2 hmB
  cases s with
  | M11 =>
    exfalso
    exact false_of_isSporadic_M11_of_le_centralizer ⟨e⟩ ht2 hLt
      (Residual.sixty_le_card_of_standard hS.standard)
  | J3 =>
    exfalso
    obtain ⟨e5⟩ := nonempty_mulEquiv_alternatingGroup_five_of_J3 e ht2 hp hp2 hmB
    exact h5 ⟨eB.symm.trans e5⟩
  | M12 => exact Or.inl ⟨e⟩
  | J1 => exact Or.inr (Or.inl ⟨e⟩)
  | J2 => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | HS => exact Or.inr (Or.inr (Or.inr ⟨e⟩))
  | _ =>
    exfalso
    exact hAny _ (by decide) G hS.nonab e t ht2 _ hcomp hoddB

end CFSG.OddStandard.L2Ree
