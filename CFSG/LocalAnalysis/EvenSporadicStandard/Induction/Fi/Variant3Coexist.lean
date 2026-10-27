module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Main

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def FiHyp31Max (IsK : GroupClass) : Prop :=
  Sol78Lit → Hyp31Row IsK (IsLS [.Fi23, .Fi24Prime]) → ∀ (H : Type) [Group H] [Finite H],
    BelowSec (Sol78PredS fiTypes) H → ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime →
          (∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P) →
            ∀ L : Subgroup H, SolStd L →
              (∃ s ∈ [TauCeti.SporadicName.Fi23, .Fi24Prime], OddCover s L) →
                Hyp31Glob H N IsK (IsLS [.Fi23, .Fi24Prime]) ∧ Hyp31FourA H N IsK

@[expose] def Fi23CloseCoexistAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N →
    N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
        (∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P) →
          OddCover .Fi23 L → SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u →
            Sol78Concl N L

theorem fiCoexistMax_of_inputs (ho : FiOrders)
    (row : Stage3Row [.Fi23, .Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)))
    (h31 : FiHyp31Max row.IsK) (hclose : ∀ (H : Type) [Group H] [Finite H], Balance.UHered H →
        Fi23CloseCoexistAt H) : FiCoexistMax := by
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 hnb ⟨L₀, hL₀, hcov₀⟩ hL₁ hmax
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hloc, -⟩ :=
    stage3Pair row lit ih.uHered
      (fun N' hN' hidx' hkp' L'' hL'' hc'' => by
        have hNN : N' = N := hN'.generalizedFitting_eq.symm.trans hN.generalizedFitting_eq
        subst hNN
        exact h31 lit row.hyp31Row H ih N' hN' hidx' hkp' hN22 hN23 hN24 hmax L'' hL'' hc'')
      (lemma33_two row.IsK (IsLS [.Fi23, .Fi24Prime]) H) N hN hidx hkp L₀ hL₀
      ⟨.Fi24Prime, by simp, hcov₀⟩
  rcases List.mem_cons.1 hs' with rfl | hs''
  · exfalso
    exact hN24 (hclose H ih.uHered N L' K t u hN hidx hkp ⟨L₀, hL₀, hcov₀⟩ hmax hcov' hglob
      hloc).2
  · obtain rfl := List.mem_singleton.1 hs''
    exact ⟨.Fi24Prime, L', by simp [fiTypes], hcov', Or.inl ⟨K, t, u, hglob,
      Or.inl (fiInBase_iff.2 ⟨hloc, noBiggerFi_fi24Prime_of_orders ho H⟩)⟩⟩

end CFSG.EvenSporadicStandard.Induction.Fi.V3
