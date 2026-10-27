module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711E4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

namespace Twin1711

variable {G : Type} [Group G] [Finite G]

theorem piGen_perfect_of_members_le {π : Set (Subgroup G)}
    (h : ∀ J ∈ π, J ≤ ⁅piGen π, piGen π⁆) : ⁅piGen π, piGen π⁆ = piGen π := by
  refine le_antisymm ?_ (piGen_le h)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact (piGen π).mul_mem ((piGen π).mul_mem ((piGen π).mul_mem hx hy) ((piGen π).inv_mem hx))
    ((piGen π).inv_mem hy)

end Twin1711


@[expose] def TwinE4Untwisted (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ π : Set (Subgroup Y),
        π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
        NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
          ∀ hKX : tightCore R ≤ conjSub g (piGen π), ∀ z : Y, ∀ hz : IsUniqueInvolution (tightCore R) z,
            ¬ TightInO2 (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩) →
            TwinE4 (SecQuot (conjSub g (piGen π))) →
              ∀ J ∈ conjSub g '' π, J ≤ ⁅conjSub g (piGen π), conjSub g (piGen π)⁆

theorem twinE4Perfect_of_untwisted {n : ℕ} (h : TwinE4Untwisted n) : TwinE4Perfect n := by
  intro Y _ _ R S t hcore hconn π hπ hH1 g hg hKX z hz hnot hE4
  have hm := h Y R S t hcore hconn π hπ hH1 g hg hKX z hz hnot hE4
  have := Twin1711.piGen_perfect_of_members_le (π := conjSub g '' π) (by
    rw [piGen_conj]; exact hm)
  rwa [piGen_conj] at this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
