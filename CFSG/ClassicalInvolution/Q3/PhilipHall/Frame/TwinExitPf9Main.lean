module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

section Leaf

variable {G : Type} [Group G] [Finite G]

@[expose] def TwinFrameULiftPairSec (Ω : Set (Subgroup G)) : Prop :=
  ∀ (K K' J : Subgroup G) (z u t : G), TwinFrameData Ω K K' z u J t →
    ∀ J' ∈ twinSet Ω J, J' ≠ J →
    ∀ c : G, (c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) →
      ∀ htC : t ∈ Subgroup.centralizer ({c} : Set G), ¬ Quiet c t htC →
      LiftedAtSec J c t htC → LiftedAtSec J' c t htC →
      ∀ x y : G, x ∈ K → y ∈ K' → x * x = z → y * y = z → x * y = u → x * t = t * x →
        ∀ hxc : x ∈ Subgroup.centralizer ({c} : Set G),
          ∃ M M' : Subgroup G,
            Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M t ∧
            Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' t ∧
            modOdd c M ≠ modOdd c M' ∧
            (∀ a ∈ modOdd c M, ∀ b ∈ modOdd c M', a * b = b * a) ∧
            (∀ a ∈ modOdd c M, oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
            (∀ a ∈ modOdd c M', oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩)

end Leaf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
