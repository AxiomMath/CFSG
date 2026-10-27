module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

namespace ExitU

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinE4_of_exitSec (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) {K : Subgroup X} (hK : K ∈ Φ)
    {z : X} (hz : IsUniqueInvolution K z)
    (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥)
    {W : Subgroup X} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hex : Thm4Twin.F2.ExitSec W K hKW z hz) : TwinE4 X := by
  have hmem := members hS htrans hK hz hodd
  have h2 : ∀ J ∈ Φ, IsPGroup 2 J := fun J hJ => (hmem J hJ).1
  have hWtop : W = ⊤ := ExitE4.eq_top_of_subnormal hS.gen htrans hK hWs rfl hKW
  have hΦ : Φ = CoreAssembly.conjClass K := by
    ext J
    constructor
    · intro hJ
      exact htrans K hK J hJ
    · rintro ⟨g, rfl⟩
      exact hS.hyp.conjInvariant g K hK
  have key : TwinE4 ↥(⊤ : Subgroup X) → TwinE4 X := fun h => ExitE4.twinE4_of_top h
  rcases hex with hE | ⟨S, hnoW, hex⟩
  · exact key (hWtop ▸ hE)
  · have hedge' : ¬ TightEdgeless (K.subgroupOf W) := by
      subst hWtop
      obtain ⟨K₀, hK₀, J, hJ⟩ := hedge
      have h2R : IsPGroup 2 ↥(K.subgroupOf (⊤ : Subgroup X)) := (h2 K hK).comap_subtype
      unfold TightEdgeless
      rw [tightCore_eq_self_of_isPGroup h2R]
      exact ExitE4.not_dEdgeless_top (h2 K hK) hΦ hK₀ hJ
    rcases hex with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hnoW
    · exact absurd h hedge'
    · exact absurd h hedge'
    · exact key (hWtop ▸ TightE4.twinE4 h)

theorem noExit_or_o2_or_e4 (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M)
    (hodd : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥) :
    NoExit X Φ ∨ (∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z) ∨ TwinE4 X := by
  by_cases hO2 : ∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z
  · exact Or.inr (Or.inl hO2)
  · by_cases hE : TwinE4 X
    · exact Or.inr (Or.inr hE)
    · left
      push Not at hO2
      intro K hK z hz
      refine ⟨hodd K hK z hz, hO2 K hK z hz, ?_⟩
      intro W hKW hWs _ hex
      exact hE (twinE4_of_exitSec hS htrans hedge hK hz (hodd K hK z hz) hKW hWs hex)

end ExitU

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
