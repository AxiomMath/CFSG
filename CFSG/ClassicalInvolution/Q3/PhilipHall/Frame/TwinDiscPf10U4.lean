module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section Main

variable {n : ℕ}

theorem disc14N_of_zt (I : TwinDiscBase n) (hT4 : Thm4RTwinBelow 3 n) (hZT : DiscZT n) :
    Disc14N n := by
  intro Y _ _ R S t₀ K K' z u J t W s
  by_cases hc : SecConnU (CoreAssembly.conjClass (tightCore R)) u
  · exact disc14N_of_conn I s hc
  · have hf := s.data.frame
    have hs := alphaStepsBase I s
    have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
      CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
    have hY : coreLayer (CoreAssembly.conjClass (tightCore R)) u ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
      rcases hZT Y R S t₀ K K' z u J t W s hc with h | h
      · exact coreLayer_le_normalizer_alpha_of_trivial hs hf hc2 (Or.inl rfl) h
      · exact coreLayer_le_normalizer_alpha_of_trivial hs hf hc2 (Or.inr rfl) h
    exact centralizer_u_le_of_disc hT4 s hc hY fun J₀ hJ₀ =>
      normalizer_le_normalizer_alpha_of_mem_dComp hs hf hJ₀

end Main

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
