module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplExt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplQuotB

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82S8Split_of : Asc82S8Split := by
  intro G _ _ V hV hC hwr
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b => hV.1.1.is_comm.comm a b
  obtain ⟨K', h1, h2⟩ := s8_split_ext hcomm (s8qι V) (s8qρ hV) (s8q_hι hV) (s8q_hker hV hC)
    (s8q_hequi hV) (by rw [s8q_range hV]; exact hwr)
  exact s8q_pull hV h1 h2

end CFSG.OddStandard.SmallF3.Omega
