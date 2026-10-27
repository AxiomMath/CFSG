module

public import CFSG.LargeExtraspecial.S63BD4
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.LargeExtraspecial.S63CD4A
public import CFSG.LargeExtraspecial.S63CD4B

public section

namespace CFSG.LargeExtraspecial.S63

theorem d42CentInput : D42CentInput := by
  intro Y _ hY s hs
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 Y hY
  refine D42At.of_mulEquiv e ?_
  have hes : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hes
  · rw [hc]
    exact d42At_d4z.conj c
  · rw [hc]
    exact d42At_d4t.conj c

end CFSG.LargeExtraspecial.S63
