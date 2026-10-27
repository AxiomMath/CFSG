module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18Ae5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2W

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

section WOut

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem wOutcome_normalizes (F : TwinDisc.ExitO2.Q8Fam Y Δ) {W : Subgroup Y} (hW1 : WSet Δ = {W})
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {t : Y} (ht : IsUniqueInvolution J t) :
    conjSub t K = K := by
  by_cases hKJ : K = J
  · subst hKJ
    exact conjSub_eq_self_of_mem ht.mem
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ :=
    TwinDisc.ExitO2.fam_mem_omegaStarNbr_of_wSet F hW1 K hK J hJ hKJ
  obtain ⟨j, hjU, hj2⟩ := exists_sq_ne_one_of_mem_USet F hU
  have hjJ : j ∈ J := hUJ hjU
  have h4 : (j * j) * (j * j) = 1 := by
    have := F.pow_four J hJ j hjJ
    calc (j * j) * (j * j) = j ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := this
  have hjt : j * j = t := (ht.unique _ (J.mul_mem hjJ hjJ) h4).resolve_left hj2
  have hjN : j ∈ Subgroup.normalizer (K : Set Y) := hUN hjU
  rw [← hjt]
  exact conjSub_eq_of_mem_normalizer ((Subgroup.normalizer (K : Set Y)).mul_mem hjN hjN)

end WOut

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
