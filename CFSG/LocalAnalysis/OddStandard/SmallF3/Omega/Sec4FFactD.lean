module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDGlue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDStd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactD_holds : Asc82FactD := by
  intro G _ _ L hL s hs h6
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨y, hact, hy⟩ :=
    (sec4I_inducesTypeSome_iff e (by decide : 6 = 2 ∨ 6 = 4 ∨ 6 = 6)).mp h6
  obtain ⟨-, t, htt, ht6, hty⟩ := hy
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    simpa [pow_two] using h
  exact sec4FD_concl_of_model sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign ht6
    (sec4FDCover0_setting hL e hss hact htt hty)
    (fun v hvL hvv r α hr => sec4FDCover0_type_iff e hvL hvv hr)

end CFSG.OddStandard.SmallF3.Omega
