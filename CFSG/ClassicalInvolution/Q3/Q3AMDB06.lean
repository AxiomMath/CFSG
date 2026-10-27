module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB04
public import CFSG.ClassicalInvolution.Q3.Q3AMDB05
public import CFSG.ClassicalInvolution.Q3.Q3CHS2Gold
public import CFSG.ClassicalInvolution.Q3.Q3AMDB03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Final


theorem c28_DoubleB_of_noA2 (hres : PspNoA2Residual) : C28_DoubleB := by
  intro G _ _ _ Ω K J S R T W z t K' hset hD
  have hnoA2 : PspNoA2At Ω K z := hres G Ω K J S R T W z t K' hset hD
  obtain ⟨P, hPsyl, hPz, hEP⟩ := hset.exists_isSylow2In_centralizer
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylow2In_top hPsyl
  have hbad := hset.bad
  have hstd := hbad.std
  have hzt := hset.mul_comm_zt
  have hzE : z ∈ Subgroup.closure ({z, t} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert z _)
  have htE : t ∈ Subgroup.closure ({z, t} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  have hcl := hset.stronglyClosed_of_le_sylow hD hnoA2 T'.isPGroup' hPz (hEP htE)
    (hEP (Subgroup.mul_mem _ hzE htE))
  obtain ⟨t₁, t₂, t₃, R₁, R₂, R₃, hax⟩ := hbad.exists_axis_of_triangle hset.intrinsic
    hstd.stand.mem hstd.hJ hset.nbrK hset.nbrJ hstd.hz hstd.ht hset.uniq_mul rfl
  obtain ⟨a, b, ha, hb, ha2, hb2, hab⟩ := hset.exists_noncomm_involutions hax
  obtain ⟨hnab, hz2, hR2, hR8, hRu, h3⟩ := hset.goldschmidt_inputs hax
  have hbot := Q3CH.eq_bot_of_stronglyClosed_of_abelian3 hnab hz2 ha hb ha2 hb2 hab hR2 hR8 hRu h3
    T' hEP (isMulCommutative_closure_pair hzt) hcl
  rw [hbot] at hzE
  exact hstd.hz.ne_one (Subgroup.mem_bot.mp hzE)

end Final

end CFSG.ClassicalInvolution.Q3.Q3AM
