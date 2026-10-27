module

public import CFSG.ClassicalInvolution.Asc77.AscT8RepEng
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem Thompson.Ctx.toRepHooks (c : CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx Ω W) :
    CFSG.ClassicalInvolution.Asc77.T8V.RepHooks Ω W :=
  ⟨c.comm_W,
    fun hR => fun hr hr' hrW hr'W =>
      CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.D_inv_mul_mem c.hΩ c.hW hR hr hr' hrW hr'W,
    fun hK hR hRK => fun hz =>
      CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW hK hR hRK hz,
    fun ρ => fun hu => c.conj_inv ρ hu,
    fun ρ σ hne hnot => fun hz hj => c.conj_involution ρ σ hne hnot hz hj,
    fun ρ σ h => fun hv => c.centralizes ρ σ h hv⟩

end CFSG.ClassicalInvolution.Q3.Q3CL
