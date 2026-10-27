module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx63
public import CFSG.GH74.GLS.Bg.Local.Lemma1621
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem54

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Fused8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem hyp_of (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {U : Subgroup G} {u : G}
    (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) (hUn : NormedBy U S) (hzU : z ∈ U) (huU : u ∈ U)
    (hu : u ∉ zpowers z) : Bg.L1621.Hyp S U z u where
  UP := hUS
  Unorm := fun g hg v hv => hUn g hg v hv
  Ucard := hU4.2
  Uexp := fun a ha => by
    have := hU4.1
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
    simpa [pow_two] using h1
  zP := hf.z_mem_S hII
  zsq := hf.z_sq
  zne := hf.z_ne
  zcent := fun g hg => hf.z_comm hII hg
  cinv := fun v hv hvc hv2 hv1 => eq_z_of_central hII hf.std hv hvc hv2 hv1
  zU := hzU
  uU := huU
  une1 := fun h => hu (h ▸ one_mem _)
  unez := fun h => hu (h ▸ mem_zpowers z)

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
