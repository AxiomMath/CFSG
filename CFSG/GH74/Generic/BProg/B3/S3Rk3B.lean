module

public import CFSG.GH74.Generic.BProg.B3.S3Rk3Glue

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk3B

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G}

theorem x_mem_CxK (hc : Cfg x y K T) : x ∈ CxK x K := by
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxK : x ∈ normalizer (K : Set G) := S3Rk3Glue.mem_normalizer_K hc hxC
  refine Subgroup.mem_inf.2 ⟨hxC, hxK, S3Rk3Glue.mem_normalizer_pPrimeCoreOf hxK, fun k hk => ?_⟩
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 (hc.hK.1 hk)
  rw [commutatorElement_eq_one_iff_mul_comm.2 hkx]
  exact Subgroup.one_mem _

end S3Rk3B

end CFSG.GH74.Generic.BProg.B3
