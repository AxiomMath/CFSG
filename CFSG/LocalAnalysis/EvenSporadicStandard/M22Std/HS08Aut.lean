module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Pinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Glue

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.M22Std.E32Check
  CFSG.Monster.B.TwoA.Fischer

theorem autHyp_pinned :
    AutHyp (Carrier .M22) s0 jSub where
  data := { card_inner := HS08H.card_jSub_inner,
            card_normalizer := HS08H.card_normalizer_jSub,
            centralizer_le := HS08H.centralizer_jSub_le,
            trans_inner := HS08H.trans_inner_jSub,
            outer_orbits := HS08H.outer_orbits_jSub,
            outer_involution := HS08H.outer_involution_jSub,
            gen_involutions := HS08H.gen_involutions_s0 }
  card_S := card_s0
  J_le := jSub_le
  J_comm := jSub_comm
  J_sq := jSub_sq
  card_J := card_jSub
  J_unique := fun E hE hc hsq h32 => jSub_unique E hE hc hsq h32
  center_S := by
    obtain ⟨t₀, F1, -, -, W⟩ := sylowWitness_m22_s0
    refine ⟨MulAut.conj t₀, W.mem, ?_, ?_, ⟨t₀, Subgroup.mem_top _, rfl⟩, W.center⟩
    · intro h1
      have : t₀ = 1 := hs08_conj_injective (by rw [h1, map_one])
      exact W.ne this
    · rw [← map_mul, W.sq, map_one]
  card_A := catalog_M22_full_automorphism_order.1
  not_inner := fun h => betaAut_not_inner (h betaAut_mem_s0)

end CFSG.EvenSporadicStandard.M22Std
