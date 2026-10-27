module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Frame
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGClaim
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGThompson

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

theorem false_of_wreathCase {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z : G}
    {h : Setting G L 10} {d : Cyc L Q z} {ι : Perm (Fin 10) →* G} (F : SwapFrame h d ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hzx : z ∈ centralizer ({z * ι τ₀} : Set G))
    {Sg V K : Subgroup (TwoSec (z * ι τ₀))}
    (H : WreathCase (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec (z * ι τ₀)) Sg V K) : False := by
  have hC : CentData z ι := F.cent
  haveI : IsSimpleGroup G := h.std.simple
  have hO : CFSG.pPrimeCore 2 (TwoSec (z * ι τ₀)) = ⊥ := by
    rw [← CFSG.ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]
    exact oddCore_twoSec_eq_bot h (orderOf_x₂ hC)
  let q : ↥(centralizer ({z * ι τ₀} : Set G)) →* TwoSec (z * ι τ₀) := QuotientGroup.mk' _
  let Nhat : Subgroup G := ((normalizer (K : Set (TwoSec (z * ι τ₀)))).comap q).map
    (centralizer ({z * ι τ₀} : Set G)).subtype
  have hNidx : Nhat.relIndex (centralizer ({z * ι τ₀} : Set G)) = 2 := by
    have h1 : Nhat.subgroupOf (centralizer ({z * ι τ₀} : Set G)) =
        (normalizer (K : Set (TwoSec (z * ι τ₀)))).comap q :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [Subgroup.relIndex, h1,
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact H.normalizer_index_eq_two
  refine false_of_outer_conjugates h.std.nonab hC F.conj hP2
    (fun c hc hcx => (claimA hC hP2 hO H hc hcx).1) Nhat hNidx ?_
  intro c hc hcx hcN
  obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hcN
  have hy' : y = ⟨c, hcx⟩ := Subtype.ext hyc
  rw [hy'] at hy
  exact (claimA hC hP2 hO H hc hcx).2 hy

end CFSG.OddStandard.AltStdSec.SwapPartner
