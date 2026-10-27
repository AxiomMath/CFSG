module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeParab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {e : ℕ}

local notation "𝐂" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "𝐏(" J ")" =>
  Subgroup.subgroupOf (graphFixedParabolic TwistTag.D4 K σ.toRingHom J) 𝐂

theorem two_part_centralizer_le_cube (h : Std e K σ) (hQ : 2 ^ e % 3 = 1) (z : ↥𝐂)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    2 ^ (Nat.card (Subgroup.centralizer ({z} : Set ↥𝐂))).factorization 2 ≤ (2 ^ e) ^ 3 := by
  classical
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥𝐂 := inferInstance
  haveI := h.charP_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  refine two_part_centralizer_le ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf 𝐂)
    ((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf 𝐂)
    {P | ∃ J : Set (Fin TwistTag.D4.foldedTag.rank), J ≠ Set.univ ∧ P = 𝐏(J)} ((2 ^ e) ^ 3)
    (Nat.one_le_pow _ _ (by positivity))
    (by
      obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
      exact ⟨PU, hPU⟩)
    ?_ ?_ ?_ z hz3 hz1
  · rintro P ⟨J, hJ, rfl⟩
    obtain ⟨hU, hH, hidx⟩ := torus_parabolic_conditions σ h hQ hJ
    refine ⟨Subgroup.comap_mono hU, Subgroup.comap_mono hH, ?_⟩
    rw [Subgroup.relIndex_subgroupOf (graphFixedParabolic_le _ _ _ _)]
    exact hidx
  · intro T hT hT2
    obtain ⟨g, J, hJ, R, hR⟩ := borelTits_normalized σ h T hT hT2
    exact ⟨g, 𝐏(J), ⟨J, hJ, rfl⟩, R, hR⟩
  · intro x hx hx3 hx1
    have hxH : (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom := Subgroup.mem_subgroupOf.1 hx
    have hx3' : (x : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
      have := congrArg (fun y : ↥𝐂 => (y : ModGL TwistTag.D4.tag K)) hx3
      simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using this
    have hx1' : (x : ModGL TwistTag.D4.tag K) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
    refine le_trans ?_ (card_posUnipotent_inf_centralizer_le h hQ hxH hx3' hx1')
    refine Nat.card_le_card_of_injective (fun u => ⟨(u.1 : ModGL TwistTag.D4.tag K), ?_⟩) ?_
    · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 u.2
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hu1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hu2 ⊢
      exact congrArg (fun y : ↥𝐂 => (y : ModGL TwistTag.D4.tag K)) hu2
    · intro u v huv
      have h1 := Subtype.ext_iff.1 huv
      exact Subtype.ext (Subtype.ext h1)

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
