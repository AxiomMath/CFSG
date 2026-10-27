module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7h
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7i
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7j

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_X7_le_K (c : Ctx7 G L) (hb : B5Std c) : X7 c.s ≤ y7bK c.s := by
  obtain ⟨ρ, hker, hsurj⟩ := y7b_exists_rhoV c hb
  haveI : ((X7 c.s).subgroupOf (y7bX c.s)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (y7b_X7_le_X c)]
    intro h k hh hk
    exact y7b_X7_normal c hb k hk h hh
  have hY : ∀ y ∈ (X7 c.s).subgroupOf (y7bX c.s), ρ y ^ 2 = 1 := by
    intro y hy
    change (y : G) ∈ X7 c.s at hy
    have hsqK : ((y : G) ^ 2) ∈ y7bK c.s :=
      y7b_X0_le_K c hb (y7b_X7_sq_mem_X0 c hb (y : G) hy)
    have h1 : ρ (y ^ 2) = 1 := (hker (y ^ 2)).mpr (by simpa only [Subgroup.coe_pow] using hsqK)
    simpa only [map_pow] using h1
  have htriv := y7b_perm3_normal_triv ρ hsurj ((X7 c.s).subgroupOf (y7bX c.s)) hY
  intro x hx
  have hxX : x ∈ y7bX c.s := y7b_X7_le_X c hx
  have hmemY : (⟨x, hxX⟩ : ↥(y7bX c.s)) ∈ (X7 c.s).subgroupOf (y7bX c.s) := hx
  exact (hker ⟨x, hxX⟩).mp (htriv ⟨x, hxX⟩ hmemY)

theorem y7b_K_eq_X7 (c : Ctx7 G L) (hb : B5Std c) : y7bK c.s = X7 c.s := by
  have hmul := Subgroup.relIndex_mul_relIndex (X7 c.s) (y7bK c.s) (y7bX c.s)
    (y7b_X7_le_K c hb) (inf_le_left : y7bK c.s ≤ y7bX c.s)
  rw [y7b_relIndex_X7_X c hb, y7b_relIndex_K_X c hb] at hmul
  have hone : (X7 c.s).relIndex (y7bK c.s) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) (y7b_X7_le_K c hb)

theorem y7b_M4_le_X7 (c : Ctx7 G L) (hb : B5Std c) : M4 c.e ≤ X7 c.s := by
  rw [← y7b_K_eq_X7 c hb]
  intro m hm
  refine Subgroup.mem_inf.mpr ⟨y7b_M4_le_X c hb hm, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvM4 : v ∈ M4 c.e := by
    have h := y7b_V_le_V2 c hb hv
    rw [V2] at h
    exact (Subgroup.mem_inf.mp h).2
  haveI : IsMulCommutative ↥(M4 c.e) := (hb.h72.2.1).1
  exact congrArg Subtype.val
    (mul_comm' (⟨v, hvM4⟩ : ↥(M4 c.e)) ⟨m, hm⟩)

end CFSG.OddStandard.HigherRank.YamadaG23
