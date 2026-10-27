module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_model_classify (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx : x * x = 1) :
    x = 1 ∨ KM0 x ∨ KM1 x ∨ KM2 x ∨ KM3 x ∨ KM4 x := by
  by_cases hG : SimInGStar x
  · obtain ⟨y, hyx⟩ := hG
    have hy2 : y * y = 1 :=
      projOrthToProjSim_injective (by rw [map_mul, hyx, hx, map_one])
    have hnot : ¬ (Even (Module.finrank (ZMod 3) V) ∧
        quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2)) := by
      rintro ⟨-, hq⟩
      rw [hdim, hsgn] at hq
      exact absurd hq (by decide)
    obtain ⟨t, htt, htoy⟩ := exists_lift_of_mul_self_eq_one hQ hnot hy2
    by_cases hy1 : y = 1
    · left
      rw [← hyx, hy1, map_one]
    · right
      rw [← hyx]
      rcases km0123_of_involution hQ hdim hsgn htt htoy hy1 with h0 | h1 | h2 | h3
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hG))))

theorem ff_KM0_ne_one {x : ProjSim Q} (h : KM0 x) : x ≠ 1 :=
  simHasType_ne_one h

theorem ff_KM1_ne_one {x : ProjSim Q} (h : KM1 x) : x ≠ 1 :=
  simHasType_ne_one h

theorem ff_KM1_sq {x : ProjSim Q} (h : KM1 x) : x * x = 1 :=
  simHasType_sq h

theorem ff_KM0_inner (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (h : KM0 x) : SimInOmegaStar hQ x := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  refine ⟨y, ?_, hyx⟩
  rw [mem_omegaProj_iff]
  refine ⟨t, ?_, htoy⟩
  rw [involution_mem_omegaGroup_iff hQ htt]
  exact ⟨by rw [show invDim t = 4 from congrArg Prod.fst hty]; decide,
    by rw [show invSign t = 1 from congrArg Prod.snd hty,
      show invDim t = 4 from congrArg Prod.fst hty]; decide⟩

theorem ff_KM1_inner (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (h : KM1 x) : SimInOmegaStar hQ x := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  refine ⟨y, ?_, hyx⟩
  rw [mem_omegaProj_iff]
  refine ⟨t, ?_, htoy⟩
  rw [involution_mem_omegaGroup_iff hQ htt]
  exact ⟨by rw [show invDim t = 2 from congrArg Prod.fst hty]; decide,
    by rw [show invSign t = -1 from congrArg Prod.snd hty,
      show invDim t = 2 from congrArg Prod.fst hty]; decide⟩

theorem ff_KM2_not_inner (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (h : KM2 x) : ¬ SimInOmegaStar hQ x := by
  rintro ⟨y', hy'om, hy'x⟩
  obtain ⟨_, y, hyx, hy1, t, htt, hty, htoy⟩ := h
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hyom : y ∈ omegaProj hQ := hyy ▸ hy'om
  have hodd : Odd (invDim t) := by
    rw [show invDim t = 1 from congrArg Prod.fst hty]
    decide
  exact not_mem_omegaProj_of_odd_invDim hQ hdim hyom htt htoy hodd

theorem ff_KM3_not_inner (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (h : KM3 x) : ¬ SimInOmegaStar hQ x := by
  rintro ⟨y', hy'om, hy'x⟩
  obtain ⟨_, y, hyx, hy1, t, htt, hty, htoy⟩ := h
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hyom : y ∈ omegaProj hQ := hyy ▸ hy'om
  have hodd : Odd (invDim t) := by
    rw [show invDim t = 3 from congrArg Prod.fst hty]
    decide
  exact not_mem_omegaProj_of_odd_invDim hQ hdim hyom htt htoy hodd

theorem ff_KM4_not_inner (hQ : Q.Nondegenerate) {x : ProjSim Q} (h : KM4 x) :
    ¬ SimInOmegaStar hQ x :=
  fun hx => h (SimInOmegaStar.simInGStar hx)

theorem ff_conj_KM0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {u u' : ↥(omegaProj hQ)} (hu : KM0 (projOrthToProjSim Q (u : ProjOrth Q)))
    (hu' : KM0 (projOrthToProjSim Q (u' : ProjOrth Q))) :
    ∃ a : ↥(omegaProj hQ), a * u * a⁻¹ = u' :=
  conj_of_simHasType_even (r := 4) (α := 1) hQ hdim hu hu' (by decide) (by decide)

theorem ff_conj_KM1 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {u u' : ↥(omegaProj hQ)} (hu : KM1 (projOrthToProjSim Q (u : ProjOrth Q)))
    (hu' : KM1 (projOrthToProjSim Q (u' : ProjOrth Q))) :
    ∃ a : ↥(omegaProj hQ), a * u * a⁻¹ = u' :=
  conj_of_simHasType_even (r := 2) (α := -1) hQ hdim hu hu' (by decide) (by decide)

end CFSG.OddStandard.SmallF3.Omega
