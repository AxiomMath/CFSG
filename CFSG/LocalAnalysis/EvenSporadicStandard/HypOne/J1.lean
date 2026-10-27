module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Walter.J1.Local

public section

namespace CFSG.EvenSporadicStandard.HypOne.J1

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.Walter CFSG.Open

theorem forall_pow_four_walterJ1 :
    ∀ x : walterJ1, x ^ 4 = 1 → x ^ 2 = 1 := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hi]
    change (x ^ i) ^ 4 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have := (Walter.J1Props.jankoHyp.sylow_structure S).2.1 x (hS (Subgroup.mem_zpowers x))
  rwa [← sq] at this

theorem forall_pow_four_native :
    ∀ x : NativeSporadic.J1, x ^ 4 = 1 → x ^ 2 = 1 := by
  intro x hx
  have := forall_pow_four_walterJ1 (walterJ1EquivNative.symm x) (by
    rw [← map_pow, hx, map_one])
  have h := congrArg walterJ1EquivNative this
  rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.J1 := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.J1.fam_j1_simplicity
  have := hfin
  have := hsimple
  refine hypothesisOne_of_inner_of_forall_pow_four ?_
    (CFSG.Sporadic.Schreier.at_j1_schreier).2.1 forall_pow_four_native
  apply center_eq_bot_of_isSimpleGroup
  rw [CFSG.Sporadic.J1.card_J1]
  norm_num

end CFSG.EvenSporadicStandard.HypOne.J1
