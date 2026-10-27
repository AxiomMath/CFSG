module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12SpMono
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Out
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.GH74.GLS.Stage2.Final.ModelDisjoint
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem eq_zero_or_one_or_neg_one_of_card_three {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 3) (x : K) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have := Fintype.ofFinite K
  have hx : x ^ 3 = x := by
    have := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, h] at this
  have h0 : x * ((x - 1) * (x + 1)) = 0 := by linear_combination hx
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h2))

theorem isPGroup_outer_psp4 {K : Type} [Field K] [Finite K] (h3 : ∀ x : K, x = 0 ∨ x = 1 ∨ x = -1)
    (hodd : ringChar K ≠ 2) : IsPGroup 2 (Outer (StatedProj (StatedSp 2 K))) := by
  intro x
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd α
  have hσ : σ = 1 := RingEquiv.ext fun y => by
    rcases h3 y with rfl | rfl | rfl <;> simp
  subst hσ
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, map_one, mul_one, ← map_pow]
  exact conjAut_inner_of_multiplier_sq (A ^ 2) (multiplier 2 K A) (by rw [map_pow, sq])

theorem not_sylCfgOf_Sp43 {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hns : ¬ Group.IsSolvable Y) (hM : LieModel Y .PSp 2 3 1) : ¬ SylCfgOf Y := by
  have hc : center Y = ⊥ := center_eq_bot_of_simple hs hns
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hM
  rw [pow_one] at hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  have hodd : ringChar F ≠ 2 := by
    rw [ringChar.eq F 3]
    norm_num
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have h3 := eq_zero_or_one_or_neg_one_of_card_three hcard
  have hout : IsPGroup 2 (Outer Y) := (isPGroup_outer_psp4 h3 hodd).of_equiv (equivalence e).symm
  refine not_sylCfgOf_of_irreducible hc hout (StatedSp 2 F) e (sgnGroupS F) isPGroup_sgnGroupS
    fun W hW => ?_
  exact eq_bot_or_top_of_sp_invariant h3 h2 W
    (fun w hw => hW _ ⟨monoGLS_mem_sgnGroupS 0 spEa spEa_pm, monoGLS_a_mem⟩ w hw)
    (fun w hw => hW _ ⟨monoGLS_mem_sgnGroupS 1 spEs spEs_pm, monoGLS_s_mem⟩ w hw)
    (fun w hw => hW _ ⟨monoGLS_mem_sgnGroupS 2 spEt spEt_pm, monoGLS_t_mem⟩ w hw)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
