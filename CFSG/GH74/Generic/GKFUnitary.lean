module

public import CFSG.GH74.Generic.S1.SymSchur
public import CFSG.GH74.Generic.GKFTables

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Blueprint
  CFSG.Blueprint.Multiplier CFSG.LocalAnalysis.ComponentInitial

theorem exists_unitaryFieldData_of_odd {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : Odd q) :
    ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f ∧ p ≠ 2 := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := CFSG.GH74.L5U5.exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact hq.pow
  have hp2 : p ≠ 2 := CFSG.GH74.L5U5.prime_ne_two_of_odd_card (F := F) (p := p) hodd
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    simp at hF
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  exact ⟨p, f, ⟨hp.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩, rfl, hp2⟩

open CFSG.ComponentClassification.TBLit in
theorem psu4_cover_of_griess (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K)) (F : Type) [Field F] [Finite F]
    (q : ℕ) (hF : Nat.card F = q ^ 2) (hq : Odd q)
    (e : K ⧸ center K ≃* StatedProj (StatedSU 4 q F)) :
    ∃ π : StatedSU 4 q F →* K, Function.Surjective π ∧
      ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g := by
  obtain ⟨p, n, hu, rfl, hp2⟩ := exists_unitaryFieldData_of_odd hF hq
  have hp : p.Prime := hu.prime
  have : Fact p.Prime := ⟨hp⟩
  have hm : CFSG.Models.LieModel (StatedProj (StatedSU 4 (p ^ n) F)) .PSU 4 p n :=
    S1.lieModel_psu_four hp hu.one_le hF (MulEquiv.refl _)
  have hexc : Odd (exceptionalOrders .PSU 4 p n).1 ∧ Odd (exceptionalOrders .PSU 4 p n).2 := by
    unfold exceptionalOrders
    split <;> simp_all
  have hmodd : Odd ((exceptionalOrders .PSU 4 p n).1 * (exceptionalOrders .PSU 4 p n).2) :=
    hexc.1.mul hexc.2
  have hcardM : Nat.card (hopfMultiplier (StatedProj (StatedSU 4 (p ^ n) F))) =
      Nat.gcd 4 (p ^ n + 1) *
        ((exceptionalOrders .PSU 4 p n).1 * (exceptionalOrders .PSU 4 p n).2) := by
    rw [card_hopfMultiplier_of_griess hGA hm]
    have hgen : genericOrders .PSU 4 p n = (Nat.gcd 4 (p ^ n + 1), 1) := rfl
    rw [hgen]
    simp
  let p₀ : ↥(StatedSU 4 (p ^ n) F) →* StatedProj (StatedSU 4 (p ^ n) F) := QuotientGroup.mk' _
  have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
  have hk₀ : p₀.ker = (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (p ^ n) F) :=
    QuotientGroup.ker_mk' _
  have hk₀c : p₀.ker ≤ center ↥(StatedSU 4 (p ^ n) F) := by
    rw [hk₀]
    exact CFSG.LieType.Universal.Spin.statedScalars_subgroupOf_le_center _
  have hS₀ : Group.IsPerfect ↥(StatedSU 4 (p ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (by norm_num) (fun h => by
      simp only [Prod.mk.injEq] at h
      omega)
  obtain ⟨α, hαs, hαc⟩ := exists_lift_of_odd_index hS₀ hK.1 p₀ hp₀ hk₀c (centralQuotientMap e)
    (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    (by rw [centralQuotientMap_ker e]; exact h2) _ hmodd
    (by rw [hcardM, hk₀, S1.card_scalars_statedSU_four hp hu.one_le hF])
  refine ⟨α, hαs, fun g => ?_⟩
  have h1 := congrArg (fun f => f g) hαc
  exact h1

end CFSG.GH74.Generic
