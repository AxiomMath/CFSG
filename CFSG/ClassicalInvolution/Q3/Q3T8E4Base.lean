module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenL33
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_two_pow {a : G} {m : ℕ} (h : a ^ 2 ^ m = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers a) := by
  have hd : orderOf a ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem commutator_mem_oddCoreOf_of_pow3 {M R : Subgroup G} {z : G}
    (hz : IsUniqueInvolution M z) (hR : IsSylow2In R M) {y : G}
    (hyN : y ∈ Subgroup.normalizer (M : Set G)) {m : ℕ} (hym : y ^ 2 ^ m = 1)
    (hyR : ∀ r ∈ R, y * r = r * y) : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M := by
  intro k hk
  refine Disconnected.AschTight.Sec6Gen.commutator_mem_oddCoreOf_of_centralizes hz hR
    (isPGroup_zpowers_of_pow_two_pow hym)
    (fun v hv => mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hyN hv))
    (fun r hr v hv => ?_) k hk y (Subgroup.mem_zpowers y)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact (Commute.zpow_right (show Commute r y from (hyR r hr).symm) n).eq

end CFSG.ClassicalInvolution.Q3.Q3T8
