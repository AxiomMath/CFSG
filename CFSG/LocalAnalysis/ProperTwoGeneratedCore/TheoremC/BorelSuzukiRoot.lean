module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsSuzuki

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open scoped commutatorElement

namespace BorelSuzuki

theorem inCenterOf_coe_iff {X : Type*} [Group X] (Q : Subgroup X) (z : Q) :
    InCenterOf Q (z : X) ↔ z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2)
  · intro h
    exact ⟨z.2, fun q hq => congrArg Subtype.val (h ⟨q, hq⟩)⟩

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem inCenterOf_iff (hm : 0 < m) (w : G) :
    InCenterOf (suzukiCoverRoot m) w ↔ ∃ b : K, w = suzukiCoverRootElement m 0 b := by
  have hZ := (suzukiCoverRoot_structure m hm).2.2.1
  constructor
  · rintro ⟨hw, hc⟩
    have hz : (⟨w, hw⟩ : suzukiCoverRoot m) ∈ commutator (suzukiCoverRoot m) := by
      rw [hZ, ← inCenterOf_coe_iff]
      exact ⟨hw, hc⟩
    obtain ⟨b, hb⟩ := ((suzukiCoverRoot_structure m hm).2.2.2 _).mp hz
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, rfl⟩
    rw [inCenterOf_coe_iff, ← hZ]
    exact ((suzukiCoverRoot_structure m hm).2.2.2 _).mpr ⟨b, rfl⟩

theorem inCenterOf_root_zero (hm : 0 < m) (b : K) :
    InCenterOf (suzukiCoverRoot m) (suzukiCoverRootElement m 0 b : G) :=
  (inCenterOf_iff m hm _).mpr ⟨b, rfl⟩

theorem inCenterOf_commutator (hm : 0 < m) {a b : G} (ha : a ∈ suzukiCoverRoot m)
    (hb : b ∈ suzukiCoverRoot m) : InCenterOf (suzukiCoverRoot m) (a * b * a⁻¹ * b⁻¹) := by
  have h : ⁅(⟨a, ha⟩ : suzukiCoverRoot m), ⟨b, hb⟩⁆ ∈ Subgroup.center (suzukiCoverRoot m) := by
    rw [← (suzukiCoverRoot_structure m hm).2.2.1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact (inCenterOf_coe_iff _ _).mpr h

theorem inCenterOf_mul_self (hm : 0 < m) {a : G} (ha : a ∈ suzukiCoverRoot m) :
    InCenterOf (suzukiCoverRoot m) (a * a) := by
  obtain ⟨x, y, hxy⟩ := suzukiCoverRootElement_surjective m ⟨a, ha⟩
  rw [inCenterOf_iff m hm]
  refine ⟨x * suzukiCoverTits m x, ?_⟩
  rw [← BenderFacts.suzukiCoverRootElement_sq m hm x y, hxy, pow_two]
  rfl

theorem card_inCenterOf (hm : 0 < m) :
    Nat.card {w : G // InCenterOf (suzukiCoverRoot m) w} = 2 ^ (2 * m + 1) := by
  rw [← GaloisField.card 2 (2 * m + 1) (by omega)]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun b : K => (⟨(suzukiCoverRootElement m 0 b : G), inCenterOf_root_zero m hm b⟩ :
      {w : G // InCenterOf (suzukiCoverRoot m) w})) ⟨?_, ?_⟩)).symm
  · intro b c hbc
    have h : (suzukiCoverRootElement m 0 b : G) = suzukiCoverRootElement m 0 c :=
      congrArg (fun z : {w : G // InCenterOf (suzukiCoverRoot m) w} => z.1) hbc
    exact (suzukiCoverRootElement_injective m _ _ _ _ (Subtype.ext h)).2
  · rintro ⟨w, hw⟩
    obtain ⟨b, rfl⟩ := (inCenterOf_iff m hm w).mp hw
    exact ⟨b, rfl⟩

theorem root_mul (hm : 0 < m) (a b c d : K) :
    (suzukiCoverRootElement m a b : G) * suzukiCoverRootElement m c d =
      suzukiCoverRootElement m (a + c) (b + d + a * suzukiCoverTits m c) :=
  congrArg Subtype.val (suzukiCoverRootElement_mul m hm a b c d)

theorem root_eq_mul (hm : 0 < m) (a b : K) :
    (suzukiCoverRootElement m a b : G) =
      suzukiCoverRootElement m a 0 * suzukiCoverRootElement m 0 b := by
  rw [root_mul m hm, map_zero, mul_zero, add_zero, zero_add, add_zero]

theorem exists_eq_root {a : G} (ha : a ∈ suzukiCoverRoot m) :
    ∃ x y : K, a = suzukiCoverRootElement m x y := by
  obtain ⟨x, y, hxy⟩ := suzukiCoverRootElement_surjective m ⟨a, ha⟩
  exact ⟨x, y, (congrArg Subtype.val hxy).symm⟩

end BorelSuzuki

end CFSG.ProperTwoGeneratedCore.TheoremC
