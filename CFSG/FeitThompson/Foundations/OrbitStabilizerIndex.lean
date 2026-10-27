module

public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open Pointwise MulAction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] (H : Subgroup G)

def quotientToRangeLeftCoset : G ⧸ H → (Set.range fun g : G => g • (H : Set G)) :=
  Quotient.lift (fun g => ⟨g • (H : Set G), ⟨g, rfl⟩⟩) fun _ _ hab =>
    Subtype.ext ((leftCoset_eq_iff H).mpr (QuotientGroup.leftRel_apply.mp hab))

@[simp]
theorem quotientToRangeLeftCoset_mk (g : G) :
    (quotientToRangeLeftCoset H g : Set G) = g • (H : Set G) := (rfl)

theorem quotientToRangeLeftCoset_bijective : Function.Bijective (quotientToRangeLeftCoset H) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · induction a using QuotientGroup.induction_on with
    | _ a =>
    induction b using QuotientGroup.induction_on with
    | _ b =>
    refine QuotientGroup.eq.mpr ((leftCoset_eq_iff H).mp ?_)
    simpa using congrArg Subtype.val hab
  · rintro ⟨s, g, rfl⟩
    exact ⟨(g : G ⧸ H), Subtype.ext (by simp)⟩

noncomputable def quotientEquivRangeLeftCoset :
    G ⧸ H ≃ (Set.range fun g : G => g • (H : Set G)) :=
  Equiv.ofBijective _ (quotientToRangeLeftCoset_bijective H)

@[simp]
theorem coe_quotientEquivRangeLeftCoset_mk (g : G) :
    (quotientEquivRangeLeftCoset H (g : G ⧸ H) : Set G) = g • (H : Set G) := by
  simp [quotientEquivRangeLeftCoset]

variable {X : Type*} [MulAction G X] (x : X)

theorem smul_eq_smul_iff_leftCoset_stabilizer_eq (g h : G) :
    g • x = h • x ↔ g • (stabilizer G x : Set G) = h • (stabilizer G x : Set G) := by
  rw [leftCoset_eq_iff, mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, eq_comm]

noncomputable def leftCosetStabilizerEquivOrbit :
    (Set.range fun g : G => g • (stabilizer G x : Set G)) ≃ orbit G x :=
  (quotientEquivRangeLeftCoset (stabilizer G x)).symm.trans
    (orbitEquivQuotientStabilizer G x).symm

@[simp]
theorem leftCosetStabilizerEquivOrbit_apply (g : G)
    (hg : g • (stabilizer G x : Set G) ∈ Set.range fun g : G => g • (stabilizer G x : Set G)) :
    (leftCosetStabilizerEquivOrbit x ⟨_, hg⟩ : X) = g • x := by
  have h : (⟨g • (stabilizer G x : Set G), hg⟩ :
      (Set.range fun g : G => g • (stabilizer G x : Set G))) =
      quotientEquivRangeLeftCoset (stabilizer G x) (g : G ⧸ stabilizer G x) :=
    Subtype.ext (by simp)
  rw [h]
  simp [leftCosetStabilizerEquivOrbit]

@[simp]
theorem leftCosetStabilizerEquivOrbit_symm_apply (g : G) :
    (leftCosetStabilizerEquivOrbit x).symm ⟨g • x, mem_orbit x g⟩ =
      ⟨g • (stabilizer G x : Set G), ⟨g, rfl⟩⟩ := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (leftCosetStabilizerEquivOrbit_apply x g ⟨g, rfl⟩).symm

theorem natCard_range_leftCoset_stabilizer :
    Nat.card (Set.range fun g : G => g • (stabilizer G x : Set G)) = Nat.card (orbit G x) :=
  Nat.card_congr (leftCosetStabilizerEquivOrbit x)

theorem natCard_orbit_eq_index_stabilizer :
    Nat.card (orbit G x) = (stabilizer G x).index := by
  rw [← natCard_range_leftCoset_stabilizer, natCard_range_leftCoset]

theorem natCard_orbit_mul_natCard_stabilizer :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  rw [← natCard_range_leftCoset_stabilizer, ← natCard_eq_natCard_range_leftCoset_mul_natCard]

theorem natCard_orbit_eq_natCard_div_natCard_stabilizer [Finite G] :
    Nat.card (orbit G x) = Nat.card G / Nat.card (stabilizer G x) :=
  (Nat.div_eq_of_eq_mul_left Nat.card_pos (natCard_orbit_mul_natCard_stabilizer x).symm).symm

end

end CFSG.FeitThompson
