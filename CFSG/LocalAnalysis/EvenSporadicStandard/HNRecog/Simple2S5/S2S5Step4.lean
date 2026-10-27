module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open scoped Pointwise

private lemma natCard_subgroupOf_inf {G : Type*} [Group G] (Y O : Subgroup G) :
    Nat.card ↥(O.subgroupOf Y) = Nat.card ↥(Y ⊓ O) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }

theorem exists_mul_of_card {G : Type*} [Group G] [Finite G] {C Y O : Subgroup G} (hYC : Y ≤ C)
    (hOC : O ≤ C) (hcard : Nat.card ↥C * Nat.card ↥(Y ⊓ O) ≤ Nat.card ↥Y * Nat.card ↥O) :
    ∀ c ∈ C, ∃ y ∈ Y, ∃ o ∈ O, c = y * o := by
  haveI : Nonempty ↥(Y ⊓ O) := ⟨1⟩
  haveI : Finite ↥(Y ⊓ O) := Finite.of_injective Subtype.val Subtype.val_injective
  have hmul := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := O) (t := (Y : Set G))
  have himg : ((Y : Set G).image (QuotientGroup.mk : G → G ⧸ O)) =
      MulAction.orbit ↥Y (((1 : G) : G ⧸ O)) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, by simp [Subgroup.smul_def]⟩
  have hstab : MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O)) = O.subgroupOf Y := by
    rw [← MulAction.stabilizer_subgroupOf Y (((1 : G) : G ⧸ O)), MulAction.stabilizer_quotient O]
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O))) =
      Nat.card ↥(Y ⊓ O) := by
    rw [hstab, natCard_subgroupOf_inf]
  have hcardimg : Nat.card ↥(((Y : Set G).image (QuotientGroup.mk : G → G ⧸ O)) : Set (G ⧸ O)) =
      Nat.card ↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) := by
    rw [himg]
  have hos : Nat.card ↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) *
      Nat.card ↥(MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O))) = Nat.card ↥Y := by
    calc Nat.card ↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) *
          Nat.card ↥(MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O)))
        = Nat.card (↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) ×
            ↥(MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O)))) := (Nat.card_prod _ _).symm
      _ = Nat.card ↥Y :=
          Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := ↥Y) (((1 : G) : G ⧸ O)))
  have hprod : Nat.card ↥((Y : Set G) * (O : Set G)) * Nat.card ↥(Y ⊓ O) =
      Nat.card ↥Y * Nat.card ↥O := by
    calc Nat.card ↥((Y : Set G) * (O : Set G)) * Nat.card ↥(Y ⊓ O)
        = (Nat.card ↥O *
            Nat.card ↥(((Y : Set G).image (QuotientGroup.mk : G → G ⧸ O)) : Set (G ⧸ O))) *
            Nat.card ↥(Y ⊓ O) := by rw [hmul]
      _ = Nat.card ↥O *
            (Nat.card ↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) * Nat.card ↥(Y ⊓ O)) := by
            rw [mul_assoc, hcardimg]
      _ = Nat.card ↥O *
            (Nat.card ↥(MulAction.orbit ↥Y (((1 : G) : G ⧸ O))) *
              Nat.card ↥(MulAction.stabilizer ↥Y (((1 : G) : G ⧸ O)))) := by rw [hstabcard]
      _ = Nat.card ↥O * Nat.card ↥Y := by rw [hos]
      _ = Nat.card ↥Y * Nat.card ↥O := mul_comm _ _
  have hCYO : Nat.card ↥C ≤ Nat.card ↥((Y : Set G) * (O : Set G)) := by
    rw [← hprod] at hcard
    exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  have hsub : ((Y : Set G) * (O : Set G)) ⊆ (C : Set G) := by
    intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨y, hy, o, ho, rfl⟩ := hx
    exact C.mul_mem (hYC hy) (hOC ho)
  have hYOC : ((Y : Set G) * (O : Set G)) = (C : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by
      have h := hCYO
      rw [show Nat.card ↥C = (C : Set G).ncard from rfl,
        show Nat.card ↥((Y : Set G) * (O : Set G)) =
          ((Y : Set G) * (O : Set G)).ncard from rfl] at h
      exact h)
  intro c hc
  have hc' : c ∈ (Y : Set G) * (O : Set G) := by rw [hYOC]; exact hc
  rw [Set.mem_mul] at hc'
  obtain ⟨y, hy, o, ho, hc_eq⟩ := hc'
  exact ⟨y, hy, o, ho, hc_eq.symm⟩

theorem pow_mem_of_coset {G : Type*} [Group G] {C O : Subgroup G}
    (hOn : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) {s y o : G} (hs : s ∈ C) (ho : o ∈ O)
    (hy : y = s * o) {n : ℕ} (hsn : s ^ n ∈ O) : y ^ n ∈ O := by
  have key : ∀ m : ℕ, ∃ o' ∈ O, (s * o) ^ m = s ^ m * o' := by
    intro m
    induction m with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨o', ho', h⟩ := ih
      refine ⟨(s⁻¹ * o' * s) * o, O.mul_mem ?_ ho, ?_⟩
      · simpa using hOn s⁻¹ (C.inv_mem hs) o' ho'
      · rw [pow_succ, h, pow_succ]
        simp only [mul_assoc]
        rw [mul_inv_cancel_left]
  obtain ⟨o', ho', h⟩ := key n
  rw [hy, h]
  exact O.mul_mem hsn ho'

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
