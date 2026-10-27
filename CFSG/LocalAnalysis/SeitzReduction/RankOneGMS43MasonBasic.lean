module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace GMS43

variable {P : Type*} [Group P]

theorem isConj_mul_zpow {j j' : P} (hj : j * j = 1) (hj' : IsConj j j') (k : ℤ) :
    IsConj j (j * (j * j') ^ k) := by
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  obtain ⟨g, hg⟩ := isConj_iff.mp hj'
  have hj'j' : j' * j' = 1 := by
    rw [← hg, show g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ by group, hj]
    group
  have hj'inv : j'⁻¹ = j' := inv_eq_of_mul_eq_one_right hj'j'
  set c := j * j' with hc
  have hjc : ∀ n : ℤ, j * c ^ n = c ^ (-n) * j := by
    intro n
    have h1 : j * c * j⁻¹ = c⁻¹ := by
      rw [hc, mul_inv_rev, hjinv, hj'inv]
      calc j * (j * j') * j = (j * j) * j' * j := by group
        _ = j' * j := by rw [hj, one_mul]
    have h2 : j * c ^ n * j⁻¹ = c ^ (-n) := by rw [← conj_zpow, h1, zpow_neg, inv_zpow]
    calc j * c ^ n = j * c ^ n * j⁻¹ * j := by group
      _ = c ^ (-n) * j := by rw [h2]
  have hconj : ∀ i : ℤ, c ^ (-i) * j * (c ^ (-i))⁻¹ = j * c ^ (2 * i) := by
    intro i
    calc c ^ (-i) * j * (c ^ (-i))⁻¹ = c ^ (-i) * (j * c ^ i) := by
          rw [← zpow_neg, neg_neg, mul_assoc]
      _ = c ^ (-i) * (c ^ (-i) * j) := by rw [hjc i]
      _ = c ^ (-(2 * i)) * j := by
          rw [← mul_assoc, ← zpow_add, show -i + -i = -(2 * i) by ring]
      _ = j * c ^ (2 * i) := (hjc (2 * i)).symm
  obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' k
  · exact isConj_iff.mpr ⟨c ^ (-i), hconj i⟩
  · have hj'c : j * c = j' := by rw [hc, ← mul_assoc, hj, one_mul]
    refine hj'.trans (isConj_iff.mpr ⟨c ^ (-i), ?_⟩)
    calc c ^ (-i) * j' * (c ^ (-i))⁻¹ = c ^ (-i) * j * (c * c ^ i) := by
          rw [← hj'c, ← zpow_neg, neg_neg]; group
      _ = c ^ (-i) * j * (c ^ (-i))⁻¹ * c := by
          rw [← zpow_one_add, add_comm, zpow_add_one, ← zpow_neg, neg_neg]; group
      _ = j * c ^ (2 * i + 1) := by rw [hconj i, zpow_add_one, mul_assoc]

theorem ncard_mul_zpow (a w : P) : {x : P | ∃ i : ℤ, x = a * w ^ i}.ncard = orderOf w := by
  have h : {x : P | ∃ i : ℤ, x = a * w ^ i} = (a * ·) '' (zpowers w : Set P) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, mem_zpowers_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨w ^ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [h, Set.ncard_image_of_injective _ (mul_right_injective a), ← Nat.card_coe_set_eq]
  exact Nat.card_zpowers w

theorem isConj_iff_of_orderOf_eq_index [Finite P] {j c : P}
    (hc : ∀ k : ℤ, IsConj j (j * c ^ k))
    (hord : orderOf c = (centralizer ({j} : Set P)).index) (x : P) :
    IsConj j x ↔ ∃ i : ℤ, x = j * c ^ i := by
  have hsub : {x : P | ∃ i : ℤ, x = j * c ^ i} ⊆ conjugatesOf j := by
    rintro _ ⟨i, rfl⟩
    exact hc i
  have heq : {x : P | ∃ i : ℤ, x = j * c ^ i} = conjugatesOf j :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [ncard_mul_zpow, hord, Subgroup.index_centralizer_eq_ncard]) (Set.toFinite _)
  constructor
  · intro hx
    have hx' : x ∈ conjugatesOf j := hx
    rw [← heq] at hx'
    exact hx'
  · rintro ⟨i, rfl⟩
    exact hc i

theorem isConj_subtype_iff {M : Subgroup P} (a b : M) :
    IsConj a b ↔ ∃ h ∈ M, h * (a : P) * h⁻¹ = b := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · rintro ⟨h, hh, hb⟩
    exact ⟨⟨h, hh⟩, Subtype.ext hb⟩

end GMS43

end CFSG.SeitzReduction.RankOne
