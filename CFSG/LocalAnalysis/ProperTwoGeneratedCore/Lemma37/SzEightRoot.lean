module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzuki

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.BenderFacts

structure SzEightSylowFacts (R : Type*) [Group R] : Prop where
  comm_of_sq : ∀ x : R, x ^ 2 = 1 → ∀ y : R, x * y = y * x
  sq_of_comm : ∀ x : R, (∀ y : R, x * y = y * x) → x ^ 2 = 1
  pow_four : ∀ x : R, x ^ 4 = 1
  comm_of_sq_eq : ∀ x y : R, x ^ 2 = y ^ 2 → x ^ 2 ≠ 1 → x * y = y * x
  exists_noncomm : ∀ x : R, x ^ 2 ≠ 1 →
    ∃ r₁ r₂ : R, x * r₁ ≠ r₁ * x ∧ x * r₂ ≠ r₂ * x ∧ x * (r₁ * r₂) ≠ r₁ * r₂ * x

theorem SzEightSylowFacts.congr {A B : Type*} [Group A] [Group B] (h : SzEightSylowFacts A)
    (θ : A ≃* B) : SzEightSylowFacts B where
  comm_of_sq x hx y := by
    have h1 := h.comm_of_sq (θ.symm x) (by rw [← map_pow, hx, map_one]) (θ.symm y)
    simpa using congrArg θ h1
  sq_of_comm x hx := by
    have h1 := h.sq_of_comm (θ.symm x) fun y => by
      have h2 := hx (θ y)
      apply θ.injective
      simpa using h2
    simpa using congrArg θ h1
  pow_four x := by simpa using congrArg θ (h.pow_four (θ.symm x))
  comm_of_sq_eq x y hxy hx := by
    have h1 := h.comm_of_sq_eq (θ.symm x) (θ.symm y) (by rw [← map_pow, ← map_pow, hxy])
      (by rw [← map_pow, ne_eq, map_eq_one_iff _ θ.symm.injective]; exact hx)
    simpa using congrArg θ h1
  exists_noncomm x hx := by
    obtain ⟨r₁, r₂, h₁, h₂, h₃⟩ := h.exists_noncomm (θ.symm x)
      (by rw [← map_pow, ne_eq, map_eq_one_iff _ θ.symm.injective]; exact hx)
    refine ⟨θ r₁, θ r₂, fun e => h₁ ?_, fun e => h₂ ?_, fun e => h₃ ?_⟩ <;>
      apply θ.injective <;> simpa using e

local notation "K" => BinaryGaloisField (2 * 1 + 1)

theorem card_binaryGaloisField_three : Nat.card K = 8 := by
  rw [GaloisField.card 2 (2 * 1 + 1) (by norm_num)]
  norm_num

theorem pow_fifteen_eq (u : K) : u ^ 15 = u := by
  have : Fintype K := Fintype.ofFinite K
  have h8 : u ^ 8 = u := by
    have h := FiniteField.pow_card u
    rwa [Fintype.card_eq_nat_card, card_binaryGaloisField_three] at h
  calc u ^ 15 = u ^ 8 * u ^ 7 := by ring
    _ = u * u ^ 7 := by rw [h8]
    _ = u ^ 8 := by ring
    _ = u := h8

theorem eq_of_pow_three_eq {a c : K} (h : c ^ 3 = a ^ 3) : c = a := by
  rw [← pow_fifteen_eq c, ← pow_fifteen_eq a, show 15 = 3 * 5 by norm_num, pow_mul, pow_mul, h]

theorem suzukiCoverTits_one_apply (c : K) : suzukiCoverTits 1 c = c ^ 4 := by
  rw [suzukiCoverTits_apply]
  norm_num

theorem mul_tits_ne {a c : K} (ha : a ≠ 0) (hc : c ≠ 0) (hca : c ≠ a) :
    a * suzukiCoverTits 1 c ≠ c * suzukiCoverTits 1 a := by
  rw [suzukiCoverTits_one_apply, suzukiCoverTits_one_apply]
  intro h
  apply hca
  apply eq_of_pow_three_eq
  have h' : a * c * c ^ 3 = a * c * a ^ 3 := by
    calc a * c * c ^ 3 = a * c ^ 4 := by ring
      _ = c * a ^ 4 := h
      _ = a * c * a ^ 3 := by ring
  exact mul_left_cancel₀ (mul_ne_zero ha hc) h'

theorem root_commute_iff (a b c d : K) :
    suzukiCoverRootElement 1 a b * suzukiCoverRootElement 1 c d =
        suzukiCoverRootElement 1 c d * suzukiCoverRootElement 1 a b ↔
      a * suzukiCoverTits 1 c = c * suzukiCoverTits 1 a := by
  rw [suzukiCoverRootElement_mul 1 one_pos, suzukiCoverRootElement_mul 1 one_pos]
  constructor
  · intro h
    have h2 := (suzukiCoverRootElement_injective 1 _ _ _ _ h).2
    rw [add_comm d b] at h2
    exact add_left_cancel h2
  · intro h
    rw [add_comm a c, add_comm d b, h]

theorem szEightSylowFacts_suzukiCoverRoot : SzEightSylowFacts (suzukiCoverRoot 1) := by
  have hm : 0 < 1 := one_pos
  have hsq1 : ∀ a b : K, suzukiCoverRootElement 1 a b ^ 2 = 1 ↔ a = 0 :=
    suzukiCoverRootElement_sq_eq_one_iff 1 hm
  refine ⟨(benderRootData_suzukiCoverRoot 1 hm).comm, benderCenterSqOne_suzukiCoverRoot 1 hm,
    fun x => ?_, fun x y hxy hx => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective 1 x
    calc suzukiCoverRootElement 1 a b ^ 4 = (suzukiCoverRootElement 1 a b ^ 2) ^ 2 := by
          rw [← pow_mul]
      _ = 1 := by rw [suzukiCoverRootElement_sq 1 hm, hsq1]
  · obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective 1 x
    obtain ⟨c, d, rfl⟩ := suzukiCoverRootElement_surjective 1 y
    rw [suzukiCoverRootElement_sq 1 hm, suzukiCoverRootElement_sq 1 hm] at hxy
    have ha : a ≠ 0 := fun h => hx ((hsq1 a b).mpr h)
    have hr : a * suzukiCoverTits 1 a ≠ 0 :=
      mul_ne_zero ha ((map_ne_zero (suzukiCoverTits 1)).mpr ha)
    have hac := (suzukiCoverRootElement_injective 1 _ _ _ _ hxy).2
    obtain ⟨a₀, -, huniq⟩ := existsUnique_mul_suzukiCoverTits_eq 1 hr
    have hca : c = a := (huniq c hac.symm).trans (huniq a rfl).symm
    rw [hca]
    exact (root_commute_iff a b a d).mpr rfl
  · obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective 1 x
    have ha : a ≠ 0 := fun h => hx ((hsq1 a b).mpr h)
    classical
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 8 := by
      rw [Fintype.card_eq_nat_card, card_binaryGaloisField_three]
    obtain ⟨c₁, -, hc₁⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, a} : Finset K)) (t := Finset.univ)
      (by rw [Finset.card_univ, hcard]
          exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
    obtain ⟨c₂, -, hc₂⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, a, c₁, a + c₁} : Finset K)) (t := Finset.univ)
      (by rw [Finset.card_univ, hcard]
          exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₁ hc₂
    obtain ⟨hc₁0, hc₁a⟩ := hc₁
    obtain ⟨hc₂0, hc₂a, hc₂c, hc₂ac⟩ := hc₂
    have hnc : ∀ c d : K, c ≠ 0 → c ≠ a →
        suzukiCoverRootElement 1 a b * suzukiCoverRootElement 1 c d ≠
          suzukiCoverRootElement 1 c d * suzukiCoverRootElement 1 a b := fun c d hc0 hca h =>
      mul_tits_ne ha hc0 hca ((root_commute_iff a b c d).mp h)
    refine ⟨suzukiCoverRootElement 1 c₁ 0, suzukiCoverRootElement 1 c₂ 0, hnc _ _ hc₁0 hc₁a,
      hnc _ _ hc₂0 hc₂a, ?_⟩
    rw [suzukiCoverRootElement_mul 1 hm]
    refine hnc _ _ (fun h => hc₂c ?_) (fun h => hc₂ac ?_)
    · exact (CharTwo.add_eq_zero.mp h).symm
    · rw [← h, add_comm c₁ c₂, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem szEightSylowFacts_of_mulEquiv {L : Type*} [Group L] [Finite L]
    (e : L ≃* CFSG.Theory.Comparator.SzModel 1) (R : Sylow 2 L) :
    SzEightSylowFacts (R : Subgroup L) := by
  let e' : L ≃* SuzukiMatrixGroup 1 :=
    e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1))
  obtain ⟨θ⟩ : Nonempty ((R : Subgroup L) ≃* suzukiCoverRoot 1) :=
    nonempty_sylow_mulEquiv_of_mulEquiv e' R (suzukiCoverSylow 1 one_pos)
  exact szEightSylowFacts_suzukiCoverRoot.congr θ.symm

end CFSG.ProperTwoGeneratedCore.Lemma37
