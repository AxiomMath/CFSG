module

public import CFSG.LargeExtraspecial.AS35VFit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.OddInversion
open Setting (orderOf_eq_two_of_isTypeA' mem_normalizer_of_conj_le)

namespace AS35V

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem three_mul_ncard_add_one_le {ι : Set S.O} (W : S.O → Submodule (ZMod 2) S.Qt)
    (hdim : ∀ x ∈ ι, finrank (ZMod 2) (W x) = 2)
    (hdisj : ∀ x ∈ ι, ∀ y ∈ ι, x ≠ y → W x ⊓ W y = ⊥) :
    3 * ι.ncard + 1 ≤ 2 ^ finrank (ZMod 2) S.Qt := by
  classical
  have : Fintype S.Qt := Fintype.ofFinite _
  have hfin : ι.Finite := Set.toFinite ι
  let A : S.O → Finset S.Qt := fun x => Finset.univ.filter (fun v => v ∈ W x ∧ v ≠ 0)
  have hA : ∀ x ∈ ι, (A x).card = 3 := by
    intro x hx
    have h4 : (Finset.univ.filter (fun v => v ∈ W x)).card = 4 := by
      rw [← Fintype.card_subtype]
      have : Fintype.card (W x) = 2 ^ 2 := by
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim x hx]
      simpa using this
    have e : A x = (Finset.univ.filter (fun v => v ∈ W x)).erase 0 := by
      ext v
      simp [A, and_comm]
    rw [e, Finset.card_erase_of_mem (by simp), h4]
  have hdisjA : (hfin.toFinset : Set S.O).PairwiseDisjoint A := by
    intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvx hvy
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hvx hvy
    have hb := hdisj x (hfin.mem_toFinset.mp hx) y (hfin.mem_toFinset.mp hy) hxy
    have : v ∈ W x ⊓ W y := ⟨hvx.1, hvy.1⟩
    rw [hb, Submodule.mem_bot] at this
    exact hvx.2 this
  have hsub : hfin.toFinset.biUnion A ⊆ Finset.univ.erase 0 := by
    intro v hv
    simp only [Finset.mem_biUnion, A, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨-, -, -, hv0⟩ := hv
    exact Finset.mem_erase.mpr ⟨hv0, Finset.mem_univ v⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisjA,
    Finset.sum_congr rfl (fun x hx => hA x (hfin.mem_toFinset.mp hx)), Finset.sum_const,
    smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at h1
  rw [Set.ncard_eq_toFinset_card ι hfin]
  have hpos : 0 < 2 ^ finrank (ZMod 2) S.Qt := Nat.pow_pos (by norm_num)
  omega

namespace PbarFacts

variable {τ : S.O} {P : Subgroup S.O}

theorem isTypeA_mul_of_inverted (h : PbarFacts S τ P) {j : S.O} (hodd : Odd (orderOf j))
    (hτj : τ * j * τ⁻¹ = j⁻¹) : IsTypeA S.q ((τ * j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  have hodd' : Odd (Nat.card (zpowers j)) := by rwa [Nat.card_zpowers]
  have hinv : ∀ x ∈ zpowers j, τ * x * τ⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, hτj, inv_zpow]
  obtain ⟨y, -, hy⟩ := OrthoF2.exists_mul_conj_eq_of_inverted h.mul_self hodd' hinv
    (mem_zpowers j)
  have e : τ * j = y⁻¹ * τ * y⁻¹⁻¹ := by
    rw [hy, ← mul_assoc, h.mul_self, one_mul]
  rw [e]
  have h1 := s12_isTypeA_conj h.typeA (y⁻¹).2
  simpa using h1

theorem fiveEleven_card (h : PbarFacts S τ P)
    (h58 : ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * τ = τ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hX3 : IsPGroup 3 X)
    (hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) (hτX : ∃ x ∈ X, τ * x ≠ x * τ) :
    Nat.card X = 27 ∧ ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a := by
  obtain ⟨hw, hC⟩ := h.fiveEleven h58 hXM hX3 hPX hτX
  have hodd := odd_card_of_isPGroup_three hX3
  have hτ2 : orderOf τ = 2 := orderOf_eq_two_of_isTypeA' h.typeA
  have hτN : τ ∈ normalizer (X : Set S.O) := mem_normalizer_of_conj_le (hPX τ h.mem)
    (hPX τ⁻¹ (P.inv_mem h.mem))
  have hτi : τ⁻¹ = τ := h.inv_eq
  have hoX : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hodd (X.orderOf_dvd_natCard hx)
  obtain ⟨x₀, hx₀, hx₀τ⟩ := hτX
  obtain ⟨c₀, -, hc₀τ, j₀, hj₀, hτj₀, rfl⟩ := exists_fixed_mul_inverted hτ2 hodd hτN hx₀
  have hj₀1 : j₀ ≠ 1 := by
    rintro rfl
    apply hx₀τ
    rw [mul_one]
    exact hc₀τ.symm
  have hnab : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    refine h.false_of_inverts (pow_three_of_inverted h.typeA (hoX j₀ hj₀) hτj₀) hj₀1
      (fun p hp => ?_) hτj₀
    exact h.mem_zpowers_of_commute hodd hj₀ (hPX p hp j₀ hj₀) hj₀1
      (hcon _ hj₀ _ (hPX p hp j₀ hj₀)) hτj₀ (h.conj_inverted hp hτj₀)
  refine ⟨?_, hnab⟩
  have hbij := fixed_mul_inverted_bijOn hodd hτ2 hτN
  have hXJ : Nat.card X = 3 * (invertedSet X τ).ncard := by
    have h2 := hbij.injOn.ncard_image
    rw [hbij.image_eq, Set.ncard_prod] at h2
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h2, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hC]
  have hJ : 3 * (invertedSet X τ).ncard + 1 ≤ 64 := by
    refine (three_mul_ncard_add_one_le (ι := invertedSet X τ)
      (fun j => commSpace ((τ * j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ?_ ?_).trans ?_
    · intro j hj
      exact (h.isTypeA_mul_of_inverted (hoX j hj.1) hj.2).2.2.2.1
    · intro j hj j' hj' hne
      have hA := h.isTypeA_mul_of_inverted (hoX j hj.1) hj.2
      have hA' := h.isTypeA_mul_of_inverted (hoX j' hj'.1) hj'.2
      have e : τ * j * (τ * j') = j⁻¹ * j' := by
        rw [← hj.2, hτi]
        group
      have hmem : j⁻¹ * j' ∈ X := X.mul_mem (X.inv_mem hj.1) hj'.1
      have h1 : j⁻¹ * j' ≠ 1 := fun e1 => hne (inv_mul_eq_one.mp e1)
      have h3 : orderOf (((τ * j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
          ((τ * j' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 3 := by
        have hmem37 := (aschbacher_3_7 S.q_nondegenerate hA hA').1
        rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, e] at hmem37 ⊢
        have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
        obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hX3) ⟨_, hmem⟩
        rw [Subgroup.orderOf_mk] at hm
        have hne1 : orderOf (j⁻¹ * j') ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem37
        rcases hmem37 with e1 | e1 | e1 | e1
        · exact absurd e1 hne1
        · rw [hm] at e1
          have : 2 ∣ 3 ^ m := by rw [e1]
          exact absurd ((Nat.prime_two.dvd_of_dvd_pow this)) (by norm_num)
        · exact e1
        · rw [hm] at e1
          have : 2 ∣ 3 ^ m := by rw [e1]; norm_num
          exact absurd ((Nat.prime_two.dvd_of_dvd_pow this)) (by norm_num)
      exact (commSpace_mul_of_orderOf_eq_three S.q_nondegenerate hA hA' h3).1
    · rw [S.finrank_Qt_eq_two_mul_width]
      calc 2 ^ (2 * S.width) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hX3.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    apply hab
    have e : (⟨a, ha⟩ : X) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      interval_cases k
      · exact mul_comm_of_card_le_three (by rw [hk]; norm_num) _ _
      · exact mul_comm_of_card_le_three (by rw [hk]; norm_num) _ _
      · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
        exact mul_comm' _ _
    exact congrArg Subtype.val e
  have hk4 : k ≤ 3 := by
    by_contra hk4
    push Not at hk4
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    omega
  rw [hk, le_antisymm hk4 hk3]
  norm_num

end PbarFacts

end AS35V

end CFSG.LargeExtraspecial
