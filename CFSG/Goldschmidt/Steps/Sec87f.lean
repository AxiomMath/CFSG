module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.GroupTheory.SuzukiTwoGroups
import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2LayerSylow
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem card_le_eight {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (huniq : ∀ x y : X, orderOf x = 2 → orderOf y = 2 → x = y) (hexp : ∀ x : X, x ^ 4 = 1) :
    Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hz : ∃ z : X, orderOf z = 2
  · obtain ⟨z, hz⟩ := hz
    have hrank := CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution
      z hz fun x hx => huniq x z hx hz
    have hdvd : Monoid.exponent X ∣ 4 := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion X hX hrank with
      hcyc | ⟨e, he3, ⟨φ⟩⟩
    · rw [IsCyclic.exponent_eq_card] at hdvd
      exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
    · obtain ⟨f, rfl⟩ : ∃ f, e = f + 3 := ⟨e - 3, by omega⟩
      rw [Monoid.exponent_eq_of_mulEquiv φ, QuaternionGroup.exponent] at hdvd
      have hlcm : 2 ^ (f + 3 - 2) ≤ lcm (2 ^ (f + 3 - 2)) 2 :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (by simp [lcm_eq_zero_iff]))
          (dvd_lcm_left _ _)
      have h1 : 2 * lcm (2 ^ (f + 3 - 2)) 2 ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hf : f = 0 := by
        by_contra hf
        have : 2 ^ 2 ≤ 2 ^ (f + 3 - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hf
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
  · have : Subsingleton X := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact (Finite.one_lt_card_iff_nontrivial.mpr hns).ne' hk
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
      exact hz ⟨y, hy⟩
    rw [Nat.card_unique]
    norm_num

theorem higman_data (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hAD : A ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hC2 : ∀ u ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, u ^ 2 = 1 → u ∈ A)
    (hnab : ¬ IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G)) :
    (∀ y ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, y ^ 4 = 1) ∧
      (∀ z ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆,
        (∀ y ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, z * y = y * z) → z ∈ A) ∧
      (Nat.card (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) = 16 ∨
        Nat.card (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) = 64) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hD
  have hDS : D ≤ S := commutator_self_le _
  have hDp : IsPGroup 2 D := S.isPGroup'.to_le hDS
  have hSA := le_centralizer hset h4
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  obtain ⟨x, hxS, hxaA, hxa⟩ := exists_mem_normalizer_sylow hset h4 ha ha1
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := normalizer_le_normalizer hset hxS
  have hxC : x ∉ Subgroup.centralizer (A : Set G) := fun h => hxa (by
    have := conj_eq_of_mem_centralizer (Subgroup.inv_mem _ h) ha
    simpa using this)
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_commutator hxS
  set φ : MulAut D := D.normalizerMonoidHom ⟨x, hxD⟩ with hφ
  have hφapp : ∀ y : D, ((φ y : D) : G) = x * y * x⁻¹ := fun y => rfl
  have hinv : ∀ y : D, orderOf y = 2 → (y : G) ∈ A ∧ (y : G) ≠ 1 := fun y hy => by
    have h2 : (y : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    refine ⟨hC2 y y.2 h2, fun h1 => ?_⟩
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have htrans : ∀ y y' : D, orderOf y = 2 → orderOf y' = 2 →
      ∃ β ∈ Subgroup.zpowers φ, β y = y' := by
    intro y y' hy hy'
    obtain ⟨hyA, hy1⟩ := hinv y hy
    obtain ⟨hy'A, hy'1⟩ := hinv y' hy'
    obtain ⟨hne, hsq⟩ := conj_conj_eq_mul hset h4 hxA hxC hyA hy1
    rcases mem_four hset.elem h4 hyA (conj_mem hxA hyA) hy'A hy1 (conj_ne_one hy1)
      (Ne.symm hne) with h | h | h | h
    · exact absurd h hy'1
    · exact ⟨1, Subgroup.one_mem _, Subtype.ext (by rw [h]; rfl)⟩
    · exact ⟨φ, Subgroup.mem_zpowers φ, Subtype.ext (by rw [hφapp, h])⟩
    · refine ⟨φ * φ, Subgroup.mul_mem _ (Subgroup.mem_zpowers φ) (Subgroup.mem_zpowers φ),
        Subtype.ext ?_⟩
      rw [MulAut.mul_apply, hφapp, hφapp, h, hsq]
  have hab : (⟨a, hAD ha⟩ : D) ≠ ⟨x⁻¹ * a * x, hAD hxaA⟩ := fun h =>
    hxa (congrArg Subtype.val h).symm
  have hord : ∀ c ∈ A, c ≠ 1 → ∀ hc : c ∈ D, orderOf (⟨c, hc⟩ : D) = 2 := fun c hc hc1 hcD => by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hset.elem.2 c hc) hc1
  have hsuz : CFSG.GroupTheory.IsSuzukiTwoGroup D :=
    ⟨inferInstance, hDp, hnab, ⟨⟨a, hAD ha⟩, ⟨x⁻¹ * a * x, hAD hxaA⟩, hord a ha ha1 _,
      hord _ hxaA (by simpa using conj_ne_one (n := x⁻¹) ha1) _, hab⟩,
      Subgroup.zpowers φ, inferInstance, htrans⟩
  obtain ⟨hΩZ, -, -, -, n, -, hcardZ, hexpD, -, hcardD⟩ := hsuz.higman
  have hall : ∀ y : D, y ^ 2 = 1 → y ∈ Subgroup.center D := fun y hy => by
    have hyA : (y : G) ∈ A := hC2 y y.2 (by simpa using congrArg Subtype.val hy)
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact (Subgroup.mem_centralizer_iff.mp (hSA (hDS g.2)) _ hyA).symm
  have hZA : ∀ z ∈ D, (∀ y ∈ D, z * y = y * z) → z ∈ A := fun z hz hzc => by
    have hzZ : (⟨z, hz⟩ : D) ∈ Subgroup.center D :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm
    rw [← hΩZ, CFSG.GroupTheory.SuzukiTwoGroup.mem_omega₁_iff_of_forall hall] at hzZ
    exact hC2 z hz (by simpa using congrArg Subtype.val hzZ)
  refine ⟨fun y hy => ?_, hZA, ?_⟩
  · have := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : D)
    rw [hexpD] at this
    simpa using congrArg Subtype.val this
  · have hZeq : Subgroup.center D = A.subgroupOf D := by
      refine le_antisymm (fun (z : D) hz => Subgroup.mem_subgroupOf.mpr
        (hZA (z : G) z.2 fun y hy => ?_)) fun (z : D) hz =>
          hall z (Subtype.ext (by simpa using hset.elem.2 _ hz))
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm
    have hcard4 : Nat.card (Subgroup.center D) = 2 ^ 2 := by
      rw [hZeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, h4]
      norm_num
    have hn : n = 2 := Nat.pow_right_injective (le_refl 2) (hcardZ.symm.trans hcard4)
    subst hn
    rcases hcardD with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num

end CFSG.Goldschmidt.Sec8
