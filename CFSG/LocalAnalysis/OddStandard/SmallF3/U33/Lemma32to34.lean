module

public import CFSG.Open.Catalog
import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour
import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
import CFSG.GH74.Uniqueness.SU.SU1BgTwoMaxClass
import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

section Lemma32

variable {X : Type*}

section Group

variable [Group X]

@[expose] def fixedSubgroup (α : X →* X) : Subgroup X where
  carrier := {x | α x = x}
  one_mem' := map_one α
  mul_mem' {a b} ha hb := by
    change α a = a at ha
    change α b = b at hb
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change α a = a at ha
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[simp]
theorem mem_fixedSubgroup {α : X →* X} {x : X} : x ∈ fixedSubgroup α ↔ α x = x := Iff.rfl

end Group

section CommGroup

variable [CommGroup X]

@[expose] def betaHom (α : X →* X) : X →* X where
  toFun x := x⁻¹ * α x
  map_one' := by rw [inv_one, map_one, mul_one]
  map_mul' x y := by
    rw [map_mul, mul_inv_rev, mul_comm y⁻¹ x⁻¹]
    exact mul_mul_mul_comm _ _ _ _

@[simp]
theorem betaHom_apply (α : X →* X) (x : X) : betaHom α x = x⁻¹ * α x := rfl

end CommGroup

end Lemma32

theorem lemma33 {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T) (A : Subgroup T)
    (hA : Nat.card A = 4) (hC : Subgroup.centralizer (A : Set T) = A) :
    A = ⊤ ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ m))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (T ≃* CFSG.Open.SemidihedralGroup n)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty (T ≃* QuaternionGroup (2 ^ m))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hAT : A = ⊤
  · exact Or.inl hAT
  right
  have hAab : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hA]; norm_num)
  by_cases hcyc : IsCyclic A
  ·
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    rw [hA] at ha
    set x : T := (a : T) with hx
    have hxo : orderOf x = 4 := by rw [hx, Subgroup.orderOf_coe]; exact ha
    have hzp : Subgroup.zpowers x = A := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr a.2
      · rw [hA, Nat.card_zpowers, hxo]
    have hcent : Subgroup.centralizer ({x} : Set T) = A := by
      rw [← hC]
      conv_rhs => rw [← hzp, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hcard_cent : Nat.card (Subgroup.centralizer ({x} : Set T)) ≤ 2 ^ 2 := by
      rw [hcent, hA]; norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
    have h4 : 4 ∣ Nat.card T := hA ▸ Subgroup.card_subgroup_dvd_card A
    have hne4 : Nat.card T ≠ 4 := fun h => hAT (Subgroup.eq_top_of_card_eq A (by rw [hA, h]))
    have h8 : 8 ≤ Nat.card T := by
      by_contra hlt
      have hk3 : k < 3 := by
        by_contra hk3
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hk3)
        omega
      interval_cases k <;> omega
    rcases h8.eq_or_lt with h8eq | h8lt
    ·
      have hnc : ∃ a b : T, a * b ≠ b * a := by
        by_contra hall
        push Not at hall
        apply hAT
        rw [← hcent, eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hall g x
      rcases CFSG.ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight
          h8eq.symm hnc with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact Or.inl ⟨2, by norm_num, ⟨e⟩⟩
      · exact Or.inr (Or.inr ⟨1, le_rfl, ⟨e⟩⟩)
    ·
      let φ : Shrink.{0} T ≃* T := Shrink.mulEquiv
      haveI : Finite (Shrink.{0} T) := Finite.of_equiv T φ.symm.toEquiv
      have hP' : IsPGroup 2 (Shrink.{0} T) := hT.of_equiv φ.symm
      have hcard' : Nat.card (Shrink.{0} T) = Nat.card T := Nat.card_congr φ.toEquiv
      have hcb : Nat.card (Subgroup.centralizer ({φ.symm x} : Set (Shrink.{0} T))) ≤ 2 ^ 2 := by
        have h1 : (Subgroup.centralizer ({φ.symm x} : Set (Shrink.{0} T))).map φ.toMonoidHom ≤
            Subgroup.centralizer ({x} : Set T) := by
          have := Subgroup.map_centralizer_le_centralizer_image
            ({φ.symm x} : Set (Shrink.{0} T)) φ.toMonoidHom
          simpa [Set.image_singleton] using this
        calc Nat.card (Subgroup.centralizer ({φ.symm x} : Set (Shrink.{0} T)))
            = Nat.card ((Subgroup.centralizer ({φ.symm x} : Set (Shrink.{0} T))).map
                φ.toMonoidHom) := (Subgroup.card_map_of_injective φ.injective).symm
          _ ≤ Nat.card (Subgroup.centralizer ({x} : Set T)) := Subgroup.card_le_of_le h1
          _ ≤ 2 ^ 2 := hcard_cent
      obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.ig10_24 2 Nat.prime_two
        (Shrink.{0} T) hP' (by rw [hcard']; omega) (φ.symm x) hcb
      rcases CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape (Shrink.{0} T) hP'
          (by rw [hcard']; exact h8lt) m hm hγ with
        ⟨j, hj, ⟨e⟩⟩ | ⟨j, hj, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · exact Or.inl ⟨j, hj, ⟨φ.symm.trans e⟩⟩
      · exact Or.inr (Or.inr ⟨j, hj, ⟨φ.symm.trans e⟩⟩)
      · exact Or.inr (Or.inl ⟨n, hn, ⟨φ.symm.trans e⟩⟩)
  ·
    have hexp : ∀ v ∈ A, v ^ 2 = 1 := by
      intro v hv
      have hdvd : orderOf (⟨v, hv⟩ : A) ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = Nat.card A by rw [hA]; norm_num]
        exact orderOf_dvd_natCard _
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hk2 : k ≤ 1 := by
        by_contra hlt
        have hk2 : k = 2 := by omega
        subst hk2
        exact hcyc (isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨⟨v, hv⟩, by rw [hk', hA]; norm_num⟩)
      have h2 : orderOf (⟨v, hv⟩ : A) ∣ 2 := by
        rw [hk']
        interval_cases k <;> norm_num
      have := orderOf_dvd_iff_pow_eq_one.mp h2
      exact congrArg Subtype.val this
    rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hT A hAab hexp hA hC with
      ⟨n, hn, hD⟩ | ⟨n, hn, hS⟩
    · exact Or.inl ⟨n - 1, by omega, hD⟩
    · exact Or.inr (Or.inl ⟨n, hn, hS⟩)

end CFSG.OddStandard.SmallF3.HarrisU33
