module

public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section SL2

variable {k : Type} [Field k]

theorem sl2_center_eq_bot [CharP k 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem sl2_isSimpleGroup [CharP k 2] (h4 : 4 ≤ Nat.card k) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : Matrix.SpecialLinearGroup (Fin 2) k ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot.symm)
  exact e.isSimpleGroup

theorem sl2_isPerfect (h4 : 4 ≤ Nat.card k) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem card_sl2 [Finite k] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card k with hq
  have hq1 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := k)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, _root_.sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

end SL2

section Node

variable {K : Type*} [Group K]

structure RankOneNode (D : UniversalRootDatum K) (i : Fin D.rank) (q : ℕ) : Prop where
  perfect : 4 ≤ q → ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i
  prime : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ q ^ 2 - 1 →
    ∃ x ∈ rankOne D.rootGroup i, orderOf x = p ∧ x ∉ Subgroup.center K

theorem le_card_of_card_eq {k : Type} [Field k] [Finite k] {q : ℕ}
    (hkq : Nat.card k = q ∨ Nat.card k = q ^ 2) : q ≤ Nat.card k := by
  rcases hkq with h | h
  · exact h.ge
  · rw [h]
    exact Nat.le_self_pow two_ne_zero q

theorem exists_orderOf_eq_sl2 {k : Type} [Field k] [Finite k] [CharP k 2] {q : ℕ} (hq : 2 ≤ q)
    (hkq : Nat.card k = q ∨ Nat.card k = q ^ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q ^ 2 - 1) :
    4 ≤ Nat.card k ∧ ∃ y : Matrix.SpecialLinearGroup (Fin 2) k, orderOf y = p := by
  have hqk := le_card_of_card_eq hkq
  have hq3 : 3 ≤ q := by
    by_contra h
    have hq2 : q = 2 := by omega
    subst hq2
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hk4 : 4 ≤ Nat.card k := by
    have : Fintype k := Fintype.ofFinite k
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := k) 2
    rw [Nat.card_eq_fintype_card, hm]
    have h3 : 3 ≤ 2 ^ (m : ℕ) := by
      have := hq3.trans hqk
      rwa [Nat.card_eq_fintype_card, hm] at this
    have hm1 : 2 ≤ (m : ℕ) := by
      by_contra hm1
      have : (m : ℕ) = 1 := by have := m.pos; omega
      rw [this] at h3
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm1
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [card_sl2]
    refine Dvd.dvd.mul_left ?_ _
    rcases hkq with h | h
    · rw [h]
      exact hpq
    · rw [h]
      refine hpq.trans ?_
      simpa using Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 2
  exact ⟨hk4, exists_prime_orderOf_dvd_card' p hdvd⟩

theorem rankOne_eq_range_of_sl2 {D : UniversalRootDatum K} {i : Fin D.rank} {k : Type}
    [Field k] {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c) :
    rankOne D.rootGroup i = ρ.range := by
  refine le_antisymm (rankOne_le_range_of_sl2 hx i hU hL) ?_
  rintro _ ⟨A, rfl⟩
  have hA := Sp.mem_closure_sl2 A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := k)) ∪ Set.range sl2Lower) ≤
      (rankOne D.rootGroup i).comap ρ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hU c]
      exact le_sup_left (a := D.rootGroup (Pi.single i 1))
        (((hx _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)).1 _).2 ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hL c]
      exact le_sup_right (b := D.rootGroup (-Pi.single i 1))
        (((hx _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
          ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i))).1 _).2 ⟨c, rfl⟩)
  exact hle hA

theorem rankOneNode_of_equiv_sl2 {D : UniversalRootDatum K} {i : Fin D.rank} {q : ℕ}
    (hq : 2 ≤ q) {k : Type} [Field k] [Finite k] [CharP k 2]
    (e : ↥(rankOne D.rootGroup i) ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (hkq : Nat.card k = q ∨ Nat.card k = q ^ 2) : RankOneNode D i q := by
  have hqk := le_card_of_card_eq hkq
  refine ⟨fun h4 => ?_, fun p hp hp5 hpq => ?_⟩
  · have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) := sl2_isPerfect (h4.trans hqk)
    have : Group.IsPerfect ↥(rankOne D.rootGroup i) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  · obtain ⟨-, y, hy⟩ := exists_orderOf_eq_sl2 hq hkq hp hp5 hpq
    refine ⟨(e.symm y : K), (e.symm y).2, ?_, fun hc => ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    · have hy1 : y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply e.symm.injective
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul]
        exact Subgroup.mem_center_iff.1 hc (e.symm z : K)
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hy1
      rw [hy1, orderOf_one] at hy
      exact hp.one_lt.ne hy

theorem rankOneNode_of_sl2 {D : UniversalRootDatum K} {i : Fin D.rank} {q : ℕ} (hq : 2 ≤ q)
    {k : Type} [Field k] [Finite k] [CharP k 2] {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c)
    (hkq : Nat.card k = q ∨ Nat.card k = q ^ 2) : RankOneNode D i q := by
  have hrange := rankOne_eq_range_of_sl2 hx hU hL
  have hqk := le_card_of_card_eq hkq
  refine ⟨fun h4 => ?_, fun p hp hp5 hpq => ?_⟩
  · rw [hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact (sl2_isPerfect (h4.trans hqk)).commutator_eq_top
  · obtain ⟨hk4, y, hy⟩ := exists_orderOf_eq_sl2 hq hkq hp hp5 hpq
    have hρ1 : ρ (sl2Upper (1 : k)) ≠ 1 := by
      rw [hU]
      intro h
      have h0 : x (Pi.single i 1) (0 : k) = 1 := by
        have := (hx _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)).2.1 0 0
        rw [add_zero] at this
        exact mul_left_cancel (a := x (Pi.single i 1) (0 : k)) (by rw [mul_one]; exact this.symm)
      exact one_ne_zero
        ((hx _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)).2.2
          (h.trans h0.symm))
    have := sl2_isSimpleGroup hk4
    have hker : ρ.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
      · exact h
      · exact absurd (by simpa using (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top (sl2Upper (1 : k))
          : sl2Upper (1 : k) ∈ ρ.ker))) hρ1
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
    refine ⟨ρ y, hrange ▸ ⟨y, rfl⟩, ?_, fun hc => ?_⟩
    · rw [orderOf_injective ρ hinj y, hy]
    · have hy1 : y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply hinj
        rw [map_mul, map_mul]
        exact (Subgroup.mem_center_iff.1 hc (ρ z))
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hy1
      rw [hy1, orderOf_one] at hy
      exact hp.one_lt.ne hy

end Node

end CFSG.AGLEmbedding.ParabPrime
