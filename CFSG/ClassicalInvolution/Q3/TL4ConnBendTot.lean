module

public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open Subgroup QuaternionGroup CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def TwoTot (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 ↥P → ∀ a ∈ P, ∀ b ∈ P, a ∈ zpowers b ∨ b ∈ zpowers a

theorem TwoTot.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (h : TwoTot X) :
    TwoTot X' := by
  intro P hP a ha b hb
  have hP' : IsPGroup 2 ↥(P.comap e.toMonoidHom) := hP.comap_of_injective _ e.injective
  have ha' : e.symm a ∈ P.comap e.toMonoidHom := by simpa using ha
  have hb' : e.symm b ∈ P.comap e.toMonoidHom := by simpa using hb
  rcases h _ hP' _ ha' _ hb' with h1 | h1
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    left
    exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg e hk⟩
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    right
    exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg e hk⟩

theorem mem_zpowers_or_of_isCyclic {P : Type*} [Group P] [Finite P] [IsCyclic P]
    (hP : IsPGroup 2 P) (a b : P) : a ∈ zpowers b ∨ b ∈ zpowers a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg a)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg b)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hord : orderOf g = 2 ^ m := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hm
  have hdi : i.gcd (orderOf g : ℤ) ∣ 2 ^ m := by
    have := Int.gcd_dvd_right i (orderOf g : ℤ)
    rw [hord] at this ⊢
    exact_mod_cast this
  have hdj : j.gcd (orderOf g : ℤ) ∣ 2 ^ m := by
    have := Int.gcd_dvd_right j (orderOf g : ℤ)
    rw [hord] at this ⊢
    exact_mod_cast this
  obtain ⟨u, -, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdi
  obtain ⟨w, -, hw⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdj
  rcases le_total u w with h | h
  · right
    refine (zpowers_le_zpowers_iff g j i).mpr ?_ (mem_zpowers _)
    rw [hu, hw]
    exact pow_dvd_pow 2 h
  · left
    refine (zpowers_le_zpowers_iff g i j).mpr ?_ (mem_zpowers _)
    rw [hu, hw]
    exact pow_dvd_pow 2 h

theorem TwoTot.of_forall_isCyclic {X : Type*} [Group X] [Finite X]
    (h : ∀ P : Subgroup X, IsPGroup 2 ↥P → IsCyclic ↥P) : TwoTot X := by
  intro P hP a ha b hb
  have := h P hP
  rcases mem_zpowers_or_of_isCyclic hP ⟨a, ha⟩ ⟨b, hb⟩ with h1 | h1
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    exact Or.inl (mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    exact Or.inr (mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)

theorem TwoTot.of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X] : TwoTot X :=
  TwoTot.of_forall_isCyclic fun _ _ => inferInstance

theorem TwoTot.of_odd {X : Type*} [Group X] [Finite X] (h : Odd (Nat.card X)) : TwoTot X := by
  intro P hP a ha b hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hd : 2 ^ m ∣ Nat.card X := hm ▸ card_subgroup_dvd_card P
  have hm0 : m = 0 := by
    by_contra h0
    have h2 : 2 ∣ Nat.card X := (dvd_pow_self 2 h0).trans hd
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hb1 : b = 1 := by
    have hP1 : P = ⊥ := (card_eq_one).mp (by rw [hm, hm0, pow_zero])
    rw [hP1] at hb
    exact hb
  left
  rw [hb1, zpowers_one_eq_bot]
  have hP1 : P = ⊥ := (card_eq_one).mp (by rw [hm, hm0, pow_zero])
  rw [hP1] at ha
  exact ha

theorem TwoTot.of_outPNice {X : Type*} [Group X] [Finite X]
    (h : RankThree.PartOne.OutStructure.OutPNice 2 X) : TwoTot (Outer X) := by
  obtain ⟨D, E, hID, hD, hE, -, hEE⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ γ : MulAut X, (γ : Outer X) ∈ (⊤ : Subgroup (Outer X)) →
      ∀ P : Subgroup (Outer X), IsPGroup 2 ↥P → (γ : Outer X) ∈ P →
        ∃ k : ℕ, γ ^ (2 ^ k) ∈ inner X := by
    intro γ _ P hP hγ
    obtain ⟨k, hk⟩ := hP ⟨_, hγ⟩
    refine ⟨k, ?_⟩
    have h1 : ((γ : Outer X)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  intro P hP a ha b hb
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨k, hk⟩ := h2 α trivial P hP ha
  obtain ⟨l, hl⟩ := h2 β trivial P hP hb
  have hαE := hE α ⟨k, hID hk⟩
  have hβE := hE β ⟨l, hID hl⟩
  rcases hEE α hαE β hβE ⟨k, hID hk⟩ ⟨l, hID hl⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have hmem : ((α * β ^ m : MulAut X) : Outer X) ∈ P := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      exact P.mul_mem ha (P.zpow_mem hb m)
    obtain ⟨j, hj⟩ := h2 _ trivial P hP hmem
    have hinn := hD _ hm j hj
    refine mem_zpowers_iff.mpr ⟨-m, ?_⟩
    have h1 : ((α * β ^ m : MulAut X) : Outer X) = 1 := (QuotientGroup.eq_one_iff _).mpr hinn
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  · right
    have hmem : ((β * α ^ m : MulAut X) : Outer X) ∈ P := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      exact P.mul_mem hb (P.zpow_mem ha m)
    obtain ⟨j, hj⟩ := h2 _ trivial P hP hmem
    have hinn := hD _ hm j hj
    refine mem_zpowers_iff.mpr ⟨-m, ?_⟩
    have h1 : ((β * α ^ m : MulAut X) : Outer X) = 1 := (QuotientGroup.eq_one_iff _).mpr hinn
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm

theorem zmod_facts {n : ℕ} (hn : 2 ≤ n) :
    (1 : ZMod (2 * n)) ≠ 0 ∧ (1 : ZMod (2 * n)) ≠ n ∧ (1 + n : ZMod (2 * n)) ≠ 0 ∧
      (1 + n : ZMod (2 * n)) ≠ n := by
  have key : ∀ x y : ℕ, x < 2 * n → y < 2 * n → x ≠ y → (x : ZMod (2 * n)) ≠ y := by
    intro x y hx hy hxy h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
    exact hxy h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using key 1 0 (by omega) (by omega) (by omega)
  · simpa using key 1 n (by omega) (by omega) (by omega)
  · simpa using key (1 + n) 0 (by omega) (by omega) (by omega)
  · simpa using key (1 + n) n (by omega) (by omega) (by omega)

theorem a_one_mul_ne {n : ℕ} (hn : 2 ≤ n) {w : QuaternionGroup n} (hw : w ∈ zpowers (xa 0)) :
    a 1 * w ≠ 1 ∧ a 1 * w ≠ a n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h10, h1n, h1n0, h1nn⟩ := zmod_facts hn
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rw [← zpow_mod_orderOf, orderOf_xa]
  have hk0 : (0 : ℤ) ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk0
  rw [hm, zpow_natCast]
  have hm4 : m < 4 := by omega
  interval_cases m
  · rw [pow_zero, mul_one, one_def]
    simp only [ne_eq, a.injEq]
    exact ⟨h10, h1n⟩
  · simp only [pow_one, a_mul_xa, one_def, ne_eq, reduceCtorEq, not_false_eq_true, and_self]
  · rw [xa_sq, a_mul_a, one_def]
    simp only [ne_eq, a.injEq]
    exact ⟨h1n0, h1nn⟩
  · rw [pow_succ, xa_sq, a_mul_xa, a_mul_xa, one_def]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self]

@[expose] def aSub (n : ℕ) : Subgroup (QuaternionGroup n) where
  carrier := {g | ∃ i, g = a i}
  one_mem' := ⟨0, one_def⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, a_mul_a i j⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, by rw [inv_eq_of_mul_eq_one_right (by rw [a_mul_a, add_neg_cancel, a_zero])]⟩

theorem xa_zero_mul_ne {n : ℕ} {w : QuaternionGroup n} (hw : w ∈ zpowers (a 1)) :
    xa 0 * w ≠ 1 ∧ xa 0 * w ≠ a n := by
  have hle : zpowers (a 1 : QuaternionGroup n) ≤ aSub n := zpowers_le.mpr ⟨1, rfl⟩
  obtain ⟨i, rfl⟩ := hle hw
  rw [xa_mul_a, one_def]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self]

end CFSG.ClassicalInvolution.Q3.TL4.Bend
