module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open

theorem mem_sup_of_commute' {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem card_sup_of_commute' {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B) = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem zpow_eq_one_of_dvd_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) {j : ℤ}
    (h : (3 : ℤ) ∣ j) : g ^ j = 1 := by
  obtain ⟨m, rfl⟩ := h
  have : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hg]
  rw [zpow_mul, this, one_zpow]

theorem exists_elemAbelian_27_of_indep {G : Type*} [Group G] {a b c : G}
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (hind : ∀ i j k : ℤ, a ^ i * b ^ j * c ^ k = 1 →
      (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have hcard : ∀ g : G, g ^ 3 = 1 → g ≠ 1 → Nat.card (Subgroup.zpowers g) = 3 := fun g hg h1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hg h1
  have ha1 : a ≠ 1 := fun h => by
    have := (hind 1 0 0 (by simp [h])).1
    omega
  have hb1 : b ≠ 1 := fun h => by
    have := (hind 0 1 0 (by simp [h])).2.1
    omega
  have hc1 : c ≠ 1 := fun h => by
    have := (hind 0 0 1 (by simp [h])).2.2
    omega
  have hcomm_ab : ∀ m n : ℤ, a ^ m * b ^ n = b ^ n * a ^ m := fun m n =>
    (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  have hcomm_ac : ∀ m n : ℤ, a ^ m * c ^ n = c ^ n * a ^ m := fun m n =>
    (Commute.zpow_zpow (show Commute a c from hac) m n).eq
  have hcomm_bc : ∀ m n : ℤ, b ^ m * c ^ n = c ^ n * b ^ m := fun m n =>
    (Commute.zpow_zpow (show Commute b c from hbc) m n).eq
  have hBC : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hcomm_bc m n
  have hBCd : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hg.1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg.2
    have h1 : a ^ (0 : ℤ) * b ^ j * c ^ (-k) = 1 := by
      rw [zpow_zero, one_mul, hj, zpow_neg, ← hk, mul_inv_cancel]
    rw [← hj]
    exact zpow_eq_one_of_dvd_three hb (hind 0 j (-k) h1).2.1
  have hBCcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = 9 := by
    rw [card_sup_of_commute' hBC hBCd, hcard b hb hb1, hcard c hc hc1]
  have hA : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commute' hBC hy
    obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    calc a ^ m * (b ^ p * c ^ r) = (a ^ m * b ^ p) * c ^ r := by rw [mul_assoc]
      _ = (b ^ p * a ^ m) * c ^ r := by rw [hcomm_ab]
      _ = b ^ p * (a ^ m * c ^ r) := by rw [mul_assoc]
      _ = b ^ p * (c ^ r * a ^ m) := by rw [hcomm_ac]
      _ = b ^ p * c ^ r * a ^ m := by rw [mul_assoc]
  have hAd : Subgroup.zpowers a ⊓ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hg.1
    obtain ⟨u, hu, v, hv, huv⟩ := mem_sup_of_commute' hBC hg.2
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have h1 : a ^ i * b ^ (-j) * c ^ (-k) = 1 := by
      have e1 : a ^ i = b ^ j * c ^ k := hi.trans huv.symm
      have e2 : b ^ (-j) * c ^ (-k) = (b ^ j * c ^ k)⁻¹ := by
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact hcomm_bc (-j) (-k)
      rw [mul_assoc, e2, e1, mul_inv_cancel]
    rw [← hi]
    exact zpow_eq_one_of_dvd_three ha (hind i (-j) (-k) h1).1
  refine ⟨Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c), ?_, ?_⟩
  ·
    have hform : ∀ x ∈ Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c),
        ∃ i j k : ℤ, x = a ^ i * b ^ j * c ^ k := by
      intro x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup_of_commute' hA hx
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨v, hv, y, hy, rfl⟩ := mem_sup_of_commute' hBC hw
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ⟨i, j, k, by rw [mul_assoc]⟩
    have cAA : ∀ m n : ℤ, Commute (a ^ m) (a ^ n) := fun m n => (Commute.refl a).zpow_zpow m n
    have cBB : ∀ m n : ℤ, Commute (b ^ m) (b ^ n) := fun m n => (Commute.refl b).zpow_zpow m n
    have cCC : ∀ m n : ℤ, Commute (c ^ m) (c ^ n) := fun m n => (Commute.refl c).zpow_zpow m n
    have cAB : ∀ m n : ℤ, Commute (a ^ m) (b ^ n) := fun m n =>
      (show Commute a b from hab).zpow_zpow m n
    have cAC : ∀ m n : ℤ, Commute (a ^ m) (c ^ n) := fun m n =>
      (show Commute a c from hac).zpow_zpow m n
    have cBC : ∀ m n : ℤ, Commute (b ^ m) (c ^ n) := fun m n =>
      (show Commute b c from hbc).zpow_zpow m n
    have key : ∀ i j k i' j' k' : ℤ,
        Commute (a ^ i * b ^ j * c ^ k) (a ^ i' * b ^ j' * c ^ k') := by
      intro i j k i' j' k'
      have X1 : Commute (a ^ i * b ^ j * c ^ k) (a ^ i') :=
        ((cAA i i').mul_left (cAB i' j).symm).mul_left (cAC i' k).symm
      have X2 : Commute (a ^ i * b ^ j * c ^ k) (b ^ j') :=
        ((cAB i j').mul_left (cBB j j')).mul_left (cBC j' k).symm
      have X3 : Commute (a ^ i * b ^ j * c ^ k) (c ^ k') :=
        ((cAC i k').mul_left (cBC j k')).mul_left (cCC k k')
      exact (X1.mul_right X2).mul_right X3
    have hpow3 : ∀ (g : G), g ^ 3 = 1 → ∀ m : ℤ, (g ^ m) ^ 3 = 1 := fun g hg m => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, j, k, hx⟩ := hform x x.2
      obtain ⟨i', j', k', hy⟩ := hform y y.2
      show (x : G) * y = y * x
      rw [hx, hy]
      exact (key i j k i' j' k').eq
    · obtain ⟨i, j, k, rfl⟩ := hform x hx
      rw [((cAC i k).mul_left (cBC j k)).mul_pow, (cAB i j).mul_pow, hpow3 a ha, hpow3 b hb,
        hpow3 c hc, one_mul, one_mul]
  · calc Nat.card ↥(Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c))
        = Nat.card (Subgroup.zpowers a) *
            Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) :=
          card_sup_of_commute' hA hAd
      _ = 3 * 9 := by rw [hcard a ha ha1, hBCcard]
      _ = 27 := by norm_num

theorem exists_fixedPoint_perm_of_coprime {T : Type*} [Finite T] (f : Equiv.Perm T)
    (hf : f ^ 3 = 1) (hT : ¬ 3 ∣ Nat.card T) : ∃ t : T, f t = t := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers f) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hf, one_zpow]
  have hmod := hp.card_modEq_card_fixedPoints T
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) T) = 0 := by
    have : IsEmpty (MulAction.fixedPoints (Subgroup.zpowers f) T) := by
      refine ⟨fun ⟨t, ht⟩ => hcon t ?_⟩
      exact ht ⟨f, Subgroup.mem_zpowers f⟩
    exact Nat.card_of_isEmpty
  rw [hfix] at hmod
  exact hT ((Nat.modEq_zero_iff_dvd).1 hmod)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
