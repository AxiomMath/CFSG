module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78FinkelsteinBasic

public section

namespace CFSG.SeitzReduction.RankOne.Finkelstein

open CFSG.ComponentClassification.GMS78.Finkelstein

variable {U : Type} [Group U]

structure Hyp (U : Type) [Group U] (n : ℕ) (t y : MulAut U) : Prop where
  pgroup : IsPGroup 2 U
  two_le : 2 ≤ n
  sq : t ^ 2 = 1
  comm : t * y = y * t
  order : orderOf y = 2 ^ n - 1
  reg : ∀ a b : U, t a = a → t b = b → a ≠ 1 → b ≠ 1 →
    ∃! k : ℕ, k < 2 ^ n - 1 ∧ (y ^ k) a = b

namespace Hyp

variable {n : ℕ} {t y : MulAut U} (h : Hyp U n t y)
include h

theorem t_t (u : U) : t (t u) = u := by
  rw [← MulAut.mul_apply, (pow_two t).symm.trans h.sq, MulAut.one_apply]

theorem t_pow_y (k : ℕ) (u : U) : t ((y ^ k) u) = (y ^ k) (t u) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ((Commute.pow_right h.comm k) : _ = _)]

theorem t_y (u : U) : t (y u) = y (t u) := by
  simpa using h.t_pow_y 1 u

theorem three_le : 3 ≤ 2 ^ n - 1 := by
  have : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

theorem pow_mem_fix (k : ℕ) {a : U} (ha : a ∈ fixSubgroup t) : (y ^ k) a ∈ fixSubgroup t := by
  rw [mem_fixSubgroup, h.t_pow_y, ha]

theorem exists_pow_eq {a b : U} (ha : a ∈ fixSubgroup t) (hb : b ∈ fixSubgroup t) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ k, (y ^ k) a = b := by
  obtain ⟨k, ⟨-, hk⟩, -⟩ := h.reg a b ha hb ha1 hb1
  exact ⟨k, hk⟩

theorem pow_eq_one_of_fix {k : ℕ} {a : U} (ha : a ∈ fixSubgroup t) (ha1 : a ≠ 1)
    (hk : (y ^ k) a = a) : y ^ k = 1 := by
  have hpos : 0 < 2 ^ n - 1 := by have := h.three_le; omega
  obtain ⟨k₀, -, hu⟩ := h.reg a a ha ha ha1 ha1
  have h1 : 0 = k₀ := hu 0 ⟨hpos, by simp⟩
  have hmod : (y ^ (k % (2 ^ n - 1))) a = a := by rw [← h.order, pow_mod_orderOf, hk]
  have h2 : k % (2 ^ n - 1) = k₀ := hu _ ⟨Nat.mod_lt _ hpos, hmod⟩
  rw [← pow_mod_orderOf, h.order, h2, ← h1, pow_zero]

theorem nontrivial : Nontrivial U := by
  by_contra hU
  rw [not_nontrivial_iff_subsingleton] at hU
  have hy : y = 1 := MulEquiv.ext fun u => Subsingleton.elim _ _
  have h1 := h.order
  rw [hy, orderOf_one] at h1
  have := h.three_le
  omega

theorem two_dvd_natCard [Finite U] {H : Subgroup U} (hH : H ≠ ⊥) : 2 ∣ Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h.pgroup.to_subgroup H)
  have h1 : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hH
  rw [hm] at h1 ⊢
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h1
  exact dvd_pow_self 2 hm0

omit h in
theorem pow_mem_of_invariant {H : Subgroup U} (hyH : ∀ x ∈ H, y x ∈ H) (k : ℕ) {x : U}
    (hx : x ∈ H) : (y ^ k) x ∈ H := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact hyH _ ih

theorem fix_le_of_invariant [Finite U] {H : Subgroup U} (htH : ∀ x ∈ H, t x ∈ H)
    (hyH : ∀ x ∈ H, y x ∈ H) (hH : H ≠ ⊥) : fixSubgroup t ≤ H := by
  set f : H → H := fun x => ⟨t x, htH x x.2⟩ with hf
  have hinv : Function.Involutive f := fun x => Subtype.ext (h.t_t x)
  obtain ⟨⟨x, hx⟩, hx1, hfx⟩ := exists_ne_fixed_of_involutive hinv (h.two_dvd_natCard hH)
    (x₀ := 1) (Subtype.ext (map_one t))
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have htx : t x = x := congrArg Subtype.val hfx
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact one_mem H
  obtain ⟨k, rfl⟩ := h.exists_pow_eq htx ha hx1' ha1
  exact pow_mem_of_invariant hyH k hx

theorem exists_fix_ne_one [Finite U] : ∃ a ∈ fixSubgroup t, a ≠ 1 := by
  have := h.nontrivial
  have h2 : 2 ∣ Nat.card U := by
    have h1 := h.two_dvd_natCard (H := ⊤) top_ne_bot
    rwa [Subgroup.card_top] at h1
  obtain ⟨a, ha1, hta⟩ := exists_ne_fixed_of_involutive (f := t) h.t_t h2 (x₀ := 1) (map_one t)
  exact ⟨a, hta, ha1⟩

theorem fix_le_center [Finite U] : fixSubgroup t ≤ Subgroup.center U := by
  have := h.nontrivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt := h.pgroup.center_nontrivial
  refine h.fix_le_of_invariant (fun x hx => map_mem_center t hx) (fun x hx => map_mem_center y hx)
    ?_
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt

theorem mem_center_of_mem_fix [Finite U] {a : U} (ha : a ∈ fixSubgroup t) (g : U) :
    g * a = a * g :=
  Subgroup.mem_center_iff.mp (h.fix_le_center ha) g

theorem natCard_fix [Finite U] : Nat.card (fixSubgroup t) = 2 ^ n := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := h.exists_fix_ne_one
  set m := 2 ^ n - 1 with hm
  have hm1 : m + 1 = 2 ^ n := by
    have := Nat.one_le_two_pow (n := n)
    omega
  set g : Option (Fin m) → fixSubgroup t := fun o =>
    o.elim 1 fun k => ⟨(y ^ (k : ℕ)) a₀, h.pow_mem_fix k ha₀⟩ with hg
  have hne : ∀ k : ℕ, (y ^ k) a₀ ≠ 1 := fun k h1 => ha₀1 ((y ^ k).injective (h1.trans
    (map_one _).symm))
  have hinj : Function.Injective g := by
    rintro (_ | k) (_ | k') hkk
    · rfl
    · exact absurd (congrArg Subtype.val hkk).symm (hne k')
    · exact absurd (congrArg Subtype.val hkk) (hne k)
    · have hb := h.pow_mem_fix k ha₀
      obtain ⟨k₀, -, hu⟩ := h.reg a₀ _ ha₀ hb ha₀1 (hne k)
      have e1 := hu k ⟨k.2, rfl⟩
      have e2 := hu k' ⟨k'.2, (congrArg Subtype.val hkk).symm⟩
      exact congrArg some (Fin.ext (e1.trans e2.symm))
  have hsurj : Function.Surjective g := by
    rintro ⟨b, hb⟩
    by_cases hb1 : b = 1
    · exact ⟨none, Subtype.ext hb1.symm⟩
    obtain ⟨k, ⟨hk, hkb⟩, -⟩ := h.reg a₀ b ha₀ hb ha₀1 hb1
    exact ⟨some ⟨k, hk⟩, Subtype.ext hkb⟩
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_option, Fintype.card_fin, hm1]

theorem mul_self_eq_one_of_mem_fix [Finite U] {a : U} (ha : a ∈ fixSubgroup t) : a * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (fixSubgroup t) := by
    rw [h.natCard_fix]
    exact dvd_pow_self 2 (by have := h.two_le; omega)
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ha₁1 : (a₁ : U) ≠ 1 := by
    intro h1
    have : a₁ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ha₁
    exact absurd ha₁ (by norm_num)
  have ha₁2 : (a₁ : U) * a₁ = 1 := by
    have := pow_orderOf_eq_one a₁
    rw [ha₁, pow_two] at this
    exact congrArg Subtype.val this
  by_cases ha1 : a = 1
  · rw [ha1, mul_one]
  obtain ⟨k, rfl⟩ := h.exists_pow_eq a₁.2 ha ha₁1 ha1
  rw [← map_mul, ha₁2, map_one]

theorem exists_not_mem_psi_mem [Finite U] {N : Subgroup U} [hN : N.Normal]
    (htN : ∀ x ∈ N, t x ∈ N) (hNt : N ≠ ⊤) : ∃ u, u ∉ N ∧ psi t u ∈ N := by
  have hle : N ≤ N.comap t.toMonoidHom := fun a ha => htN a ha
  set tb := QuotientGroup.map _ _ t.toMonoidHom hle with htb
  have htb_mk : ∀ u : U, tb (u : U ⧸ N) = ((t u : U) : U ⧸ N) :=
    fun u => QuotientGroup.map_mk _ _ _ hle u
  have hinv : Function.Involutive tb := fun x => by
    induction x using QuotientGroup.induction_on with
    | H u => rw [htb_mk, htb_mk, h.t_t]
  have heven : 2 ∣ Nat.card (U ⧸ N) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h.pgroup
    have hdvd : Nat.card (U ⧸ N) ∣ 2 ^ m := hm ▸ Subgroup.card_quotient_dvd_card N
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_eq_one] at hj
      exact hNt hj
    rw [hj]
    exact dvd_pow_self 2 hj0
  obtain ⟨x, hx1, hx⟩ := exists_ne_fixed_of_involutive hinv heven (x₀ := 1) (map_one tb)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [htb_mk] at hx
  refine ⟨u, fun hu => hx1 ((QuotientGroup.eq_one_iff u).mpr hu), ?_⟩
  exact QuotientGroup.eq.mp hx.symm

end Hyp

end CFSG.SeitzReduction.RankOne.Finkelstein
