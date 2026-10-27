module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.SeitzReduction

open Subgroup

section Group

variable {G : Type*} [Group G]

theorem inv_mul_mul_eq_mul_mul_conj {σ v : G} (hv : v * v = 1)
    (hc : Commute v (σ⁻¹ * v * σ)) : v⁻¹ * σ * v = σ * (v * (σ⁻¹ * v * σ)) := by
  rw [hc.eq, inv_eq_of_mul_eq_one_right hv]
  group

theorem conj_eq_mul_conj_of_commute {τ z : G} (hτ : τ * τ = 1) (hz : z * z = 1)
    (hc : Commute z (τ * z * τ)) : z⁻¹ * τ * z = τ * (z * (τ * z * τ)) := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have h := inv_mul_mul_eq_mul_mul_conj (σ := τ) hz (by rwa [hτinv])
  rwa [hτinv] at h

theorem isConj_mul_conj_of_commute {τ z : G} (hτ : τ * τ = 1) (hz : z * z = 1)
    (hc : Commute z (τ * z * τ)) : IsConj τ (τ * (z * (τ * z * τ))) :=
  isConj_iff.2 ⟨z⁻¹, by rw [inv_inv, conj_eq_mul_conj_of_commute hτ hz hc]⟩

theorem commute_of_forall_mul_self_eq_one {U : Subgroup G} (hU : ∀ u ∈ U, u * u = 1) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U) : Commute a b := by
  show a * b = b * a
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hU _ (U.mul_mem ha hb))).symm
    _ = b * a := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hU a ha), inv_eq_of_mul_eq_one_right (hU b hb)]

theorem inv_mul_mul_eq_of_exponent_two {U : Subgroup G} (hU : ∀ u ∈ U, u * u = 1) {σ : G}
    (hσ : σ ∈ normalizer (U : Set G)) {v : G} (hv : v ∈ U) :
    v⁻¹ * σ * v = σ * (v * (σ⁻¹ * v * σ)) :=
  inv_mul_mul_eq_mul_mul_conj (hU v hv)
    (commute_of_forall_mul_self_eq_one hU hv ((mem_normalizer_iff''.1 hσ v).1 hv))

theorem inv_mul_mul_eq_mul_mul_conj_of_involution {σ v : G} (hσ : σ * σ = 1) (hv : v * v = 1)
    (hc : Commute v (σ * v * σ⁻¹)) : v⁻¹ * σ * v = σ * (v * (σ * v * σ⁻¹)) := by
  rw [inv_eq_of_mul_eq_one_right hσ] at hc ⊢
  exact conj_eq_mul_conj_of_commute hσ hv hc

theorem inv_mul_mul_eq_of_exponent_two_of_involution {U : Subgroup G}
    (hU : ∀ u ∈ U, u * u = 1) {σ : G} (hσ : σ ∈ normalizer (U : Set G)) (hσσ : σ * σ = 1)
    {v : G} (hv : v ∈ U) : v⁻¹ * σ * v = σ * (v * (σ * v * σ⁻¹)) :=
  inv_mul_mul_eq_mul_mul_conj_of_involution hσσ (hU v hv)
    (commute_of_forall_mul_self_eq_one hU hv ((mem_normalizer_iff.1 hσ v).1 hv))

theorem isConj_mul_of_exponent_two {U : Subgroup G} (hU : ∀ u ∈ U, u * u = 1) {σ : G}
    (hσ : σ ∈ normalizer (U : Set G)) (hσσ : σ * σ = 1) {v : G} (hv : v ∈ U) :
    IsConj σ (σ * (v * (σ * v * σ⁻¹))) :=
  isConj_iff.2 ⟨v⁻¹, by rw [inv_inv, inv_mul_mul_eq_of_exponent_two_of_involution hU hσ hσσ hv]⟩

end Group

section Field

open Polynomial

theorem natCard_le_of_forall_pow_eq_self {K : Type*} [Field K] {q : ℕ} (hq : 1 < q) (S : Set K)
    (hS : ∀ x ∈ S, x ^ q = x) : Nat.card S ≤ q := by
  classical
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hsub : S ⊆ ((X ^ q - X : K[X]).roots.toFinset : Set K) := fun x hx => by
    simp [Polynomial.mem_roots hne, hS x hx]
  calc Nat.card S ≤ Nat.card ((X ^ q - X : K[X]).roots.toFinset : Set K) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (X ^ q - X : K[X]).roots.toFinset.card := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ Multiset.card (X ^ q - X : K[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : K[X]).natDegree := Polynomial.card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq

theorem pow_pow_eq_self_of_natCard_eq_sq {K : Type*} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (c : K) : (c ^ q) ^ q = c := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_add_pow_eq_of_pow_eq {K : Type*} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {d : K} (hd : d ^ 2 ^ f = d) :
    ∃ c : K, c + c ^ 2 ^ f = d := by
  set q := 2 ^ f
  have hq : 1 < q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    rw [hK] at h1
    by_contra h
    have h' : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hadd : ∀ a b : K, (a + b) ^ q = a ^ q + b ^ q := fun a b => add_pow_char_pow a b 2 f
  have hqq := pow_pow_eq_self_of_natCard_eq_sq hK
  let F : AddSubgroup K :=
    { carrier := {x | x ^ q = x}
      add_mem' := fun {a b} (ha : a ^ q = a) (hb : b ^ q = b) =>
        show (a + b) ^ q = a + b by rw [hadd, ha, hb]
      zero_mem' := show (0 : K) ^ q = 0 from zero_pow (by omega)
      neg_mem' := fun {a} (ha : a ^ q = a) => show (-a) ^ q = -a by rw [CharTwo.neg_eq, ha] }
  let T : K →+ F :=
    { toFun := fun c => ⟨c + c ^ q, show (c + c ^ q) ^ q = c + c ^ q by rw [hadd, hqq, add_comm]⟩
      map_zero' := Subtype.ext (show (0 : K) + 0 ^ q = 0 by rw [zero_pow (by omega), add_zero])
      map_add' := fun a b => Subtype.ext (show (a + b) + (a + b) ^ q = (a + a ^ q) + (b + b ^ q) by
        rw [hadd]; abel) }
  have hF : Nat.card F ≤ q := natCard_le_of_forall_pow_eq_self hq (F : Set K) fun _ hx => hx
  have hker : Nat.card T.ker ≤ q := natCard_le_of_forall_pow_eq_self hq (T.ker : Set K)
    fun x hx => (CharTwo.add_eq_zero.1 (congrArg Subtype.val (AddMonoidHom.mem_ker.1 hx))).symm
  have hsurj : Function.Surjective T := by
    refine AddMonoidHom.surjective_of_card_ker_le_div T (hker.trans ?_)
    rw [hK, Nat.le_div_iff_mul_le Nat.card_pos, sq]
    exact Nat.mul_le_mul_left q hF
  obtain ⟨c, hc⟩ := hsurj ⟨d, hd⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_add_pow_eq_of_pow_eq_galoisField {n : ℕ} (hn : n ≠ 0)
    {d : GaloisField 2 (2 * n)} (hd : d ^ 2 ^ n = d) :
    ∃ c : GaloisField 2 (2 * n), c + c ^ 2 ^ n = d :=
  exists_add_pow_eq_of_pow_eq (by rw [GaloisField.card 2 (2 * n) (by omega)]; ring) hd

variable {G K : Type*} [Group G] [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem isConj_mul_of_frobenius (hK : Nat.card K = (2 ^ f) ^ 2) {x : K → G}
    (hx : ∀ a b, x (a + b) = x a * x b) {σ : G} (hσ : ∀ c, σ * x c * σ⁻¹ = x (c ^ 2 ^ f))
    {d : K} (hd : d ^ 2 ^ f = d) : IsConj σ (σ * x d) := by
  obtain ⟨c, rfl⟩ := exists_add_pow_eq_of_pow_eq hK hd
  have hx0 : x 0 = 1 := (mul_eq_left (a := x 0)).1 (by rw [← hx, add_zero])
  have hxx : x c * x c = 1 := by rw [← hx, CharTwo.add_self_eq_zero, hx0]
  have hconj : σ⁻¹ * x c * σ = x (c ^ 2 ^ f) := by
    have h := hσ (c ^ 2 ^ f)
    rw [pow_pow_eq_self_of_natCard_eq_sq hK] at h
    rw [← h]
    group
  have hcomm : Commute (x c) (σ⁻¹ * x c * σ) := by
    rw [hconj]
    show x c * x (c ^ 2 ^ f) = x (c ^ 2 ^ f) * x c
    rw [← hx, ← hx, add_comm]
  have key := inv_mul_mul_eq_mul_mul_conj hxx hcomm
  rw [hconj, ← hx] at key
  exact isConj_iff.2 ⟨(x c)⁻¹, by rw [inv_inv, key]⟩

theorem isConj_mul_of_frobenius_of_commute (hK : Nat.card K = (2 ^ f) ^ 2) {x : K → G}
    (hx : ∀ a b, x (a + b) = x a * x b) (hinj : Function.Injective x) {σ : G}
    (hσ : ∀ c, σ * x c * σ⁻¹ = x (c ^ 2 ^ f)) {u : G} (hu : u ∈ Set.range x)
    (hσu : Commute σ u) : IsConj σ (σ * u) := by
  obtain ⟨d, rfl⟩ := hu
  refine isConj_mul_of_frobenius hK hx hσ (hinj ?_)
  rw [← hσ, hσu.eq, mul_inv_cancel_right]

end Field

end CFSG.SeitzReduction
