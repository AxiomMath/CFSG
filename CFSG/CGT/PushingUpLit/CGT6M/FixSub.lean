module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {V : Type} [Group V]

@[expose] def fixSub (x : MulAut V) : Subgroup V where
  carrier := {v | x v = v}
  one_mem' := map_one x
  mul_mem' := fun {a b} (ha : x a = a) (hb : x b = b) => by
    show x (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : x a = a) => by
    show x a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {x : MulAut V} {v : V} : v ∈ fixSub x ↔ x v = v := ⟨fun h => h, fun h => h⟩

theorem fixSub_one : fixSub (1 : MulAut V) = ⊤ := by
  ext v
  simp [mem_fixSub]

theorem card_fixSub_conj (g x : MulAut V) :
    Nat.card (fixSub (g * x * g⁻¹)) = Nat.card (fixSub x) :=
  Nat.card_congr
    { toFun := fun v => ⟨g⁻¹ v.1, by
        have h : g (x (g⁻¹ v.1)) = v.1 := v.2
        rw [mem_fixSub]
        apply g.injective
        rw [h]
        simp⟩
      invFun := fun v => ⟨g v.1, by
        have h : x v.1 = v.1 := v.2
        rw [mem_fixSub, MulAut.mul_apply, MulAut.mul_apply]
        simp [h]⟩
      left_inv := fun v => by ext; simp
      right_inv := fun v => by ext; simp }

theorem fixSub_le_pow (x : MulAut V) (n : ℕ) : fixSub x ≤ fixSub (x ^ n) := by
  intro v hv
  induction n with
  | zero => simp [mem_fixSub]
  | succ n ih =>
    rw [mem_fixSub] at hv ih ⊢
    rw [pow_succ', MulAut.mul_apply, ih, hv]

theorem pow_mod_five {M : Type*} [Monoid M] {x : M} (hx : x ^ 5 = 1) (n : ℕ) :
    x ^ (n % 5) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, hx, one_pow, mul_one]

theorem fixSub_pow_eq {x : MulAut V} (hx : x ^ 5 = 1) {k m : ℕ} (h : k * m % 5 = 1) :
    fixSub (x ^ k) = fixSub x := by
  refine le_antisymm ?_ (fixSub_le_pow x k)
  have h1 : (x ^ k) ^ m = x := by
    rw [← pow_mul, ← pow_mod_five hx, h, pow_one]
  have := fixSub_le_pow (x ^ k) m
  rwa [h1] at this

theorem exists_card_fixSub_five [Finite V] {d : ℕ} (hV : Nat.card V = 2 ^ d) {x : MulAut V}
    (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    ∃ e < d, Nat.card (fixSub x) = 2 ^ e ∧ 5 ∣ 2 ^ d - 2 ^ e := by
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hx hx1
  let K := Subgroup.zpowers x
  have hK : IsPGroup 5 K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hset : MulAction.fixedPoints K V = (fixSub x : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hv
      exact hv ⟨x, Subgroup.mem_zpowers x⟩
    · intro hv u
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
      change (u : MulAut V) v = v
      rw [← hk]
      have h2 : v ∈ MulAction.fixedBy V x := by
        rw [MulAction.mem_fixedBy]; exact hv
      have h3 := MulAction.mem_fixedBy_zpow h2 k
      rwa [MulAction.mem_fixedBy] at h3
  have hmod := hK.card_modEq_card_fixedPoints V
  rw [hset] at hmod
  change Nat.card V ≡ Nat.card (fixSub x) [MOD 5] at hmod
  obtain ⟨e, hed, hFe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hV ▸ Subgroup.card_subgroup_dvd_card (fixSub x))
  have hlt : e < d := by
    refine lt_of_le_of_ne hed fun hde => hx1 ?_
    have htop : fixSub x = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hFe, hV, hde])
    ext v
    have hv : v ∈ fixSub x := htop ▸ Subgroup.mem_top v
    exact hv
  refine ⟨e, hlt, hFe, ?_⟩
  rw [hFe, hV] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hlt.le)).mp hmod.symm

end CFSG.CGT.PushingUpLit.CGT6M
