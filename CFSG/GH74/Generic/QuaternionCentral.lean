module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Filter.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Generic

open CFSG.GH74.Filter CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

abbrev Qgen (j : ℕ) : Type := QuaternionGroup (2 ^ j)

@[expose] def Qgen.z (j : ℕ) : Qgen j := QuaternionGroup.a ((2 ^ j : ℕ) : ZMod (2 * 2 ^ j))

theorem Qgen.z_one : Qgen.z 1 = QuaternionGroup.a 2 := rfl

theorem Qgen.z_eq (j : ℕ) : Qgen.z j = QuaternionGroup.a (2 ^ j) := by
  unfold Qgen.z
  congr 1
  push_cast
  rfl

theorem Qgen.xa_sq (j : ℕ) (i : ZMod (2 * 2 ^ j)) :
    (QuaternionGroup.xa i : Qgen j) ^ 2 = Qgen.z j :=
  QuaternionGroup.xa_sq i

theorem Qgen.z_mul_self (j : ℕ) : Qgen.z j * Qgen.z j = 1 := by
  unfold Qgen.z
  rw [QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ← QuaternionGroup.a_zero]
  congr 1
  exact ZMod.natCast_self _

theorem Qgen.z_ne_one {j : ℕ} (_hj : 1 ≤ j) : Qgen.z j ≠ 1 := by
  unfold Qgen.z
  rw [← QuaternionGroup.a_zero]
  intro h
  have h1 := QuaternionGroup.a.inj h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : 0 < 2 ^ j := by positivity
  have := Nat.le_of_dvd h2 h1
  omega

theorem Qgen.orderOf_z {j : ℕ} (hj : 1 ≤ j) : orderOf (Qgen.z j) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Qgen.z_mul_self j) (Qgen.z_ne_one hj)

theorem Qgen.center_iff {j : ℕ} (hj : 1 ≤ j) (g : Qgen j) :
    g ∈ Subgroup.center (Qgen j) ↔ g = 1 ∨ g = Qgen.z j := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    rcases g with k | k
    · have h1 := h (QuaternionGroup.xa 0)
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub] at h1
      have h2 : k = -k := QuaternionGroup.xa.inj h1
      have h3 : ((2 * k.val : ℕ) : ZMod (2 * 2 ^ j)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat, two_mul k]
        nth_rewrite 1 [h2]
        exact neg_add_cancel k
      rw [ZMod.natCast_eq_zero_iff] at h3
      have h4 : 2 ^ j ∣ k.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
      obtain ⟨m, hm⟩ := h4
      have h5 : k.val < 2 * 2 ^ j := ZMod.val_lt k
      have h6 : m < 2 := by
        by_contra hm2
        have : 2 ^ j * 2 ≤ 2 ^ j * m := Nat.mul_le_mul_left _ (not_lt.1 hm2)
        omega
      interval_cases m
      · left
        have : k = 0 := by rw [← ZMod.val_eq_zero]; omega
        rw [this]
        exact QuaternionGroup.a_zero
      · right
        have : k = ((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) := by
          rw [← ZMod.natCast_zmod_val k, hm]; simp
        rw [this]
        rfl
    · exfalso
      have h1 := h (QuaternionGroup.a 1)
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
      have h2 : k - 1 = k + 1 := QuaternionGroup.xa.inj h1
      have h3 : ((2 : ℕ) : ZMod (2 * 2 ^ j)) = 0 := by
        have : (k + 1) - (k - 1) = 0 := by rw [h2]; exact sub_self _
        rw [show (k + 1) - (k - 1) = 2 by ring] at this
        exact_mod_cast this
      rw [ZMod.natCast_eq_zero_iff] at h3
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
  · rintro (rfl | rfl)
    · intro x
      rw [mul_one, one_mul]
    · intro x
      rcases x with i | i
      · rw [Qgen.z]
        rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
      · rw [Qgen.z]
        rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
        congr 1
        have hn : ((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) + ((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) = 0 := by
          rw [← Nat.cast_add, ← two_mul]
          exact ZMod.natCast_self _
        rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right hn]

private def q8Exp (k : ℕ) : ZMod (2 * 2) →+ ZMod (2 * 2 ^ (k + 1)) :=
  ZMod.lift (2 * 2) ⟨(AddMonoidHom.mulLeft ((2 ^ k : ℕ) : ZMod (2 * 2 ^ (k + 1)))).comp
    (Int.castAddHom _), by
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, Int.coe_castAddHom,
      Int.cast_natCast]
    rw [← Nat.cast_mul]
    have : 2 ^ k * (2 * 2) = 2 * 2 ^ (k + 1) := by ring
    rw [this]
    exact ZMod.natCast_self _⟩

private theorem q8Exp_injective (k : ℕ) : Function.Injective (q8Exp k) := by
  unfold q8Exp
  rw [ZMod.lift_injective]
  intro m hm
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, Int.coe_castAddHom] at hm
  rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : ((2 * 2 ^ (k + 1) : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) * ((2 * 2 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h2] at hm
  exact (mul_dvd_mul_iff_left (Nat.cast_ne_zero.2 (pow_ne_zero k (by norm_num)))).1 hm

private theorem q8Exp_natCast_two (k : ℕ) :
    q8Exp k ((2 : ℕ) : ZMod (2 * 2)) = ((2 ^ (k + 1) : ℕ) : ZMod (2 * 2 ^ (k + 1))) := by
  have : ((2 : ℕ) : ZMod (2 * 2)) = (((2 : ℕ) : ℤ) : ZMod (2 * 2)) := by simp
  rw [this]
  simp only [q8Exp, ZMod.lift_coe]
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, Int.coe_castAddHom,
    Int.cast_natCast]
  rw [← Nat.cast_mul]
  congr 1

private def q8ToQgen (k : ℕ) : Q8 →* Qgen (k + 1) where
  toFun
    | .a i => .a (q8Exp k i)
    | .xa i => .xa (q8Exp k i)
  map_one' := by
    show QuaternionGroup.a (q8Exp k 0) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (l | l)
    · show QuaternionGroup.a (q8Exp k (i + l)) = _
      rw [map_add]
      rfl
    · show QuaternionGroup.xa (q8Exp k (l - i)) = _
      rw [map_sub]
      rfl
    · show QuaternionGroup.xa (q8Exp k (i + l)) = _
      rw [map_add]
      rfl
    · show QuaternionGroup.a (q8Exp k (((2 : ℕ) : ZMod (2 * 2)) + l - i)) = _
      rw [map_sub, map_add, q8Exp_natCast_two]
      rfl

private theorem q8ToQgen_injective (k : ℕ) : Function.Injective (q8ToQgen k) := by
  rintro (i | i) (l | l) h
  · have := QuaternionGroup.a.inj h
    rw [q8Exp_injective k this]
  · cases h
  · cases h
  · have := QuaternionGroup.xa.inj h
    rw [q8Exp_injective k this]

private theorem q8ToQgen_a_two (k : ℕ) :
    q8ToQgen k (QuaternionGroup.a 2) = Qgen.z (k + 1) := by
  show QuaternionGroup.a (q8Exp k 2) = _
  have : (2 : ZMod (2 * 2)) = ((2 : ℕ) : ZMod (2 * 2)) := by simp
  rw [this, q8Exp_natCast_two]
  rfl

theorem exists_q8_embedding {j : ℕ} (hj : 1 ≤ j) :
    ∃ ι : Q8 →* Qgen j, Function.Injective ι ∧ ι (QuaternionGroup.a 2) = Qgen.z j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact ⟨q8ToQgen k, q8ToQgen_injective k, q8ToQgen_a_two k⟩

@[expose] def qgenParity (j : ℕ) : ZMod (2 * 2 ^ j) →+* ZMod 2 :=
  ZMod.castHom (dvd_mul_right 2 _) (ZMod 2)

private theorem qgenParity_natCast_pow {j : ℕ} (hj : 1 ≤ j) :
    qgenParity j ((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) = 0 := by
  rw [qgenParity, map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_pow_self 2 (by omega)

private theorem qgenParity_sub (j : ℕ) (k i : ZMod (2 * 2 ^ j)) :
    qgenParity j (k - i) = qgenParity j i + qgenParity j k := by
  rw [map_sub]
  exact (by decide : ∀ x y : ZMod 2, x - y = y + x) _ _

private theorem qgenParity_natCast_pow_add_sub {j : ℕ} (hj : 1 ≤ j) (k i : ZMod (2 * 2 ^ j)) :
    qgenParity j (((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) + k - i) =
      qgenParity j i + qgenParity j k := by
  rw [map_sub, map_add, qgenParity_natCast_pow hj]
  exact (by decide : ∀ x y : ZMod 2, 0 + x - y = y + x) _ _

@[expose] def qgenFrattini (j : ℕ) (hj : 1 ≤ j) : Qgen j →* V4 where
  toFun
    | .a i => Multiplicative.ofAdd (qgenParity j i, (0 : ZMod 2))
    | .xa i => Multiplicative.ofAdd (qgenParity j i, (1 : ZMod 2))
  map_one' := by
    show Multiplicative.ofAdd (qgenParity j 0, (0 : ZMod 2)) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (k | k)
    · show Multiplicative.ofAdd (qgenParity j (i + k), (0 : ZMod 2)) = _
      rw [map_add]
      rfl
    · show Multiplicative.ofAdd (qgenParity j (k - i), (1 : ZMod 2)) = _
      rw [qgenParity_sub]
      rfl
    · show Multiplicative.ofAdd (qgenParity j (i + k), (1 : ZMod 2)) = _
      rw [map_add]
      rfl
    · show Multiplicative.ofAdd (qgenParity j (((2 ^ j : ℕ) : ZMod (2 * 2 ^ j)) + k - i),
        (0 : ZMod 2)) = _
      rw [qgenParity_natCast_pow_add_sub hj]
      show _ = Multiplicative.ofAdd (qgenParity j i + qgenParity j k, (1 : ZMod 2) + 1)
      rw [(by decide : (1 : ZMod 2) + 1 = 0)]

theorem qgenFrattini_a {j : ℕ} (hj : 1 ≤ j) (i : ZMod (2 * 2 ^ j)) :
    qgenFrattini j hj (QuaternionGroup.a i) =
      Multiplicative.ofAdd (qgenParity j i, (0 : ZMod 2)) :=
  rfl

theorem qgenFrattini_xa {j : ℕ} (hj : 1 ≤ j) (i : ZMod (2 * 2 ^ j)) :
    qgenFrattini j hj (QuaternionGroup.xa i) =
      Multiplicative.ofAdd (qgenParity j i, (1 : ZMod 2)) :=
  rfl

theorem qgenFrattini_surjective {j : ℕ} (hj : 1 ≤ j) :
    Function.Surjective (qgenFrattini j hj) := by
  rintro ⟨u, w⟩
  have hw : w = 0 ∨ w = 1 := by revert w; decide
  have hu : ∃ i : ZMod (2 * 2 ^ j), qgenParity j i = u :=
    ⟨(u.val : ZMod (2 * 2 ^ j)), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
  obtain ⟨i, hi⟩ := hu
  rcases hw with rfl | rfl
  · exact ⟨QuaternionGroup.a i, by rw [qgenFrattini_a, hi]; rfl⟩
  · exact ⟨QuaternionGroup.xa i, by rw [qgenFrattini_xa, hi]; rfl⟩

theorem qgenFrattini_z {j : ℕ} (hj : 1 ≤ j) : qgenFrattini j hj (Qgen.z j) = 1 := by
  rw [Qgen.z, qgenFrattini_a, qgenParity_natCast_pow hj]
  rfl

theorem qgenFrattini_eq_one_iff {j : ℕ} (hj : 1 ≤ j) (g : Qgen j) :
    qgenFrattini j hj g = 1 ↔
      ∃ i : ZMod (2 * 2 ^ j), g = QuaternionGroup.a i ∧ qgenParity j i = 0 := by
  rcases g with i | i
  · rw [qgenFrattini_a]
    constructor
    · intro h
      refine ⟨i, rfl, ?_⟩
      exact congrArg (fun v : V4 => (Multiplicative.toAdd v).1) h
    · rintro ⟨i', hi', hp⟩
      cases hi'
      rw [hp]
      rfl
  · rw [qgenFrattini_xa]
    constructor
    · intro h
      have h1 : (1 : ZMod 2) = 0 := congrArg (fun v : V4 => (Multiplicative.toAdd v).2) h
      exact absurd h1 (by decide)
    · rintro ⟨i', hi', -⟩
      cases hi'

theorem qgenFrattini_one_eq_one_iff (g : Qgen 1) :
    qgenFrattini 1 le_rfl g = 1 ↔ g = 1 ∨ g = Qgen.z 1 := by
  rw [qgenFrattini_eq_one_iff]
  have key : ∀ i : ZMod (2 * 2 ^ 1), qgenParity 1 i = 0 →
      i = 0 ∨ i = ((2 ^ 1 : ℕ) : ZMod (2 * 2 ^ 1)) := by
    decide
  constructor
  · rintro ⟨i, rfl, hi⟩
    rcases key i hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl, map_zero _⟩
    · exact ⟨_, rfl, qgenParity_natCast_pow le_rfl⟩

theorem qgenFrattini_one : qgenFrattini 1 le_rfl = q8Frattini := by
  refine MonoidHom.ext fun g => ?_
  rcases g with i | i
  · show Multiplicative.ofAdd (qgenParity 1 i, (0 : ZMod 2)) =
      Multiplicative.ofAdd ((i.val : ZMod 2), (0 : ZMod 2))
    rw [qgenParity, ZMod.castHom_apply, ZMod.cast_eq_val]
  · show Multiplicative.ofAdd (qgenParity 1 i, (1 : ZMod 2)) =
      Multiplicative.ofAdd ((i.val : ZMod 2), (1 : ZMod 2))
    rw [qgenParity, ZMod.castHom_apply, ZMod.cast_eq_val]

section Counting

variable {C : Type*} [Group C]

private theorem q8_a_two_ne_one : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide

private theorem q8Frattini_a_two_aux : q8Frattini (QuaternionGroup.a 2) = 1 := by decide

private theorem q8Frattini_eq_one_of_central_aux (g : Q8) (hg : ∀ x, g * x = x * g) :
    q8Frattini g = 1 := by
  rcases quaternion_center g hg with rfl | rfl
  · exact map_one _
  · exact q8Frattini_a_two_aux

private theorem V4_sq_aux : ∀ a : V4, a ^ 2 = 1 := by decide

theorem q8q8_central_of_commute {φ : Q8 × Q8 →* C}
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2))
    {g : Q8 × Q8} (hg : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a) :
    (∀ x : Q8, g.1 * x = x * g.1) ∧ (∀ x : Q8, g.2 * x = x * g.2) := by
  constructor
  · intro x
    have h1 : φ ((x, 1) * g * (g * (x, 1))⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hg (x, 1)]
      exact mul_inv_cancel _
    rcases hφ _ h1 with h | h
    · have h2 : x * g.1 * (g.1 * x)⁻¹ = 1 := congrArg Prod.fst h
      exact (mul_inv_eq_one.1 h2).symm
    · have h2 := congrArg Prod.snd h
      simp at h2
      exact absurd h2.symm q8_a_two_ne_one
  · intro x
    have h1 : φ ((1, x) * g * (g * (1, x))⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hg (1, x)]
      exact mul_inv_cancel _
    rcases hφ _ h1 with h | h
    · have h2 : x * g.2 * (g.2 * x)⁻¹ = 1 := congrArg Prod.snd h
      exact (mul_inv_eq_one.1 h2).symm
    · have h2 := congrArg Prod.fst h
      simp at h2
      exact absurd h2.symm q8_a_two_ne_one

theorem q8q8_commuting_two_subgroup_le_range' [Finite C] (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2))
    (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) : T ≤ φ.range := by
  by_contra hnot
  set M : Subgroup T := φ.range.subgroupOf T with hM
  have hMc : ∀ t ∈ M, ∀ s : T, s * t = t * s := by
    intro t ht s
    obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.1 ht)
    apply Subtype.ext
    change (s : C) * (t : C) = (t : C) * (s : C)
    rw [← ha]
    exact (hcomm a s s.2).symm
  have hMn : M.Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hMc n hn g
      rw [this]
      exact hn⟩
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply hnot
    intro t ht
    have : (⟨t, ht⟩ : T) ∈ M := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hQ : IsPGroup 2 (T ⧸ M) := hT.to_quotient M
  have hnil : Group.IsNilpotent (T ⧸ M) := hQ.isNilpotent
  have hdvd : 2 ∣ Nat.card (T ⧸ M) := by
    rcases hQ.card_eq_or_dvd with h | h
    · exfalso
      apply hMtop
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact h
    · exact h
  obtain ⟨H, hHidx, hHn⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := T ⧸ M) (k := 2) hdvd
  have _ := hHn
  have hEcard : Nat.card ((T ⧸ M) ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hHidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcyc : IsCyclic ((T ⧸ M) ⧸ H) := isCyclic_of_prime_card hEcard
  let _ : CommGroup ((T ⧸ M) ⧸ H) := IsCyclic.commGroup
  have hEsq : ∀ e : (T ⧸ M) ⧸ H, e ^ 2 = 1 := fun e => by
    rw [← hEcard]; exact pow_card_eq_one'
  let τ : T →* (T ⧸ M) ⧸ H := (QuotientGroup.mk' H).comp (QuotientGroup.mk' M)
  have hτ : Function.Surjective τ :=
    (QuotientGroup.mk'_surjective H).comp (QuotientGroup.mk'_surjective M)
  let α : (Q8 × Q8) × T →* C :=
    MonoidHom.noncommCoprod φ T.subtype (fun a t => (hcomm a t t.2 : _))
  let β : (Q8 × Q8) × T →* (V4 × V4) × ((T ⧸ M) ⧸ H) :=
    (q8Frattini.prodMap q8Frattini).prodMap τ
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap hτ
  refine not_gen4_of_surjection α β hβ ?_ ?_ ?_ ?_ hC
  · intro a b
    exact Prod.ext (Prod.ext (mul_comm _ _) (mul_comm _ _)) (mul_comm _ _)
  · intro a
    exact Prod.ext (Prod.ext (V4_sq_aux _) (V4_sq_aux _)) (hEsq _)
  · rw [Nat.card_prod, Nat.card_prod, card_V4, hEcard]
    norm_num
  · rintro ⟨g, t⟩ hgt
    rw [MonoidHom.mem_ker] at hgt ⊢
    have h1 : φ g * (t : C) = 1 := hgt
    have htg : (t : C) = (φ g)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have htM : t ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf, htg]
      exact φ.range.inv_mem ⟨g, rfl⟩
    have hcent : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a := by
      intro a
      have hgT : φ g ∈ T := by
        have : (φ g) = ((t : C))⁻¹ := by rw [htg, inv_inv]
        rw [this]
        exact T.inv_mem t.2
      exact hcomm a (φ g) hgT
    obtain ⟨hg1, hg2⟩ := q8q8_central_of_commute hφ hcent
    change ((q8Frattini g.1, q8Frattini g.2), τ t) = 1
    refine Prod.ext (Prod.ext (q8Frattini_eq_one_of_central_aux _ hg1)
      (q8Frattini_eq_one_of_central_aux _ hg2)) ?_
    change τ t = 1
    have : (QuotientGroup.mk' M) t = 1 := (QuotientGroup.eq_one_iff t).2 htM
    change (QuotientGroup.mk' H) ((QuotientGroup.mk' M) t) = 1
    rw [this, map_one]

theorem q8q8_commuting_two_subgroup_le' [Finite C] (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2))
    (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) :
    ∀ t ∈ T, ∃ g : Q8 × Q8, φ g = t ∧ ∀ a : Q8 × Q8, g * a = a * g := by
  intro t ht
  obtain ⟨g, hg⟩ := q8q8_commuting_two_subgroup_le_range' hC φ hφ T hT hcomm ht
  obtain ⟨hg1, hg2⟩ := q8q8_central_of_commute hφ (g := g) fun a => by
    rw [hg]
    exact hcomm a t ht
  exact ⟨g, hg, fun a => Prod.ext (hg1 a.1) (hg2 a.2)⟩

end Counting

section Rank

variable {C : Type*} [Group C]

theorem qq_commuting_two_subgroup_le_center [Finite C] (hC : Gen4 C) {j : ℕ} (hj : 1 ≤ j)
    (φ : Qgen j × Qgen j →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j))
    (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Qgen j × Qgen j) (t : C), t ∈ T → φ a * t = t * φ a) :
    ∀ t ∈ T, ∃ g : Qgen j × Qgen j, φ g = t ∧ (g.1 = 1 ∨ g.1 = Qgen.z j) ∧
      (g.2 = 1 ∨ g.2 = Qgen.z j) := by
  obtain ⟨ι, hι, hιz⟩ := exists_q8_embedding hj
  let ψ : Q8 × Q8 →* C := φ.comp (ι.prodMap ι)
  have hψ : ∀ g, ψ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
    intro g hg
    rcases hφ ((ι.prodMap ι) g) hg with h | h
    · left
      have h1 : ι g.1 = ι 1 := by rw [map_one]; exact congrArg Prod.fst h
      have h2 : ι g.2 = ι 1 := by rw [map_one]; exact congrArg Prod.snd h
      exact Prod.ext (hι h1) (hι h2)
    · right
      have h1 : ι g.1 = ι (QuaternionGroup.a 2) := by rw [hιz]; exact congrArg Prod.fst h
      have h2 : ι g.2 = ι (QuaternionGroup.a 2) := by rw [hιz]; exact congrArg Prod.snd h
      exact Prod.ext (hι h1) (hι h2)
  intro t ht
  obtain ⟨g, hg, hgc⟩ :=
    q8q8_commuting_two_subgroup_le' hC ψ hψ T hT (fun a t ht => hcomm _ t ht) t ht
  have h1 : g.1 = 1 ∨ g.1 = QuaternionGroup.a 2 := quaternion_center g.1 (fun x => by
    have := congrArg Prod.fst (hgc (x, 1))
    simpa using this)
  have h2 : g.2 = 1 ∨ g.2 = QuaternionGroup.a 2 := quaternion_center g.2 (fun x => by
    have := congrArg Prod.snd (hgc (1, x))
    simpa using this)
  refine ⟨(ι g.1, ι g.2), hg, ?_, ?_⟩
  · rcases h1 with h | h
    · left
      show ι g.1 = 1
      rw [h, map_one]
    · right
      show ι g.1 = Qgen.z j
      rw [h, hιz]
  · rcases h2 with h | h
    · left
      show ι g.2 = 1
      rw [h, map_one]
    · right
      show ι g.2 = Qgen.z j
      rw [h, hιz]

theorem qq_commuting_two_subgroup_le_range [Finite C] (hC : Gen4 C) {j : ℕ} (hj : 1 ≤ j)
    (φ : Qgen j × Qgen j →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j))
    (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Qgen j × Qgen j) (t : C), t ∈ T → φ a * t = t * φ a) :
    T ≤ (Subgroup.center (Qgen j × Qgen j)).map φ := by
  intro t ht
  obtain ⟨g, hg, h1, h2⟩ := qq_commuting_two_subgroup_le_center hC hj φ hφ T hT hcomm t ht
  refine ⟨g, Subgroup.mem_center_iff.2 fun a => ?_, hg⟩
  exact Prod.ext (Subgroup.mem_center_iff.1 ((Qgen.center_iff hj g.1).2 h1) a.1)
    (Subgroup.mem_center_iff.1 ((Qgen.center_iff hj g.2).2 h2) a.2)

theorem rankCertified_of_qq {j : ℕ} (hj : 1 ≤ j) (φ : Qgen j × Qgen j →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j)) : RankCertified C 3 := by
  let β : Qgen j × Qgen j →* V4 × V4 := (qgenFrattini j hj).prodMap (qgenFrattini j hj)
  have hβ : Function.Surjective β :=
    (qgenFrattini_surjective hj).prodMap (qgenFrattini_surjective hj)
  have hker : (QuotientGroup.mk' φ.ker).ker ≤ β.ker := by
    rw [QuotientGroup.ker_mk']
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rcases hφ k hk with rfl | rfl
    · exact map_one _
    · exact Prod.ext (qgenFrattini_z hj) (qgenFrattini_z hj)
  have h : ¬ SectionalTwoRankLE ((Qgen j × Qgen j) ⧸ φ.ker) 3 :=
    not_sectionalTwoRankLE_of_surjection 3 (QuotientGroup.mk' φ.ker) β hβ
      (fun a b => Prod.ext (mul_comm _ _) (mul_comm _ _))
      (fun a => Prod.ext (V4_sq_aux _) (V4_sq_aux _))
      (by rw [Nat.card_prod, card_V4]; norm_num) hker
  exact (rankCertified_of_not_sectionalTwoRankLE h).of_injective (QuotientGroup.kerLift φ)
    (QuotientGroup.kerLift_injective φ)

theorem rankCertified_of_q8q8 (φ : Q8 × Q8 →* C)
    (hφ : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2)) :
    RankCertified C 3 :=
  rankCertified_of_qq (j := 1) le_rfl φ hφ

end Rank

end CFSG.GH74.Generic
