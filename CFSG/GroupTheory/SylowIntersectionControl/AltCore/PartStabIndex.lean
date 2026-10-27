module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup
open scoped Pointwise Nat

section Count

variable {n : ℕ} (s : Setoid (Fin n))

private noncomputable def classPerm (g : partStab s) : Perm (Quotient s) :=
  Quotient.congr (g : Perm (Fin n)) fun a b => (g.2 a b).symm

private noncomputable def classHom : partStab s →* Perm (Quotient s) where
  toFun := classPerm s
  map_one' := by ext x; induction x using Quotient.inductionOn; rfl
  map_mul' g h := by ext x; induction x using Quotient.inductionOn; rfl

private noncomputable def classSize (c : Quotient s) : ℕ := Nat.card {x // Quotient.mk s x = c}

private theorem classHom_mem_ker {g : partStab s} :
    g ∈ (classHom s).ker ↔ Quotient.mk s ∘ (g : Perm (Fin n)) = Quotient.mk s := by
  rw [MonoidHom.mem_ker, funext_iff]
  constructor
  · intro h x
    exact congrArg (fun π : Perm (Quotient s) => π (Quotient.mk s x)) h
  · intro h
    ext c
    induction c using Quotient.inductionOn with | _ x => exact h x

private theorem mem_partStab_of_comp {g : Perm (Fin n)} (h : Quotient.mk s ∘ g = Quotient.mk s) :
    g ∈ partStab s := fun x y => by
  rw [← Quotient.eq (r := s), ← Quotient.eq (r := s)]
  have hx := congrFun h x
  have hy := congrFun h y
  simp only [Function.comp_apply] at hx hy
  rw [hx, hy]

private theorem card_classHom_ker :
    Nat.card (classHom s).ker =
      Nat.card {g : Perm (Fin n) // Quotient.mk s ∘ g = Quotient.mk s} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, (classHom_mem_ker s).1 g.2⟩
      invFun := fun g => ⟨⟨g.1, mem_partStab_of_comp s g.2⟩, (classHom_mem_ker s).2 g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem classSize_classHom (g : partStab s) (c : Quotient s) :
    classSize s (classHom s g c) = classSize s c := by
  induction c using Quotient.inductionOn with | _ x => ?_
  show Nat.card {y // Quotient.mk s y = Quotient.mk s ((g : Perm (Fin n)) x)} =
    Nat.card {y // Quotient.mk s y = Quotient.mk s x}
  exact (Nat.card_congr (Equiv.subtypeEquiv (g : Perm (Fin n))
    fun y => by rw [Quotient.eq, Quotient.eq]; exact (g.2 y x).symm)).symm

variable {s} {π : Perm (Quotient s)}

private noncomputable def fibreEquiv (h : ∀ c, classSize s (π c) = classSize s c)
    (c : Quotient s) : {x // Quotient.mk s x = c} ≃ {x // Quotient.mk s x = π c} :=
  (Finite.card_eq.1 (h c).symm).some

private noncomputable def liftPerm (h : ∀ c, classSize s (π c) = classSize s c) :
    Perm (Fin n) :=
  (Equiv.sigmaFiberEquiv (Quotient.mk s)).symm.trans
    ((Equiv.sigmaCongr π (fibreEquiv h)).trans (Equiv.sigmaFiberEquiv (Quotient.mk s)))

private theorem mk_liftPerm (h : ∀ c, classSize s (π c) = classSize s c) (x : Fin n) :
    Quotient.mk s (liftPerm h x) = π (Quotient.mk s x) :=
  (fibreEquiv h (Quotient.mk s x) ⟨x, rfl⟩).2

private theorem liftPerm_mem (h : ∀ c, classSize s (π c) = classSize s c) :
    liftPerm h ∈ partStab s := fun x y => by
  rw [← Quotient.eq (r := s), ← Quotient.eq (r := s), mk_liftPerm, mk_liftPerm]
  exact π.injective.eq_iff

variable (s)

private theorem mem_range_classHom_iff {π : Perm (Quotient s)} :
    π ∈ (classHom s).range ↔ classSize s ∘ π = classSize s := by
  constructor
  · rintro ⟨g, rfl⟩
    exact funext (classSize_classHom s g)
  · intro h
    refine ⟨⟨liftPerm (congrFun h), liftPerm_mem _⟩, ?_⟩
    ext c
    induction c using Quotient.inductionOn with | _ x => exact mk_liftPerm _ x

private theorem card_classHom_range :
    Nat.card (classHom s).range =
      Nat.card {π : Perm (Quotient s) // classSize s ∘ π = classSize s} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_range_classHom_iff s)

private noncomputable def classCount (i : ℕ) : ℕ := Nat.card {c : Quotient s // classSize s c = i}

private theorem classSize_mk (x : Fin n) :
    classSize s (Quotient.mk s x) = Nat.card {y // s.r x y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [Quotient.eq]; exact ⟨s.iseqv.symm, s.iseqv.symm⟩)

private theorem card_comp_eq_prod [Fintype (Quotient s)] [DecidableEq (Quotient s)] :
    Nat.card {g : Perm (Fin n) // Quotient.mk s ∘ g = Quotient.mk s} =
      ∏ c : Quotient s, (classSize s c)! := by
  rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card',
    Finset.image_univ_of_surjective Quotient.mk_surjective]
  simp only [classSize, Nat.card_eq_fintype_card]

private theorem card_perm_classSize [Fintype (Quotient s)] [DecidableEq (Quotient s)] :
    Nat.card {π : Perm (Quotient s) // classSize s ∘ π = classSize s} =
      ∏ i ∈ Finset.univ.image (classSize s), (classCount s i)! := by
  rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card']
  simp only [classCount, Nat.card_eq_fintype_card]

private theorem prod_classSize_eq [Fintype (Quotient s)] [DecidableEq (Quotient s)] :
    ∏ c : Quotient s, (classSize s c)! =
      ∏ i ∈ Finset.univ.image (classSize s), i ! ^ classCount s i := by
  rw [Finset.prod_comp (fun i => i !) (classSize s)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [classCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem classCount_eq_zero {i : ℕ} (hi : ∀ c, classSize s c ≠ i) : classCount s i = 0 :=
  haveI : IsEmpty {c : Quotient s // classSize s c = i} := ⟨fun c => hi c.1 c.2⟩
  Nat.card_of_isEmpty

private theorem mem_of_mem_image [Fintype (Quotient s)] {T : Finset ℕ}
    (hT : ∀ c, classSize s c ∈ T) {i : ℕ} (hi : i ∈ Finset.univ.image (classSize s)) : i ∈ T := by
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hi
  exact hT c

private theorem classCount_eq_zero' [Fintype (Quotient s)] {i : ℕ}
    (hi : i ∉ Finset.univ.image (classSize s)) : classCount s i = 0 :=
  classCount_eq_zero s fun c hc => hi (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩)

private theorem card_partStab_eq_prod (T : Finset ℕ) (hT : ∀ c, classSize s c ∈ T) :
    Nat.card (partStab s) = ∏ i ∈ T, (i ! ^ classCount s i * (classCount s i)!) := by
  classical
  have := Fintype.ofFinite (Quotient s)
  rw [← Subgroup.card_ker_mul_card_range (classHom s), card_classHom_ker, card_classHom_range,
    card_comp_eq_prod, card_perm_classSize, prod_classSize_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_subset (fun i hi => mem_of_mem_image s hT hi) fun i _ hi => ?_
  rw [classCount_eq_zero' s hi]
  simp

private theorem card_eq_sum_classSize [Fintype (Quotient s)] :
    n = ∑ c : Quotient s, classSize s c := by
  have := Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk s))
  rw [Nat.card_sigma, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  exact this.symm

private theorem card_eq_sum_classCount (T : Finset ℕ) (hT : ∀ c, classSize s c ∈ T) :
    n = ∑ i ∈ T, classCount s i * i := by
  classical
  have := Fintype.ofFinite (Quotient s)
  calc n = ∑ c : Quotient s, classSize s c := card_eq_sum_classSize s
    _ = ∑ i ∈ Finset.univ.image (classSize s), classCount s i * i := by
        rw [Finset.sum_comp (fun i : ℕ => i) (classSize s)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [classCount, Nat.card_eq_fintype_card, Fintype.card_subtype, smul_eq_mul]
    _ = ∑ i ∈ T, classCount s i * i :=
        Finset.sum_subset (fun i hi => mem_of_mem_image s hT hi) fun i _ hi => by
          rw [classCount_eq_zero' s hi, zero_mul]

private theorem card_partStab_uniform {d : ℕ} (hs : ∀ x, Nat.card {y // s.r x y} = d) :
    ∃ k, n = k * d ∧ Nat.card (partStab s) = d ! ^ k * k ! := by
  have hT : ∀ c, classSize s c ∈ ({d} : Finset ℕ) := fun c => by
    induction c using Quotient.inductionOn with | _ x => ?_
    rw [Finset.mem_singleton, classSize_mk, hs]
  exact ⟨classCount s d, by simpa using card_eq_sum_classCount s {d} hT,
    by simpa using card_partStab_eq_prod s {d} hT⟩

private theorem classSize_mk_special {b : Fin n} {d e : ℕ}
    (hb : Nat.card {y // s.r b y} = e) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = d)
    (x : Fin n) : (s.r b x ∧ classSize s (Quotient.mk s x) = e) ∨
      (¬ s.r b x ∧ classSize s (Quotient.mk s x) = d) := by
  rw [classSize_mk]
  by_cases h : s.r b x
  · refine Or.inl ⟨h, hb ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)⟩
    exact ⟨fun hy => s.iseqv.trans h hy, fun hy => s.iseqv.trans (s.iseqv.symm h) hy⟩
  · exact Or.inr ⟨h, hs x h⟩

private theorem card_partStab_special {b : Fin n} {d e : ℕ} (hde : d ≠ e)
    (hb : Nat.card {y // s.r b y} = e) (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = d) :
    ∃ k, n = k * d + e ∧ Nat.card (partStab s) = d ! ^ k * k ! * e ! := by
  have hsize := classSize_mk_special s hb hs
  have hT : ∀ c, classSize s c ∈ ({d, e} : Finset ℕ) := fun c => by
    induction c using Quotient.inductionOn with | _ x => ?_
    rcases hsize x with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hone : classCount s e = 1 := by
    rw [classCount, Nat.card_eq_one_iff_exists]
    refine ⟨⟨Quotient.mk s b, by rw [classSize_mk, hb]⟩, ?_⟩
    rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with | _ x => ?_
    refine Subtype.ext (Quotient.sound ?_)
    rcases hsize x with ⟨h, -⟩ | ⟨-, h⟩
    · exact s.iseqv.symm h
    · exact absurd (h.symm.trans hc) hde
  refine ⟨classCount s d, ?_, ?_⟩
  · simpa [Finset.sum_pair hde, hone] using card_eq_sum_classCount s {d, e} hT
  · simpa [Finset.prod_pair hde, hone] using card_partStab_eq_prod s {d, e} hT

end Count

section Stab

variable {n : ℕ}

private theorem card_stabilizer_finset (Γ : Finset (Fin n)) :
    Nat.card (MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n))) =
      Γ.card ! * (n - Γ.card)! := by
  classical
  have e : MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n)) ≃
      {g : Perm (Fin n) // (fun a => decide (a ∈ Γ)) ∘ g = fun a => decide (a ∈ Γ)} :=
    Equiv.subtypeEquivRight fun g => by
      rw [MulAction.mem_stabilizer_set, funext_iff]
      simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, DomMulAct.stabilizer_card, Fintype.prod_bool]
  simp

end Stab

section Arith

private theorem v2_fact_two_mul (a : ℕ) :
    padicValNat 2 (2 * a)! = padicValNat 2 a ! + a := padicValNat_factorial_mul a

private theorem v2_fact_two_mul_add_one (a : ℕ) :
    padicValNat 2 (2 * a + 1)! = padicValNat 2 a ! + a := by
  rw [padicValNat_factorial_mul_add a (by norm_num : 1 < 2), padicValNat_factorial_mul]

private theorem v2_fact_pow_mul (j a : ℕ) :
    padicValNat 2 (2 ^ j * a)! = (2 ^ j - 1) * a + padicValNat 2 a ! := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc, v2_fact_two_mul, ih]
    have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ j = t + 1 := ⟨2 ^ j - 1, by omega⟩
    rw [ht, show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
    simp only [Nat.add_sub_cancel]
    ring

private theorem v2_fact_one : padicValNat 2 1 ! = 0 := by simp

private theorem v2_fact_two : padicValNat 2 2 ! = 1 := by
  have h := v2_fact_two_mul 1
  rw [v2_fact_one] at h
  exact h

private theorem v2_fact_three : padicValNat 2 3 ! = 1 := by
  have h := v2_fact_two_mul_add_one 1
  rw [v2_fact_one] at h
  exact h

private theorem v2_fact_four : padicValNat 2 4 ! = 3 := by
  have h := v2_fact_two_mul 2
  rw [v2_fact_two] at h
  exact h

private theorem odd_index_of_padicVal {n : ℕ} {H : Subgroup (Perm (Fin n))}
    (h : padicValNat 2 (Nat.card H) = padicValNat 2 n !) : Odd H.index := by
  have h1 := H.card_mul_index
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h1
  have h2 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h4 := congrArg (padicValNat 2) h1
  rw [padicValNat.mul h3 h2] at h4
  rw [Nat.odd_iff]
  by_contra hodd
  have := one_le_padicValNat_of_dvd h2 (by omega : 2 ∣ H.index)
  omega

private theorem v2_uniform (d k : ℕ) :
    padicValNat 2 (d ! ^ k * k !) = k * padicValNat 2 d ! + padicValNat 2 k ! := by
  rw [padicValNat.mul (pow_ne_zero _ d.factorial_ne_zero) k.factorial_ne_zero, padicValNat.pow]

private theorem v2_special (d k e : ℕ) : padicValNat 2 (d ! ^ k * k ! * e !) =
    k * padicValNat 2 d ! + padicValNat 2 k ! + padicValNat 2 e ! := by
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ d.factorial_ne_zero) k.factorial_ne_zero)
    e.factorial_ne_zero, v2_uniform]

private theorem v2_fact_odd {n : ℕ} (hn : n % 2 = 1) :
    padicValNat 2 n ! = padicValNat 2 (n - 1)! := by
  obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by omega⟩
  rw [v2_fact_two_mul_add_one, Nat.add_sub_cancel, v2_fact_two_mul]

private theorem v2_split {m : ℕ} (w : ℕ) (hm : 1 ≤ m) :
    padicValNat 2 (2 ^ m + 1)! + padicValNat 2 (2 ^ m * (2 * w))! =
      padicValNat 2 (2 ^ m * (2 * w + 1))! := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 := v2_fact_pow_mul m 1
  rw [mul_one, v2_fact_one] at h1
  have h2 : 2 ^ (m + 1) + 1 = 2 * 2 ^ m + 1 := by ring
  have h3 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have h4 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [h2, v2_fact_two_mul_add_one, h1, v2_fact_pow_mul, v2_fact_pow_mul, v2_fact_two_mul,
    v2_fact_two_mul_add_one, mul_add (2 ^ (m + 1) - 1), mul_one, h3]
  omega

private theorem v2_stab_pow {n m : ℕ} (h1 : n % 4 = 1)
    (hm : 2 ^ m ∣ n - 1 ∧ ¬ 2 ^ (m + 1) ∣ n - 1) :
    padicValNat 2 (2 ^ m + 1)! + padicValNat 2 (n - (2 ^ m + 1))! = padicValNat 2 (n - 1)! := by
  have hm1 : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    exact hm.2 (Nat.dvd_of_mod_eq_zero (by omega))
  obtain ⟨u, hu⟩ := hm.1
  have hu2 : u % 2 = 1 := by
    by_contra h0
    obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w := ⟨u / 2, by omega⟩
    exact hm.2 ⟨w, by rw [hu]; ring⟩
  obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w + 1 := ⟨u / 2, by omega⟩
  have hu' := hu
  rw [mul_add, mul_one] at hu'
  rw [show n - (2 ^ m + 1) = 2 ^ m * (2 * w) by omega, hu]
  exact v2_split w hm1

end Arith

variable {n : ℕ} {s : Setoid (Fin n)}

theorem odd_index_partStab_pairs (hs : ∀ x, Nat.card {y // s.r x y} = 2) :
    Odd (partStab s).index := by
  obtain ⟨k, hn, hc⟩ := card_partStab_uniform s hs
  refine odd_index_of_padicVal ?_
  rw [hc, v2_uniform, v2_fact_two, show n = 2 * k by omega, v2_fact_two_mul]
  omega

theorem odd_index_partStab_quads (hs : ∀ x, Nat.card {y // s.r x y} = 4) :
    Odd (partStab s).index := by
  obtain ⟨k, hn, hc⟩ := card_partStab_uniform s hs
  refine odd_index_of_padicVal ?_
  rw [hc, v2_uniform, v2_fact_four, show n = 2 * (2 * k) by omega, v2_fact_two_mul,
    v2_fact_two_mul]
  omega

theorem odd_index_partStab_quadsPair {b : Fin n} (hb : Nat.card {y // s.r b y} = 2)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) : Odd (partStab s).index := by
  obtain ⟨k, hn, hc⟩ := card_partStab_special s (by norm_num) hb hs
  refine odd_index_of_padicVal ?_
  rw [hc, v2_special, v2_fact_four, v2_fact_two, show n = 2 * (2 * k + 1) by omega,
    v2_fact_two_mul, v2_fact_two_mul_add_one]
  omega

theorem odd_index_partStab_pairsPoint {b : Fin n} (hb : Nat.card {y // s.r b y} = 1)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 2) : Odd (partStab s).index := by
  obtain ⟨k, hn, hc⟩ := card_partStab_special s (by norm_num) hb hs
  refine odd_index_of_padicVal ?_
  rw [hc, v2_special, v2_fact_two, v2_fact_one, show n = 2 * k + 1 by omega,
    v2_fact_two_mul_add_one]
  omega

theorem odd_index_partStab_quadsTriple {b : Fin n} (hb : Nat.card {y // s.r b y} = 3)
    (hs : ∀ x, ¬ s.r b x → Nat.card {y // s.r x y} = 4) : Odd (partStab s).index := by
  obtain ⟨k, hn, hc⟩ := card_partStab_special s (by norm_num) hb hs
  refine odd_index_of_padicVal ?_
  rw [hc, v2_special, v2_fact_four, v2_fact_three, show n = 2 * (2 * k + 1) + 1 by omega,
    v2_fact_two_mul_add_one, v2_fact_two_mul_add_one]
  omega

theorem odd_index_stabilizer_finset (h1 : n % 4 = 1) {Γ : Finset (Fin n)} {m : ℕ}
    (hm : 2 ^ m ∣ n - 1 ∧ ¬ 2 ^ (m + 1) ∣ n - 1) (hΓ : Γ.card = 1 ∨ Γ.card = 2 ^ m + 1) :
    Odd (MulAction.stabilizer (Perm (Fin n)) (Γ : Set (Fin n))).index := by
  refine odd_index_of_padicVal ?_
  rw [card_stabilizer_finset,
    padicValNat.mul Γ.card.factorial_ne_zero (n - Γ.card).factorial_ne_zero,
    v2_fact_odd (by omega : n % 2 = 1)]
  rcases hΓ with h | h
  · rw [h, v2_fact_one, zero_add]
  · rw [h]
    exact v2_stab_pow h1 hm

end CFSG.GroupTheory.AltCore
