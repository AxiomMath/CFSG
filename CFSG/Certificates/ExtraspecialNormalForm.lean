module

public import CFSG.Monster.B.Short.Extraspecial
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.Certificates.ExtraspecialNF

open scoped commutatorElement

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def mon (q : Fin n → G) (v : Fin n → ZMod 2) : G :=
  (List.ofFn fun i => q i ^ (v i).val).prod

@[expose] def nf (z : G) (q : Fin n → G) (s : ZMod 2) (v : Fin n → ZMod 2) : G :=
  z ^ s.val * mon q v

structure Rel (z : G) (q : Fin n → G) (c : Fin n → Fin n → ZMod 2) : Prop where
  z_sq : z * z = 1
  z_comm : ∀ i, z * q i = q i * z
  q_sq : ∀ i, q i * q i = 1
  comm : ∀ i j, q i * q j = q j * q i * z ^ (c i j).val

@[expose] def collect (c : Fin n → Fin n → ZMod 2) (v w : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, if j < i then c i j * v i * w j else 0

@[expose] def qf (c : Fin n → Fin n → ZMod 2) (v : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, if i < j then c i j * v i * v j else 0

@[expose] def bil (c : Fin n → Fin n → ZMod 2) (v w : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, v i * c i j * w j

@[expose] def Nondegenerate (c : Fin n → Fin n → ZMod 2) : Prop :=
  ∀ v : Fin n → ZMod 2, v ≠ 0 → ∃ w, bil c v w ≠ 0

instance instDecidableNondegenerate (c : Fin n → Fin n → ZMod 2) : Decidable (Nondegenerate c) :=
  inferInstanceAs (Decidable (∀ v : Fin n → ZMod 2, v ≠ 0 → ∃ w, bil c v w ≠ 0))

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

theorem pow_val_add {x : G} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h11]
    simp [val_one_two, hx]

theorem mon_zero (q : Fin 0 → G) (v : Fin 0 → ZMod 2) : mon q v = 1 := by
  simp [mon]

theorem mon_zero_vec (q : Fin n → G) : mon q 0 = 1 := by
  simp [mon]

theorem mon_succ (q : Fin (n + 1) → G) (v : Fin (n + 1) → ZMod 2) :
    mon q v = q 0 ^ (v 0).val * mon (fun i => q i.succ) (fun i => v i.succ) := by
  simp [mon, List.ofFn_succ]

theorem mon_single (q : Fin n → G) (j : Fin n) : mon q (Pi.single j 1) = q j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [mon_succ]
    refine Fin.cases ?_ (fun j' => ?_) j
    · have ht : (fun i : Fin n => (Pi.single 0 1 : Fin (n + 1) → ZMod 2) i.succ) = 0 := by
        funext i
        simp [Fin.succ_ne_zero]
      rw [ht, mon_zero_vec]
      simp [val_one_two]
    · have h0 : (Pi.single j'.succ 1 : Fin (n + 1) → ZMod 2) 0 = 0 :=
        Pi.single_eq_of_ne (Fin.succ_ne_zero j').symm _
      have ht : (fun i : Fin n => (Pi.single j'.succ 1 : Fin (n + 1) → ZMod 2) i.succ) =
          Pi.single j' 1 := by
        funext i
        simp [Pi.single_apply]
      rw [h0, ht, ih]
      simp

theorem commute_mon {x : G} {q : Fin n → G} (hx : ∀ i, x * q i = q i * x) (v : Fin n → ZMod 2) :
    Commute x (mon q v) := by
  unfold mon
  refine Commute.list_prod_right _ _ fun a ha => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact (show Commute x (q i) from hx i).pow_right _

private theorem step_aux {A M y Z S : G} (h0 : A * y = y * A * Z) (ih : M * y = y * M * S)
    (hc : Z * M = M * Z) : A * M * y = y * (A * M) * (Z * S) := by
  calc A * M * y = A * (M * y) := mul_assoc _ _ _
    _ = A * (y * M * S) := by rw [ih]
    _ = (A * y) * M * S := by simp only [mul_assoc]
    _ = (y * A * Z) * M * S := by rw [h0]
    _ = y * A * (Z * M) * S := by simp only [mul_assoc]
    _ = y * A * (M * Z) * S := by rw [hc]
    _ = y * (A * M) * (Z * S) := by simp only [mul_assoc]

theorem mon_mul_gen {z : G} (hzz : z * z = 1) {y : G} (q : Fin n → G)
    (hz : ∀ i, z * q i = q i * z) (d : Fin n → ZMod 2)
    (hy : ∀ i, q i * y = y * q i * z ^ (d i).val) (u : Fin n → ZMod 2) :
    mon q u * y = y * mon q u * z ^ (∑ i, d i * u i).val := by
  induction n with
  | zero => simp [mon_zero]
  | succ n ih =>
    have ih' := ih (fun i => q i.succ) (fun i => hz i.succ) (fun i => d i.succ)
      (fun i => hy i.succ) (fun i => u i.succ)
    have h0 : q 0 ^ (u 0).val * y = y * q 0 ^ (u 0).val * z ^ (d 0 * u 0).val := by
      rcases zmod_two_cases (u 0) with h | h
      · simp [h]
      · simp [h, val_one_two, hy 0]
    have hcz : ∀ k : ℕ, z ^ k * mon (fun i => q i.succ) (fun i => u i.succ) =
        mon (fun i => q i.succ) (fun i => u i.succ) * z ^ k := fun k =>
      ((commute_mon (fun i => hz i.succ) _).pow_left k).eq
    rw [mon_succ, Fin.sum_univ_succ, pow_val_add hzz]
    exact step_aux h0 ih' (hcz _)

variable {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

theorem collect_succ (c : Fin (n + 1) → Fin (n + 1) → ZMod 2) (v w : Fin (n + 1) → ZMod 2) :
    collect c v w = (∑ i : Fin n, c i.succ 0 * v i.succ * w 0) +
      collect (fun i j => c i.succ j.succ) (fun i => v i.succ) (fun i => w i.succ) := by
  simp [collect, Fin.sum_univ_succ, Finset.sum_add_distrib]

theorem collect_zero_right (c : Fin n → Fin n → ZMod 2) (v : Fin n → ZMod 2) :
    collect c v 0 = 0 := by
  simp [collect]

theorem collect_single (c : Fin n → Fin n → ZMod 2) (v : Fin n → ZMod 2) (j : Fin n) :
    collect c v (Pi.single j 1) = ∑ k, if j < k then c k j * v k else 0 := by
  unfold collect
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

theorem Rel.tail {q : Fin (n + 1) → G} {c : Fin (n + 1) → Fin (n + 1) → ZMod 2}
    (h : Rel z q c) :
    Rel z (fun i : Fin n => q i.succ) (fun i j => c i.succ j.succ) where
  z_sq := h.z_sq
  z_comm i := h.z_comm i.succ
  q_sq i := h.q_sq i.succ
  comm i j := h.comm i.succ j.succ

private theorem mul_mul_comm_aux {x y A M : G} (hx : x * A = A * x) (hy : y * A = A * y) :
    A * (x * (y * M)) = x * (y * (A * M)) := by
  calc A * (x * (y * M)) = (A * x) * (y * M) := by simp only [mul_assoc]
    _ = (x * A) * (y * M) := by rw [hx]
    _ = x * (A * (y * M)) := by simp only [mul_assoc]
    _ = x * ((A * y) * M) := by simp only [mul_assoc]
    _ = x * ((y * A) * M) := by rw [hy]
    _ = x * (y * (A * M)) := by simp only [mul_assoc]

private theorem step_aux' {A B Mv Mw Z : G} (hM : Mv * B = B * Mv * Z) (hc : Z * Mv = Mv * Z) :
    A * Mv * (B * Mw) = (A * B) * (Z * (Mv * Mw)) := by
  calc A * Mv * (B * Mw) = A * (Mv * B) * Mw := by simp only [mul_assoc]
    _ = A * (B * Mv * Z) * Mw := by rw [hM]
    _ = (A * B) * (Mv * Z) * Mw := by simp only [mul_assoc]
    _ = (A * B) * (Z * Mv) * Mw := by rw [hc]
    _ = (A * B) * (Z * (Mv * Mw)) := by simp only [mul_assoc]

theorem mon_mul_mon (h : Rel z q c) (v w : Fin n → ZMod 2) :
    mon q v * mon q w = z ^ (collect c v w).val * mon q (v + w) := by
  induction n with
  | zero => simp [mon_zero, collect]
  | succ n ih =>
    have ih' := ih h.tail (fun i => v i.succ) (fun i => w i.succ)
    have hy : ∀ i : Fin n, q i.succ * q 0 ^ (w 0).val =
        q 0 ^ (w 0).val * q i.succ * z ^ (c i.succ 0 * w 0).val := by
      intro i
      rcases zmod_two_cases (w 0) with hw | hw
      · simp [hw]
      · simp [hw, val_one_two, h.comm i.succ 0]
    have hM := mon_mul_gen h.z_sq (fun i => q i.succ) (fun i => h.z_comm i.succ)
      (fun i => c i.succ 0 * w 0) hy (fun i => v i.succ)
    have hcz : ∀ k : ℕ, z ^ k * mon (fun i => q i.succ) (fun i => v i.succ) =
        mon (fun i => q i.succ) (fun i => v i.succ) * z ^ k := fun k =>
      ((commute_mon (fun i => h.z_comm i.succ) _).pow_left k).eq
    have hE : (∑ i : Fin n, c i.succ 0 * v i.succ * w 0) =
        ∑ i : Fin n, c i.succ 0 * w 0 * v i.succ :=
      Finset.sum_congr rfl fun i _ => mul_right_comm _ _ _
    have hAB : q 0 ^ (v 0).val * q 0 ^ (w 0).val = q 0 ^ (v 0 + w 0).val :=
      (pow_val_add (h.q_sq 0) _ _).symm
    have hzAB : ∀ k : ℕ, z ^ k * (q 0 ^ (v 0 + w 0).val) = q 0 ^ (v 0 + w 0).val * z ^ k :=
      fun k => ((show Commute z (q 0) from h.z_comm 0).pow_pow k _).eq
    have hvw : (fun i : Fin n => (v + w) i.succ) = (fun i => v i.succ) + (fun i => w i.succ) :=
      rfl
    rw [mon_succ q v, mon_succ q w, mon_succ q (v + w), collect_succ, hvw, hE,
      step_aux' hM (hcz _), hAB, ih', pow_val_add h.z_sq, mul_assoc (z ^ _)]
    exact mul_mul_comm_aux (hzAB _) (hzAB _)

theorem nf_zero_zero (z : G) (q : Fin n → G) : nf z q 0 0 = 1 := by
  simp [nf, mon_zero_vec]

theorem nf_zero_vec (z : G) (q : Fin n → G) (b : ZMod 2) : nf z q b 0 = z ^ b.val := by
  simp [nf, mon_zero_vec]

theorem nf_one_zero (z : G) (q : Fin n → G) : nf z q 1 0 = z := by
  simp [nf_zero_vec, val_one_two]

theorem nf_single (z : G) (q : Fin n → G) (j : Fin n) : nf z q 0 (Pi.single j 1) = q j := by
  simp [nf, mon_single]

theorem nf_mul_nf (h : Rel z q c) (s t : ZMod 2) (v w : Fin n → ZMod 2) :
    nf z q s v * nf z q t w = nf z q (s + t + collect c v w) (v + w) := by
  have hv := (commute_mon h.z_comm v).pow_left t.val
  calc nf z q s v * nf z q t w = z ^ s.val * (mon q v * z ^ t.val) * mon q w := by
        simp only [nf, mul_assoc]
    _ = z ^ s.val * (z ^ t.val * mon q v) * mon q w := by rw [hv.eq]
    _ = z ^ s.val * z ^ t.val * (mon q v * mon q w) := by simp only [mul_assoc]
    _ = z ^ s.val * z ^ t.val * (z ^ (collect c v w).val * mon q (v + w)) := by
        rw [mon_mul_mon h]
    _ = nf z q (s + t + collect c v w) (v + w) := by
        simp only [nf, pow_val_add h.z_sq, mul_assoc]

theorem nf_mul_zpow (h : Rel z q c) (s b : ZMod 2) (v : Fin n → ZMod 2) :
    nf z q s v * z ^ b.val = nf z q (s + b) v := by
  rw [← nf_zero_vec z q b, nf_mul_nf h, collect_zero_right, add_zero, add_zero]

theorem nf_mul_q (h : Rel z q c) (s : ZMod 2) (v : Fin n → ZMod 2) (j : Fin n) :
    nf z q s v * q j =
      nf z q (s + ∑ k, if j < k then c k j * v k else 0) (v + Pi.single j 1) := by
  rw [← nf_single z q j, nf_mul_nf h, collect_single, add_zero]

theorem nf_mul_q_of_symm (h : Rel z q c) (hsymm : ∀ i j, c i j = c j i) (s : ZMod 2)
    (v : Fin n → ZMod 2) (j : Fin n) :
    nf z q s v * q j =
      nf z q (s + ∑ k, if j < k then c j k * v k else 0) (v + Pi.single j 1) := by
  have e : (∑ k, if j < k then c k j * v k else 0) = ∑ k, if j < k then c j k * v k else 0 :=
    Finset.sum_congr rfl fun k _ => by rw [hsymm k j]
  rw [nf_mul_q h, e]

theorem nf_mul_z (h : Rel z q c) (s : ZMod 2) (v : Fin n → ZMod 2) :
    nf z q s v * z = nf z q (s + 1) v := by
  simpa [val_one_two] using nf_mul_zpow h s 1 v

theorem q_mem_closure (z : G) (q : Fin n → G) (j : Fin n) :
    q j ∈ Subgroup.closure (insert z (Set.range q)) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self j))

theorem z_mem_closure (z : G) (q : Fin n → G) :
    z ∈ Subgroup.closure (insert z (Set.range q)) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem nf_mem_closure (z : G) (q : Fin n → G) (s : ZMod 2) (v : Fin n → ZMod 2) :
    nf z q s v ∈ Subgroup.closure (insert z (Set.range q)) := by
  refine mul_mem (pow_mem (z_mem_closure z q) _) ?_
  unfold mon
  refine Subgroup.list_prod_mem _ fun a ha => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact pow_mem (q_mem_closure z q i) _

private def nfSubgroup (h : Rel z q c) : Subgroup G where
  carrier := Set.range (Function.uncurry (nf z q))
  one_mem' := ⟨(0, 0), nf_zero_zero z q⟩
  mul_mem' := by
    rintro _ _ ⟨⟨s, v⟩, rfl⟩ ⟨⟨t, w⟩, rfl⟩
    exact ⟨(s + t + collect c v w, v + w), (nf_mul_nf h s t v w).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨s, v⟩, rfl⟩
    refine ⟨(s + collect c v v, v), ?_⟩
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    have e1 : ∀ a b : ZMod 2, a + (a + b) + b = 0 := by decide
    have e2 : v + v = 0 := by
      funext i
      have : ∀ a : ZMod 2, a + a = 0 := by decide
      exact this _
    show nf z q s v * nf z q (s + collect c v v) v = 1
    rw [nf_mul_nf h, e1, e2, nf_zero_zero]

theorem mem_closure_iff (h : Rel z q c) {x : G} :
    x ∈ Subgroup.closure (insert z (Set.range q)) ↔ ∃ s v, nf z q s v = x := by
  constructor
  · intro hx
    have hle : Subgroup.closure (insert z (Set.range q)) ≤ nfSubgroup h := by
      rw [Subgroup.closure_le]
      rintro x (rfl | ⟨j, rfl⟩)
      · exact ⟨(1, 0), nf_one_zero x q⟩
      · exact ⟨(0, Pi.single j 1), nf_single z q j⟩
    obtain ⟨⟨s, v⟩, hsv⟩ := hle hx
    exact ⟨s, v, hsv⟩
  · rintro ⟨s, v, rfl⟩
    exact nf_mem_closure z q s v

theorem range_nf (h : Rel z q c) :
    Set.range (Function.uncurry (nf z q)) =
      (Subgroup.closure (insert z (Set.range q)) : Set G) := by
  ext x
  rw [SetLike.mem_coe, mem_closure_iff h]
  constructor
  · rintro ⟨⟨s, v⟩, rfl⟩
    exact ⟨s, v, rfl⟩
  · rintro ⟨s, v, rfl⟩
    exact ⟨(s, v), rfl⟩

theorem finite_closure (h : Rel z q c) :
    Finite ↥(Subgroup.closure (insert z (Set.range q))) := by
  have e : (Subgroup.closure (insert z (Set.range q)) : Set G) =
      Set.range (Function.uncurry (nf z q)) := (range_nf h).symm
  rw [← SetLike.coe_sort_coe, e]
  exact (Set.finite_range _).to_subtype

theorem natCard_pairs : Nat.card (ZMod 2 × (Fin n → ZMod 2)) = 2 ^ (n + 1) := by
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_succ, mul_comm]

theorem card_closure (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q))) :
    Nat.card (Subgroup.closure (insert z (Set.range q))) = 2 ^ (n + 1) := by
  calc Nat.card (Subgroup.closure (insert z (Set.range q)))
      = Nat.card (Set.range (Function.uncurry (nf z q))) := by rw [range_nf h]; rfl
    _ = Nat.card (ZMod 2 × (Fin n → ZMod 2)) := Nat.card_range_of_injective hinj
    _ = 2 ^ (n + 1) := natCard_pairs

theorem injective_of_card_ge (h : Rel z q c)
    (hcard : 2 ^ (n + 1) ≤ Nat.card (Subgroup.closure (insert z (Set.range q)))) :
    Function.Injective (Function.uncurry (nf z q)) := by
  let f : ZMod 2 × (Fin n → ZMod 2) → ↥(Subgroup.closure (insert z (Set.range q))) :=
    fun p => ⟨nf z q p.1 p.2, nf_mem_closure z q p.1 p.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
    exact ⟨(s, v), rfl⟩
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (by rw [natCard_pairs]; exact hcard)
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

theorem injective_iff_card (h : Rel z q c) :
    Function.Injective (Function.uncurry (nf z q)) ↔
      Nat.card (Subgroup.closure (insert z (Set.range q))) = 2 ^ (n + 1) :=
  ⟨card_closure h, fun hc => injective_of_card_ge h hc.ge⟩

theorem eq_of_nf_eq (hinj : Function.Injective (Function.uncurry (nf z q)))
    {s t : ZMod 2} {v w : Fin n → ZMod 2} (h : nf z q s v = nf z q t w) : s = t ∧ v = w :=
  Prod.mk.inj (hinj (a₁ := (s, v)) (a₂ := (t, w)) h)

theorem ne_one_of_injective (hinj : Function.Injective (Function.uncurry (nf z q))) :
    z ≠ 1 := by
  intro hz
  have h1 : nf z q 1 0 = nf z q 0 0 := by rw [nf_one_zero, nf_zero_zero, hz]
  exact absurd (eq_of_nf_eq hinj h1).1 (by decide)

theorem nf_mul_self (h : Rel z q c) (s : ZMod 2) (v : Fin n → ZMod 2) :
    nf z q s v * nf z q s v = z ^ (collect c v v).val := by
  have e1 : ∀ a b : ZMod 2, a + a + b = b := by decide
  have e2 : v + v = 0 := by
    funext i
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this _
  rw [nf_mul_nf h, e1, e2, nf_zero_vec]

theorem collect_self (hsymm : ∀ i j, c i j = c j i) (v : Fin n → ZMod 2) :
    collect c v v = qf c v := by
  unfold collect qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [hsymm j i]
    ring
  · rfl

theorem nf_sq (h : Rel z q c) (hsymm : ∀ i j, c i j = c j i) (s : ZMod 2)
    (v : Fin n → ZMod 2) : nf z q s v ^ 2 = z ^ (qf c v).val := by
  rw [sq, nf_mul_self h, collect_self hsymm]

theorem bil_eq_collect_add (hsymm : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (v w : Fin n → ZMod 2) : bil c v w = collect c v w + collect c w v := by
  unfold bil collect
  have h2 : (∑ i, ∑ j, if j < i then c i j * w i * v j else 0) =
      ∑ i, ∑ j, if i < j then c i j * v i * w j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [hsymm j i]
      ring
    · rfl
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy j i with hji | rfl | hij
  · simp only [hji, not_lt.2 hji.le, ↓reduceIte, add_zero]
    ring
  · simp [hdiag]
  · simp only [hij, not_lt.2 hij.le, ↓reduceIte, zero_add]
    ring

theorem nf_mul_comm (h : Rel z q c) (hsymm : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (s t : ZMod 2) (v w : Fin n → ZMod 2) :
    nf z q s v * nf z q t w = nf z q t w * nf z q s v * z ^ (bil c v w).val := by
  rw [nf_mul_nf h, nf_mul_nf h, nf_mul_zpow h, bil_eq_collect_add hsymm hdiag, add_comm w v]
  congr 1
  generalize collect c v w = a
  generalize collect c w v = b
  revert s t a b
  decide

theorem Rel.pow_diag (h : Rel z q c) (i : Fin n) : z ^ (c i i).val = 1 :=
  mul_eq_left.1 (h.comm i i).symm

theorem Rel.diag_eq_zero (h : Rel z q c) (hz : z ≠ 1) (i : Fin n) : c i i = 0 := by
  rcases zmod_two_cases (c i i) with h0 | h1
  · exact h0
  · exact absurd (by simpa [h1, val_one_two] using h.pow_diag i) hz

theorem Rel.symm_of_ne_one (h : Rel z q c) (hz : z ≠ 1) (i j : Fin n) : c i j = c j i := by
  have h1 := h.comm i j
  have h2 := h.comm j i
  have h3 : z ^ (c j i).val * z ^ (c i j).val = 1 := by
    have : q i * q j * (z ^ (c j i).val * z ^ (c i j).val) = q i * q j := by
      calc q i * q j * (z ^ (c j i).val * z ^ (c i j).val)
          = (q i * q j * z ^ (c j i).val) * z ^ (c i j).val := by simp only [mul_assoc]
        _ = q j * q i * z ^ (c i j).val := by rw [← h2]
        _ = q i * q j := h1.symm
    exact mul_eq_left.1 this
  rcases zmod_two_cases (c i j) with a | a <;> rcases zmod_two_cases (c j i) with b | b
  · rw [a, b]
  · exact absurd (by simpa [a, b, val_one_two] using h3) hz
  · exact absurd (by simpa [a, b, val_one_two] using h3) hz
  · rw [a, b]

theorem Rel.symm_of_injective (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (i j : Fin n) : c i j = c j i :=
  h.symm_of_ne_one (ne_one_of_injective hinj) i j

theorem Rel.diag_of_injective (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (i : Fin n) : c i i = 0 :=
  h.diag_eq_zero (ne_one_of_injective hinj) i

theorem nf_sq_eq_one_iff (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (s : ZMod 2) (v : Fin n → ZMod 2) : nf z q s v ^ 2 = 1 ↔ qf c v = 0 := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  rw [nf_sq h (h.symm_of_injective hinj)]
  rcases zmod_two_cases (qf c v) with h0 | h1
  · simp [h0]
  · rw [h1, val_one_two, pow_one]
    exact iff_of_false hz1 (by decide)

theorem card_sq_eq_one (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q))) :
    Nat.card {x : ↥(Subgroup.closure (insert z (Set.range q))) // x ^ 2 = 1} =
      2 * Nat.card {v : Fin n → ZMod 2 // qf c v = 0} := by
  let f : ZMod 2 × {v : Fin n → ZMod 2 // qf c v = 0} →
      {x : ↥(Subgroup.closure (insert z (Set.range q))) // x ^ 2 = 1} :=
    fun p => ⟨⟨nf z q p.1 p.2.1, nf_mem_closure z q p.1 p.2.1⟩, Subtype.ext
      ((nf_sq_eq_one_iff h hinj _ _).2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨s, v, hv⟩ ⟨t, w, hw⟩ hst
      obtain ⟨rfl, rfl⟩ := eq_of_nf_eq hinj (congrArg (fun x => (x.1 : G)) hst)
      rfl
    · rintro ⟨⟨x, hx⟩, hx2⟩
      obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
      exact ⟨(s, ⟨v, (nf_sq_eq_one_iff h hinj s v).1 (congrArg Subtype.val hx2)⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_zmod]

theorem commute_of_mem_closure (h : Rel z q c) {x : G}
    (hx : x ∈ Subgroup.closure (insert z (Set.range q))) : Commute z x := by
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
  exact ((Commute.refl z).pow_right _).mul_right (commute_mon h.z_comm v)

theorem commutator_eq_zpow (h : Rel z q c) (hsymm : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (s t : ZMod 2) (v w : Fin n → ZMod 2) :
    ⁅nf z q s v, nf z q t w⁆ = z ^ (bil c v w).val := by
  have hzyx : Commute (z ^ (bil c v w).val) (nf z q t w * nf z q s v) :=
    ((commute_of_mem_closure h (nf_mem_closure z q t w)).mul_right
      (commute_of_mem_closure h (nf_mem_closure z q s v))).pow_left _
  have e : nf z q s v * nf z q t w = z ^ (bil c v w).val * (nf z q t w * nf z q s v) :=
    (nf_mul_comm h hsymm hdiag s t v w).trans hzyx.eq.symm
  rw [commutatorElement_def, e]
  group

theorem mem_zpowers_iff_exists (h : Rel z q c) {x : G} :
    x ∈ Subgroup.zpowers z ↔ ∃ b : ZMod 2, z ^ b.val = x := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    clear hx
    induction k using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ i ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨b + 1, ?_⟩
      rw [pow_val_add h.z_sq, val_one_two, pow_one, hb, zpow_add_one]
    | pred i ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨b + 1, ?_⟩
      rw [pow_val_add h.z_sq, val_one_two, pow_one, hb, zpow_sub_one,
        inv_eq_of_mul_eq_one_right h.z_sq]
  · rintro ⟨b, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _

theorem center_eq (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) :
    Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) =
      (Subgroup.zpowers z).subgroupOf (Subgroup.closure (insert z (Set.range q))) := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  have hsymm := h.symm_of_ne_one hz1
  have hdiag := h.diag_eq_zero hz1
  ext ⟨x, hx⟩
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
  constructor
  · intro hcen
    by_contra hnot
    have hv0 : v ≠ 0 := by
      rintro rfl
      apply hnot
      show nf z q s 0 ∈ Subgroup.zpowers z
      rw [nf_zero_vec]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
    obtain ⟨w, hw⟩ := hnd v hv0
    have hcw := congrArg Subtype.val (hcen ⟨nf z q 0 w, nf_mem_closure z q 0 w⟩)
    have hc := nf_mul_comm h hsymm hdiag s 0 v w
    have hb : bil c v w = 1 := (zmod_two_cases _).resolve_left hw
    rw [hb, val_one_two, pow_one] at hc
    have hcw' : nf z q 0 w * nf z q s v = nf z q s v * nf z q 0 w := hcw
    rw [← hcw'] at hc
    exact hz1 (mul_eq_left.1 hc.symm)
  · intro hmem y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : z ^ k = nf z q s v := hk
    apply Subtype.ext
    show (y : G) * nf z q s v = nf z q s v * y
    rw [← hk']
    exact ((commute_of_mem_closure h y.2).zpow_left k).symm.eq

theorem map_center_eq (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) :
    (Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))).map
        (Subgroup.closure (insert z (Set.range q))).subtype = Subgroup.zpowers z := by
  rw [center_eq h hinj hnd]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 (z_mem_closure z q))

theorem orderOf_eq_two (h : Rel z q c) (hz : z ≠ 1) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.z_sq) hz

theorem card_center (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) :
    Nat.card (Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) = 2 := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  have hle : Subgroup.zpowers z ≤ Subgroup.closure (insert z (Set.range q)) :=
    Subgroup.zpowers_le.2 (z_mem_closure z q)
  rw [center_eq h hinj hnd, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_zpowers, orderOf_eq_two h hz1]

theorem commutator_le_center (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (hnd : Nondegenerate c) :
    commutator ↥(Subgroup.closure (insert z (Set.range q))) ≤
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  have hsymm := h.symm_of_ne_one hz1
  have hdiag := h.diag_eq_zero hz1
  rw [_root_.commutator_def, Subgroup.commutator_le]
  rintro ⟨x, hx⟩ _ ⟨y, hy⟩ _
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
  obtain ⟨t, w, rfl⟩ := (mem_closure_iff h).1 hy
  rw [center_eq h hinj hnd, Subgroup.mem_subgroupOf]
  show ⁅nf z q s v, nf z q t w⁆ ∈ Subgroup.zpowers z
  rw [commutator_eq_zpow h hsymm hdiag]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _

theorem sq_mem_center (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) (x : ↥(Subgroup.closure (insert z (Set.range q)))) :
    x ^ 2 ∈ Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
  rw [center_eq h hinj hnd, Subgroup.mem_subgroupOf]
  show (nf z q s v) ^ 2 ∈ Subgroup.zpowers z
  rw [sq, nf_mul_self h]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _

theorem bil_eq_dotProduct (c : Fin n → Fin n → ZMod 2) (v w : Fin n → ZMod 2) :
    bil c v w = dotProduct v (Matrix.mulVec (Matrix.of c) w) := by
  simp [bil, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem Nondegenerate.of_matrix {c : Fin n → Fin n → ZMod 2}
    (hc : (Matrix.of c).Nondegenerate) : Nondegenerate c := by
  intro v hv
  by_contra hne
  refine hv (hc.eq_zero_of_ortho fun w => ?_)
  rw [← bil_eq_dotProduct]
  by_contra hw
  exact hne ⟨w, hw⟩

theorem Nondegenerate.of_det_ne_zero {c : Fin n → Fin n → ZMod 2}
    (hc : (Matrix.of c).det ≠ 0) : Nondegenerate c :=
  .of_matrix (Matrix.nondegenerate_of_det_ne_zero hc)

theorem Nondegenerate.of_mul_eq_one {c : Fin n → Fin n → ZMod 2}
    {d : Matrix (Fin n) (Fin n) (ZMod 2)} (hcd : Matrix.of c * d = 1) : Nondegenerate c :=
  .of_det_ne_zero fun hdet => by
    have := congrArg Matrix.det hcd
    rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

@[expose] def thetaFun (z : G) (q : Fin n → G) (v : Fin n → ZMod 2) :
    ↥(Subgroup.closure (insert z (Set.range q))) ⧸
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) :=
  QuotientGroup.mk ⟨nf z q 0 v, nf_mem_closure z q 0 v⟩

theorem zpow_mem_center (h : Rel z q c) (b : ℕ) :
    (⟨z ^ b, pow_mem (z_mem_closure z q) b⟩ :
        ↥(Subgroup.closure (insert z (Set.range q)))) ∈
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact ((commute_of_mem_closure h y.2).pow_left b).symm.eq

theorem thetaFun_add (h : Rel z q c) (v w : Fin n → ZMod 2) :
    thetaFun z q (v + w) = thetaFun z q v * thetaFun z q w := by
  unfold thetaFun
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
  have e : nf z q 0 v * nf z q 0 w = nf z q 0 (v + w) * z ^ (collect c v w).val := by
    rw [nf_mul_nf h, nf_mul_zpow h]
    simp
  have e2 : ((⟨nf z q 0 (v + w), nf_mem_closure z q 0 (v + w)⟩ :
      ↥(Subgroup.closure (insert z (Set.range q))))⁻¹ *
      (⟨nf z q 0 v, nf_mem_closure z q 0 v⟩ * ⟨nf z q 0 w, nf_mem_closure z q 0 w⟩)) =
      ⟨z ^ (collect c v w).val, pow_mem (z_mem_closure z q) _⟩ := by
    apply Subtype.ext
    show (nf z q 0 (v + w))⁻¹ * (nf z q 0 v * nf z q 0 w) = z ^ (collect c v w).val
    rw [e, inv_mul_cancel_left]
  rw [e2]
  exact zpow_mem_center h _

theorem thetaFun_zero (z : G) (q : Fin n → G) : thetaFun z q 0 = 1 := by
  unfold thetaFun
  rw [QuotientGroup.eq_one_iff]
  have : (⟨nf z q 0 0, nf_mem_closure z q 0 0⟩ :
      ↥(Subgroup.closure (insert z (Set.range q)))) = 1 := Subtype.ext (nf_zero_zero z q)
  rw [this]
  exact one_mem _

@[expose] def theta (h : Rel z q c) :
    Multiplicative (Fin n → ZMod 2) →*
      ↥(Subgroup.closure (insert z (Set.range q))) ⧸
        Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) where
  toFun v := thetaFun z q (Multiplicative.toAdd v)
  map_one' := thetaFun_zero z q
  map_mul' _ _ := thetaFun_add h _ _

theorem theta_apply_eq_mk (h : Rel z q c) (s : ZMod 2) (v : Fin n → ZMod 2) :
    theta h (Multiplicative.ofAdd v) =
      (QuotientGroup.mk ⟨nf z q s v, nf_mem_closure z q s v⟩ :
        ↥(Subgroup.closure (insert z (Set.range q))) ⧸
          Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) := by
  show thetaFun z q v = _
  unfold thetaFun
  rw [QuotientGroup.eq]
  have e : (⟨nf z q 0 v, nf_mem_closure z q 0 v⟩ :
      ↥(Subgroup.closure (insert z (Set.range q))))⁻¹ * ⟨nf z q s v, nf_mem_closure z q s v⟩ =
      ⟨z ^ s.val, pow_mem (z_mem_closure z q) _⟩ := by
    apply Subtype.ext
    show (nf z q 0 v)⁻¹ * nf z q s v = z ^ s.val
    have e1 : nf z q s v = nf z q 0 v * z ^ s.val := by
      rw [nf_mul_zpow h, zero_add]
    rw [e1, inv_mul_cancel_left]
  rw [e]
  exact zpow_mem_center h _

theorem theta_single (h : Rel z q c) (j : Fin n) :
    theta h (Multiplicative.ofAdd (Pi.single j 1)) =
      (QuotientGroup.mk ⟨q j, q_mem_closure z q j⟩ :
        ↥(Subgroup.closure (insert z (Set.range q))) ⧸
          Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) := by
  rw [theta_apply_eq_mk h 0 (Pi.single j 1)]
  exact congrArg QuotientGroup.mk (Subtype.ext (nf_single z q j))

theorem theta_surjective (h : Rel z q c) : Function.Surjective (theta h) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨x, hx⟩ := a
    obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hx
    exact ⟨Multiplicative.ofAdd v, theta_apply_eq_mk h s v⟩

theorem theta_injective (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) : Function.Injective (theta h) := by
  intro a b hab
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective a
  obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective b
  have hab' : thetaFun z q v = thetaFun z q w := hab
  unfold thetaFun at hab'
  rw [QuotientGroup.eq, center_eq h hinj hnd, Subgroup.mem_subgroupOf] at hab'
  obtain ⟨β, hβ⟩ := (mem_zpowers_iff_exists h).1 hab'
  have hβ' : z ^ β.val = (nf z q 0 v)⁻¹ * nf z q 0 w := hβ
  have h2 : nf z q β v = nf z q 0 w := by
    have e := nf_mul_zpow h 0 β v
    rw [zero_add] at e
    rw [← e, hβ', mul_inv_cancel_left]
  exact congrArg Multiplicative.ofAdd (eq_of_nf_eq hinj h2).2

@[expose] def thetaEquiv (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) :
    Multiplicative (Fin n → ZMod 2) ≃*
      ↥(Subgroup.closure (insert z (Set.range q))) ⧸
        Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))) :=
  MulEquiv.ofBijective (theta h) ⟨theta_injective h hinj hnd, theta_surjective h⟩

@[expose] def thetaAddEquiv (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) :
    (Fin n → ZMod 2) ≃+
      Additive (↥(Subgroup.closure (insert z (Set.range q))) ⧸
        Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) :=
  MulEquiv.toAdditiveRight (thetaEquiv h hinj hnd)

theorem thetaEquiv_apply (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    (hnd : Nondegenerate c) (v : Fin n → ZMod 2) :
    thetaEquiv h hinj hnd (Multiplicative.ofAdd v) =
      QuotientGroup.mk ⟨nf z q 0 v, nf_mem_closure z q 0 v⟩ :=
  rfl

theorem card_quotient_center (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (hnd : Nondegenerate c) :
    Nat.card (↥(Subgroup.closure (insert z (Set.range q))) ⧸
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) = 2 ^ n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))))
  rw [card_closure h hinj, card_center h hinj hnd, pow_succ] at h1
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm

theorem isElementaryAbelian_quotient_center (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (hnd : Nondegenerate c) :
    IsElementaryAbelian 2 (↥(Subgroup.closure (insert z (Set.range q))) ⧸
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) := by
  have hcomm : IsMulCommutative (↥(Subgroup.closure (insert z (Set.range q))) ⧸
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center ↥(Subgroup.closure (insert z (Set.range q))))).2
      (commutator_le_center h hinj hnd)
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact sq_mem_center h hinj hnd a

theorem nontrivial_quotient_center (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (hnd : Nondegenerate c)
    (hn : 0 < n) :
    Nontrivial (↥(Subgroup.closure (insert z (Set.range q))) ⧸
      Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton, QuotientGroup.subsingleton_iff] at hcon
  have h1 : Nat.card (Subgroup.center ↥(Subgroup.closure (insert z (Set.range q)))) =
      Nat.card ↥(Subgroup.closure (insert z (Set.range q))) := by
    rw [hcon, Subgroup.card_top]
  rw [card_center h hinj hnd, card_closure h hinj] at h1
  have h2 : 2 ^ 1 < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem isExtraspecialPGroup (h : Rel z q c)
    (hinj : Function.Injective (Function.uncurry (nf z q))) (hnd : Nondegenerate c)
    (hn : 0 < n) : IsExtraspecialPGroup 2 (Subgroup.closure (insert z (Set.range q))) := by
  have : Finite ↥(Subgroup.closure (insert z (Set.range q))) := finite_closure h
  have hE : IsExtraspecial 2 ↥(Subgroup.closure (insert z (Set.range q))) :=
    { center_order_p := card_center h hinj hnd
      quotient_elementary_abelian := isElementaryAbelian_quotient_center h hinj hnd
      quotient_nontrivial := nontrivial_quotient_center h hinj hnd hn }
  exact IsExtraspecial.isExtraspecialPGroup (hE := hE)

end CFSG.Certificates.ExtraspecialNF
