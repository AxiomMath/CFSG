module

public import Certificates.Data.CFSGNative.D4Q2.Check
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [CharP K 2]

@[expose] def enc (ω : K) : ℕ → K
  | 1 => 1
  | 2 => ω
  | 3 => ω + 1
  | _ => 0

@[expose] def cidx : Fin 4 ⊕ Fin 4 → ℕ
  | .inl i => i
  | .inr i => i + 4

private def d4c_coord (k : ℕ) (hk : k < 8) : Fin 4 ⊕ Fin 4 :=
  if h : k < 4 then .inl ⟨k, h⟩ else .inr ⟨k - 4, by omega⟩

private lemma d4c_cidx_coord {k : ℕ} (hk : k < 8) : cidx (d4c_coord k hk) = k := by
  unfold d4c_coord
  split
  · rfl
  · simp [cidx]
    omega

@[expose] def vecC (ω : K) (v : ℕ) : Fin 4 ⊕ Fin 4 → K := fun x => enc ω (cd v (cidx x))

variable {ω : K}

omit [CharP K 2] in
private lemma d4c_omega_ne_zero (hω : ω * ω = ω + 1) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

omit [CharP K 2] in
private lemma d4c_omega_ne_one (hω : ω * ω = ω + 1) : ω ≠ 1 := by
  intro h
  rw [h] at hω
  simp at hω

private lemma d4c_omega_add_one_ne_zero (hω : ω * ω = ω + 1) : ω + 1 ≠ 0 := by
  intro h
  have h1 : ω = 1 := by
    calc ω = ω + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 0 + 1 := by rw [h]
      _ = 1 := zero_add 1
  exact d4c_omega_ne_one hω h1

omit [CharP K 2] in
private lemma d4c_omega_add_one_ne_one (hω : ω * ω = ω + 1) : ω + 1 ≠ 1 := by
  intro h
  have h1 : ω + 1 = 0 + 1 := by rw [h, zero_add]
  exact d4c_omega_ne_zero hω (add_right_cancel h1)

omit [CharP K 2] in
private lemma d4c_omega_ne_add_one : ω ≠ ω + 1 := by
  intro h
  have h1 : ω + 0 = ω + 1 := by rw [add_zero]; exact h
  exact one_ne_zero (add_left_cancel h1).symm

private lemma d4c_three_eq_one : (3 : K) = 1 := by
  rw [show (3 : K) = Nat.cast 3 from rfl, CharTwo.natCast_eq_mod]
  norm_num

private theorem d4c_exists_omega_aux [Fintype K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) : ∃ ω : K, ω * ω = ω + 1 ∧ σ ω = ω + 1 := by
  classical
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have hex : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
    by_contra h
    have hsub : (Finset.univ : Finset K) ⊆ ({0, 1} : Finset K) := by
      intro x _
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hx1 : x = 1 := by
          by_contra hx1
          exact h ⟨x, hx0, hx1⟩
        simp [hx1]
    have hle := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset K).card = 2 := Finset.card_pair zero_ne_one
    rw [Finset.card_univ, hcard, h2] at hle
    omega
  obtain ⟨w, hw0, hw1⟩ := hex
  have hw3 : w ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one w hw0
    rw [hcard] at h
    simpa using h
  have hroot : w ^ 2 + w + 1 = 0 := by
    have hfac : (w - 1) * (w ^ 2 + w + 1) = 0 := by
      have hcube : w ^ 3 - 1 = 0 := by rw [hw3, sub_self]
      rw [← hcube]
      ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hw1)
  have hw : w * w = w + 1 := by
    have h' : w ^ 2 + (w + 1) = 0 := by linear_combination hroot
    have hneg : w ^ 2 = -(w + 1) := eq_neg_of_add_eq_zero_left h'
    rw [CharTwo.neg_eq] at hneg
    simpa [pow_two] using hneg
  let g : Fin 4 → K := fun i => if i = 0 then 0 else if i = 1 then 1 else
    if i = 2 then w else w + 1
  have hg : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [g] at h ⊢ <;>
      first
      | rfl
      | exact (d4c_omega_ne_zero hw h).elim
      | exact (d4c_omega_ne_zero hw h.symm).elim
      | exact (d4c_omega_ne_one hw h).elim
      | exact (d4c_omega_ne_one hw h.symm).elim
      | exact (d4c_omega_add_one_ne_zero hw h).elim
      | exact (d4c_omega_add_one_ne_zero hw h.symm).elim
  have hset : (Finset.univ.image g) = ({0, 1, w, w + 1} : Finset K) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [g]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by simp [g]⟩
      · exact ⟨1, by simp [g]⟩
      · exact ⟨2, by simp [g]⟩
      · exact ⟨3, by simp [g]⟩
  have hfour : ({0, 1, w, w + 1} : Finset K) = Finset.univ := by
    rw [← hset]
    exact Finset.eq_univ_of_card _ (by
      rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin, hcard])
  have hσw_ne : σ w ≠ w := by
    intro hσw
    have hfix : ∀ x : K, σ x = x := by
      intro x
      have hxmem : x ∈ ({0, 1, w, w + 1} : Finset K) := by
        rw [hfour]; exact Finset.mem_univ x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      rcases hxmem with rfl | rfl | rfl | rfl
      · rw [map_zero]
      · rw [map_one]
      · exact hσw
      · rw [map_add, hσw, map_one]
    obtain ⟨c, hc⟩ := hσ.exists_ne
    exact hc (hfix c)
  have hmem : σ w ∈ ({0, 1, w, w + 1} : Finset K) := by
    rw [hfour]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h1 | hwsw | hwsw
  · exact absurd h0 (fun h => hw0 (σ.injective (by rw [h, map_zero])))
  · exact absurd h1 (fun h => hw1 (σ.injective (by rw [h, map_one])))
  · exact absurd hwsw hσw_ne
  · exact ⟨w, hw, hwsw⟩

theorem exists_omega [Finite K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) : ∃ ω : K, ω * ω = ω + 1 ∧ σ ω = ω + 1 := by
  classical
  exact @d4c_exists_omega_aux K _ _ (Fintype.ofFinite K) σ hσ hK

theorem cd_lt (v k : ℕ) : cd v k < 4 := by
  unfold cd
  exact Nat.mod_lt _ (by norm_num)

theorem cd_xor (u v k : ℕ) : cd (u ^^^ v) k = cd u k ^^^ cd v k := by
  unfold cd
  rw [Nat.shiftRight_xor_distrib]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.xor_mod_two_pow]

theorem mul4_lt {a b : ℕ} (ha : a < 4) (hb : b < 4) : mul4 a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem frob4_lt {a : ℕ} (ha : a < 4) : frob4 a < 4 := by
  interval_cases a <;> decide

private lemma d4c_xor2_lt {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.xor_lt_two_pow ha hb

private lemma d4c_xor4_lt {a b c d : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) :
    a ^^^ b ^^^ c ^^^ d < 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc) hd

private lemma d4c_smulC_eq_ofDigits (a v : ℕ) :
    smulC a v = Nat.ofDigits 4 [mul4 a (cd v 0), mul4 a (cd v 1), mul4 a (cd v 2),
      mul4 a (cd v 3), mul4 a (cd v 4), mul4 a (cd v 5), mul4 a (cd v 6),
      mul4 a (cd v 7)] := by
  simp [smulC, Nat.ofDigits]
  ring

private lemma d4c_digit_ofDigits {L : List ℕ} (hL : ∀ l ∈ L, l < 4) {k : ℕ}
    (hk : k < L.length) :
    Nat.ofDigits 4 L >>> (2 * k) % 4 = L.getD k 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (2 : ℕ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop k (by norm_num) L hL]
  rw [Nat.ofDigits_mod_eq_head!]
  have hdrop : L.drop k ≠ [] := by
    intro h
    have hlen := List.length_drop (l := L) (i := k)
    rw [h] at hlen
    simp at hlen
    omega
  have hhead : (L.drop k).head! = L.getD k 0 := by
    have hsome : (L.drop k).head? = some (L.getD k 0) := by
      rw [List.head?_drop, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hk]
      rfl
    rw [List.head!_of_head? hsome]
  rw [hhead]
  rw [List.getD_eq_getElem L 0 hk, Nat.mod_eq_of_lt (hL _ (List.getElem_mem hk))]

theorem cd_smulC {a : ℕ} (ha : a < 4) (v : ℕ) {k : ℕ} (hk : k < 8) :
    cd (smulC a v) k = mul4 a (cd v k) := by
  rw [d4c_smulC_eq_ofDigits, cd]
  have hlen : ([mul4 a (cd v 0), mul4 a (cd v 1), mul4 a (cd v 2), mul4 a (cd v 3),
      mul4 a (cd v 4), mul4 a (cd v 5), mul4 a (cd v 6),
      mul4 a (cd v 7)] : List ℕ).length = 8 := rfl
  rw [d4c_digit_ofDigits]
  · interval_cases k <;> simp
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mul4_lt ha (cd_lt v _)
  · omega

theorem smulC_lt {a : ℕ} (ha : a < 4) (v : ℕ) : smulC a v < 65536 := by
  rw [d4c_smulC_eq_ofDigits]
  have h := Nat.ofDigits_lt_base_pow_length (b := 4) (by norm_num)
    (l := [mul4 a (cd v 0), mul4 a (cd v 1), mul4 a (cd v 2), mul4 a (cd v 3),
      mul4 a (cd v 4), mul4 a (cd v 5), mul4 a (cd v 6), mul4 a (cd v 7)])
    (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact mul4_lt ha (cd_lt v _))
  simpa using h

theorem xor_lt {u v : ℕ} (hu : u < 65536) (hv : v < 65536) : u ^^^ v < 65536 := by
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num] at hu hv ⊢
  exact Nat.xor_lt_two_pow hu hv

theorem quadC_lt (v : ℕ) : quadC v < 4 := by
  unfold quadC
  exact d4c_xor4_lt (mul4_lt (cd_lt v 0) (cd_lt v 4))
    (mul4_lt (cd_lt v 1) (cd_lt v 5)) (mul4_lt (cd_lt v 2) (cd_lt v 6))
    (mul4_lt (cd_lt v 3) (cd_lt v 7))

theorem polarC_lt (u v : ℕ) : polarC u v < 4 := by
  unfold polarC
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact mul4_lt (cd_lt u _) (cd_lt v _)

theorem hermC_lt (u v : ℕ) : hermC u v < 4 := by
  unfold hermC
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact mul4_lt (cd_lt u _) (frob4_lt (cd_lt v _))

private lemma d4c_cd_testBit {x k b : ℕ} (hb : b < 2) :
    Nat.testBit (cd x k) b = Nat.testBit x (2 * k + b) := by
  rw [cd, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.testBit_mod_two_pow]
  simp [hb, Nat.testBit_shiftRight]

theorem eq_of_cd_eq {u v : ℕ} (hu : u < 65536) (hv : v < 65536) (h : ∀ k < 8, cd u k = cd v k) :
    u = v := by
  refine Nat.eq_iff_testBit_eq.mpr fun i => ?_
  by_cases hi : i < 16
  · obtain ⟨k, b, rfl, hk, hb⟩ : ∃ k b, i = 2 * k + b ∧ k < 8 ∧ b < 2 := by
      refine ⟨i / 2, i % 2, ?_, by omega, Nat.mod_lt _ (by norm_num)⟩
      omega
    rw [← d4c_cd_testBit (x := u) hb, ← d4c_cd_testBit (x := v) hb, h k hk]
  · have hu16 : u < 2 ^ 16 := by norm_num at hu ⊢; exact hu
    have hv16 : v < 2 ^ 16 := by norm_num at hv ⊢; exact hv
    have hle : 16 ≤ i := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu16 (Nat.pow_le_pow_right (by norm_num) hle)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv16 (Nat.pow_le_pow_right (by norm_num) hle))]

theorem enc_xor {a b : ℕ} (ha : a < 4) (hb : b < 4) : enc ω (a ^^^ b) = enc ω a + enc ω b := by
  interval_cases a <;> interval_cases b <;> simp [enc] <;> ring_nf <;>
    simp [CharTwo.two_eq_zero]

theorem enc_frob4 {σ : K ≃+* K} (hσω : σ ω = ω + 1) {a : ℕ} (ha : a < 4) :
    enc ω (frob4 a) = σ (enc ω a) := by
  interval_cases a
  all_goals simp [enc, frob4, hσω, map_add]
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

private lemma d4c_sum_enc_four {a b c d : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4)
    (hd : d < 4) :
    enc ω a + enc ω b + enc ω c + enc ω d = enc ω (a ^^^ b ^^^ c ^^^ d) := by
  rw [← enc_xor ha hb, ← enc_xor (d4c_xor2_lt ha hb) hc,
    ← enc_xor (d4c_xor2_lt (d4c_xor2_lt ha hb) hc) hd]

private lemma d4c_sum_enc_eight {a b c d e f g h : ℕ}
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) (hf : f < 4)
    (hg : g < 4) (hh : h < 4) :
    enc ω a + enc ω b + enc ω c + enc ω d + enc ω e + enc ω f + enc ω g + enc ω h =
      enc ω (a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f ^^^ g ^^^ h) := by
  rw [← enc_xor ha hb, ← enc_xor (d4c_xor2_lt ha hb) hc,
    ← enc_xor (d4c_xor2_lt (d4c_xor2_lt ha hb) hc) hd,
    ← enc_xor (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt ha hb) hc) hd) he,
    ← enc_xor (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt ha hb) hc) hd) he) hf,
    ← enc_xor
      (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt ha hb) hc) hd) he) hf) hg,
    ← enc_xor
      (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt (d4c_xor2_lt ha hb)
        hc) hd) he) hf) hg) hh]

section Omega

variable (hω : ω * ω = ω + 1)
include hω

theorem enc_mul4 {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    enc ω (mul4 a b) = enc ω a * enc ω b := by
  have hω' : ω ^ 2 = ω + 1 := by rw [pow_two]; exact hω
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  interval_cases a <;> interval_cases b <;>
    simp only [enc, mul4] <;>
    ring_nf
  all_goals try rw [hω']
  all_goals ring_nf
  all_goals simp [h2, d4c_three_eq_one]

theorem enc_injOn {a b : ℕ} (ha : a < 4) (hb : b < 4) (h : enc ω a = enc ω b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    simp [enc] at h ⊢ <;>
    first
    | rfl
    | exact (d4c_omega_ne_zero hω h).elim
    | exact (d4c_omega_ne_zero hω h.symm).elim
    | exact (one_ne_zero h).elim
    | exact (one_ne_zero h.symm).elim
    | exact (d4c_omega_ne_one hω h).elim
    | exact (d4c_omega_ne_one hω h.symm).elim
    | exact (d4c_omega_add_one_ne_zero hω h).elim
    | exact (d4c_omega_add_one_ne_zero hω h.symm).elim

theorem enc_eq_zero_iff {a : ℕ} (ha : a < 4) : enc ω a = 0 ↔ a = 0 := by
  constructor
  · intro h
    interval_cases a <;> simp [enc] at h ⊢ <;>
      first
      | rfl
      | exact (one_ne_zero h).elim
      | exact (d4c_omega_ne_zero hω h).elim
      | exact (d4c_omega_add_one_ne_zero hω h).elim
  · rintro rfl; rfl

omit hω in
private theorem d4c_exists_enc_aux [Fintype K] (hω' : ω * ω = ω + 1)
    (hK : Nat.card K = 4) (x : K) : ∃ a < 4, enc ω a = x := by
  classical
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  let f : Fin 4 → K := fun a => enc ω a
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact enc_injOn hω' a.isLt b.isLt h
  have himg : (Finset.univ.image f).card = 4 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have huniv : (Finset.univ.image f) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [himg, hcard])
  have hx : x ∈ (Finset.univ.image f) := by rw [huniv]; exact Finset.mem_univ x
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx
  exact ⟨a, a.isLt, ha⟩


theorem exists_enc [Finite K] (hK : Nat.card K = 4) (x : K) : ∃ a < 4, enc ω a = x := by
  classical
  exact @d4c_exists_enc_aux K _ _ ω (Fintype.ofFinite K) hω hK x

private lemma d4c_mul4_comm {a b : ℕ} (ha : a < 4) (hb : b < 4) : mul4 a b = mul4 b a := by
  apply enc_injOn hω (mul4_lt ha hb) (mul4_lt hb ha)
  rw [enc_mul4 hω ha hb, enc_mul4 hω hb ha, mul_comm]

theorem vecC_injOn {u v : ℕ} (hu : u < 65536) (hv : v < 65536) (h : vecC ω u = vecC ω v) :
    u = v := by
  apply eq_of_cd_eq hu hv
  intro k hk
  have hc := congrFun h (d4c_coord k hk)
  simp only [vecC, d4c_cidx_coord hk] at hc
  exact enc_injOn hω (cd_lt u k) (cd_lt v k) hc

theorem vecC_eq_zero_iff {v : ℕ} (hv : v < 65536) : vecC ω v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply eq_of_cd_eq hv (by norm_num : 0 < 65536)
    intro k hk
    have hc := congrFun h (d4c_coord k hk)
    simp only [vecC, d4c_cidx_coord hk, Pi.zero_apply] at hc
    have hz : cd v k = 0 := (enc_eq_zero_iff hω (cd_lt v k)).mp hc
    rw [hz]
    simp [cd]
  · rintro rfl
    funext x
    simp [vecC, cd, enc]

theorem exists_vecC [Finite K] (hK : Nat.card K = 4) (w : Fin 4 ⊕ Fin 4 → K) :
    ∃ v < 65536, vecC ω v = w := by
  classical
  choose a ha hcode using fun x => exists_enc hω hK (w x)
  let L : List ℕ := [a (.inl 0), a (.inl 1), a (.inl 2), a (.inl 3),
    a (.inr 0), a (.inr 1), a (.inr 2), a (.inr 3)]
  have hLt : ∀ l ∈ L, l < 4 := by
    intro l hl
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ha _
  let v := Nat.ofDigits 4 L
  have hvlen : L.length = 8 := rfl
  have hv : v < 65536 := by
    have h := Nat.ofDigits_lt_base_pow_length (b := 4) (by norm_num) hLt
    rw [hvlen] at h
    norm_num at h ⊢
    exact h
  refine ⟨v, hv, ?_⟩
  funext x
  have hk : cidx x < 8 := by cases x <;> simp [cidx] <;> omega
  have hcd : cd v (cidx x) = a x := by
    have hdigit := d4c_digit_ofDigits (L := L) hLt (k := cidx x) (by rw [hvlen]; exact hk)
    have h' : cd v (cidx x) = L.getD (cidx x) 0 := by
      simpa [cd, v] using hdigit
    rw [h']
    cases x with
    | inl i => fin_cases i <;> simp [L, cidx]
    | inr i => fin_cases i <;> simp [L, cidx]
  rw [show vecC ω v x = enc ω (cd v (cidx x)) from rfl, hcd, hcode x]

theorem vecC_smulC {a : ℕ} (ha : a < 4) (v : ℕ) :
    vecC ω (smulC a v) = enc ω a • vecC ω v := by
  funext x
  have hk : cidx x < 8 := by cases x <;> simp [cidx] <;> omega
  simp only [vecC, Pi.smul_apply, smul_eq_mul]
  rw [cd_smulC ha v hk, ← enc_mul4 hω ha (cd_lt v (cidx x))]

theorem quadPlus_vecC (v : ℕ) : quadPlus 4 K (vecC ω v) = enc ω (quadC v) := by
  rw [quadPlus_apply]
  have hterm : ∀ i : Fin 4, vecC ω v (.inl i) * vecC ω v (.inr i) =
      enc ω (mul4 (cd v i) (cd v ((i : ℕ) + 4))) := by
    intro i
    simp only [vecC, cidx]
    rw [← enc_mul4 hω (cd_lt v i) (cd_lt v ((i : ℕ) + 4))]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Fin.sum_univ_four]
  norm_num
  rw [d4c_sum_enc_four (mul4_lt (cd_lt v 0) (cd_lt v 4))
    (mul4_lt (cd_lt v 1) (cd_lt v 5)) (mul4_lt (cd_lt v 2) (cd_lt v 6))
    (mul4_lt (cd_lt v 3) (cd_lt v 7))]
  rfl

theorem polar_vecC (u v : ℕ) :
    polar (quadPlus 4 K) (vecC ω u) (vecC ω v) = enc ω (polarC u v) := by
  rw [polar_quadPlus]
  have hterm : ∀ i : Fin 4,
      vecC ω u (.inl i) * vecC ω v (.inr i) + vecC ω v (.inl i) * vecC ω u (.inr i) =
      enc ω (mul4 (cd u i) (cd v ((i : ℕ) + 4))) +
        enc ω (mul4 (cd v i) (cd u ((i : ℕ) + 4))) := by
    intro i
    simp only [vecC, cidx]
    rw [← enc_mul4 hω (cd_lt u i) (cd_lt v ((i : ℕ) + 4)),
      ← enc_mul4 hω (cd_lt v i) (cd_lt u ((i : ℕ) + 4))]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Fin.sum_univ_four]
  norm_num
  rw [← enc_xor (mul4_lt (cd_lt u 0) (cd_lt v 4))
      (mul4_lt (cd_lt v 0) (cd_lt u 4)),
    ← enc_xor (mul4_lt (cd_lt u 1) (cd_lt v 5))
      (mul4_lt (cd_lt v 1) (cd_lt u 5)),
    ← enc_xor (mul4_lt (cd_lt u 2) (cd_lt v 6))
      (mul4_lt (cd_lt v 2) (cd_lt u 6)),
    ← enc_xor (mul4_lt (cd_lt u 3) (cd_lt v 7))
      (mul4_lt (cd_lt v 3) (cd_lt u 7))]
  rw [d4c_sum_enc_four
    (d4c_xor2_lt (mul4_lt (cd_lt u 0) (cd_lt v 4)) (mul4_lt (cd_lt v 0) (cd_lt u 4)))
    (d4c_xor2_lt (mul4_lt (cd_lt u 1) (cd_lt v 5)) (mul4_lt (cd_lt v 1) (cd_lt u 5)))
    (d4c_xor2_lt (mul4_lt (cd_lt u 2) (cd_lt v 6)) (mul4_lt (cd_lt v 2) (cd_lt u 6)))
    (d4c_xor2_lt (mul4_lt (cd_lt u 3) (cd_lt v 7)) (mul4_lt (cd_lt v 3) (cd_lt u 7)))]
  congr 1
  rw [polarC]
  rw [d4c_mul4_comm hω (cd_lt v 0) (cd_lt u 4),
    d4c_mul4_comm hω (cd_lt v 1) (cd_lt u 5),
    d4c_mul4_comm hω (cd_lt v 2) (cd_lt u 6),
    d4c_mul4_comm hω (cd_lt v 3) (cd_lt u 7)]
  simp only [Nat.xor_assoc]

theorem flipHerm_vecC {σ : K ≃+* K} (hσω : σ ω = ω + 1) (u v : ℕ) :
    flipHerm σ (vecC ω u) (vecC ω v) = enc ω (hermC u v) := by
  rw [flipHerm_apply]
  have hterm : ∀ i : Fin 4,
      vecC ω u (.inl i) * σ (vecC ω v (.inl i)) +
        vecC ω u (.inr i) * σ (vecC ω v (.inr i)) =
      enc ω (mul4 (cd u i) (frob4 (cd v i))) +
        enc ω (mul4 (cd u ((i : ℕ) + 4)) (frob4 (cd v ((i : ℕ) + 4)))) := by
    intro i
    simp only [vecC, cidx]
    rw [← enc_frob4 hσω (cd_lt v i),
      ← enc_frob4 hσω (cd_lt v ((i : ℕ) + 4)),
      ← enc_mul4 hω (cd_lt u i) (frob4_lt (cd_lt v i)),
      ← enc_mul4 hω (cd_lt u ((i : ℕ) + 4)) (frob4_lt (cd_lt v ((i : ℕ) + 4)))]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Fin.sum_univ_four]
  norm_num
  rw [show (enc ω (mul4 (cd u 0) (frob4 (cd v 0))) +
        enc ω (mul4 (cd u 4) (frob4 (cd v 4)))) +
        (enc ω (mul4 (cd u 1) (frob4 (cd v 1))) +
        enc ω (mul4 (cd u 5) (frob4 (cd v 5)))) +
        (enc ω (mul4 (cd u 2) (frob4 (cd v 2))) +
        enc ω (mul4 (cd u 6) (frob4 (cd v 6)))) +
        (enc ω (mul4 (cd u 3) (frob4 (cd v 3))) +
        enc ω (mul4 (cd u 7) (frob4 (cd v 7)))) =
      enc ω (mul4 (cd u 0) (frob4 (cd v 0))) +
        enc ω (mul4 (cd u 1) (frob4 (cd v 1))) +
        enc ω (mul4 (cd u 2) (frob4 (cd v 2))) +
        enc ω (mul4 (cd u 3) (frob4 (cd v 3))) +
        enc ω (mul4 (cd u 4) (frob4 (cd v 4))) +
        enc ω (mul4 (cd u 5) (frob4 (cd v 5))) +
        enc ω (mul4 (cd u 6) (frob4 (cd v 6))) +
        enc ω (mul4 (cd u 7) (frob4 (cd v 7))) by ring]
  rw [d4c_sum_enc_eight (mul4_lt (cd_lt u 0) (frob4_lt (cd_lt v 0)))
    (mul4_lt (cd_lt u 1) (frob4_lt (cd_lt v 1)))
    (mul4_lt (cd_lt u 2) (frob4_lt (cd_lt v 2)))
    (mul4_lt (cd_lt u 3) (frob4_lt (cd_lt v 3)))
    (mul4_lt (cd_lt u 4) (frob4_lt (cd_lt v 4)))
    (mul4_lt (cd_lt u 5) (frob4_lt (cd_lt v 5)))
    (mul4_lt (cd_lt u 6) (frob4_lt (cd_lt v 6)))
    (mul4_lt (cd_lt u 7) (frob4_lt (cd_lt v 7)))]
  rfl

end Omega

theorem vecC_xor (u v : ℕ) : vecC ω (u ^^^ v) = vecC ω u + vecC ω v := by
  funext x
  simp only [vecC, Pi.add_apply]
  rw [cd_xor, enc_xor (cd_lt u (cidx x)) (cd_lt v (cidx x))]

end CFSG.ClassicalInvolution.PhanDn.D4Q2
