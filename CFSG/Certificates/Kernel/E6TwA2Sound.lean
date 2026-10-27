module

public import Certificates.Data.Kernel.E6TwA2.Defs
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

namespace CFSG.KC.E6TwA2

open Certificates.E6TwA2K CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.Steinberg.Adjoint

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem letN_eq {α : Type} (y : ℕ) (k : ℕ → α) : letN y k = k y := by cases y <;> rfl

theorem forceN_eq {α : Type} (y : ℕ) (k : ℕ → α) : forceN y k = k y := by
  unfold forceN
  cases Nat.beq y 0 <;> rfl

theorem allL_eq_true {l : List ℕ} {f : ℕ → Bool} : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons x l ih =>
    change andB (f x) (allL l f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem mem_of_anyL {l : List ℕ} {m : ℕ} (h : anyL l (fun r => Nat.beq m r) = true) : m ∈ l := by
  induction l with
  | nil => exact absurd h (by change ¬ (false = true); decide)
  | cons x l ih =>
    change orB (Nat.beq m x) (anyL l fun r => Nat.beq m r) = true at h
    rw [orB_eq, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with h | h
    · rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem bitB_eq (x n : ℕ) : bitB x n = x.testBit n := by
  change Nat.blt 0 (x &&& 1 <<< n) = _
  rw [Nat.one_shiftLeft]
  have key : ∀ i, (x &&& 2 ^ n).testBit i = (decide (n = i) && x.testBit n) := by
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases h : n = i
    · subst h
      simp
    · simp [h]
  cases h : x.testBit n
  · have h0 : x &&& 2 ^ n = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [key, Nat.zero_testBit, h, Bool.and_false]
    rw [h0]
    rfl
  · have hpos : 0 < x &&& 2 ^ n := Nat.pos_of_ne_zero fun h0 => by
      have := key n
      rw [h0, Nat.zero_testBit, h] at this
      simp at this
    simpa using hpos

theorem hex_eq (c j : ℕ) : (c >>> (4 * j)) &&& 15 = c / 16 ^ j % 16 := by
  change (c >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem kd_pk_tab : ∀ t < 729,
    kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 0 =
        t / 1 % 3 ∧
      kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 2 =
        t / 3 % 3 ∧
      kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 4 =
        t / 9 % 3 ∧
      kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 6 =
        t / 27 % 3 ∧
      kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 8 =
        t / 81 % 3 ∧
      kd (pk (t / 1 % 3) (t / 3 % 3) (t / 9 % 3) (t / 27 % 3) (t / 81 % 3) (t / 243 % 3)) 10 =
        t / 243 % 3 := by
  decide +kernel

theorem kd_pk_all {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 3) (h1 : a1 < 3) (h2 : a2 < 3)
    (h3 : a3 < 3) (h4 : a4 < 3) (h5 : a5 < 3) :
    kd (pk a0 a1 a2 a3 a4 a5) 0 = a0 ∧ kd (pk a0 a1 a2 a3 a4 a5) 2 = a1 ∧
      kd (pk a0 a1 a2 a3 a4 a5) 4 = a2 ∧ kd (pk a0 a1 a2 a3 a4 a5) 6 = a3 ∧
      kd (pk a0 a1 a2 a3 a4 a5) 8 = a4 ∧ kd (pk a0 a1 a2 a3 a4 a5) 10 = a5 := by
  have e0 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 1 % 3 = a0 := by omega
  have e1 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 3 % 3 = a1 := by omega
  have e2 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 9 % 3 = a2 := by omega
  have e3 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 27 % 3 = a3 := by omega
  have e4 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 81 % 3 = a4 := by omega
  have e5 : (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) / 243 % 3 = a5 := by omega
  have ht := kd_pk_tab (a0 + 3 * a1 + 9 * a2 + 27 * a3 + 81 * a4 + 243 * a5) (by omega)
  rw [e0, e1, e2, e3, e4, e5] at ht
  exact ht

theorem pr_def (c v : ℕ) : pr c v = (c / 1 % 3 * kd v 0 + (c / 3 % 3 * kd v 2 +
    (c / 9 % 3 * kd v 4 + (c / 27 % 3 * kd v 6 + (c / 81 % 3 * kd v 8 +
      c / 243 % 3 * kd v 10))))) % 3 := rfl

theorem pr_sound {c : ℕ} {a : Fin 6 → ℕ} {u : Fin 6 → ℤ} (ha : ∀ j, a j < 3)
    (hu : ∀ j, ((u j : ℤ) : ZMod 3) = ((a j : ℕ) : ZMod 3))
    (h : pr c (pk (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)) = 0) :
    triPairing (τ := .E6) (vec3OfIndex c) u = 0 := by
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := kd_pk_all (ha 0) (ha 1) (ha 2) (ha 3) (ha 4) (ha 5)
  rw [pr_def, k0, k1, k2, k3, k4, k5] at h
  have hz := congrArg (Nat.cast : ℕ → ZMod 3) h
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_zero] at hz
  have e : triPairing (τ := .E6) (vec3OfIndex c) u =
      ∑ j : Fin 6, vec3OfIndex (τ := .E6) c j * ((a j : ℕ) : ZMod 3) := by
    unfold triPairing
    exact Finset.sum_congr rfl fun j _ => by rw [hu j]
  rw [e, Fin.sum_univ_six]
  simp only [vec3OfIndex, ZMod.natCast_mod]
  norm_num at hz ⊢
  linear_combination hz

@[expose] def digLift (n : ℕ) : Fin Tag.E6.rank → ℤ := fun j => ((n / 3 ^ (j : ℕ) % 3 : ℕ) : ℤ)

theorem rr_def (c s : ℕ) : rr c s = (((c >>> s) &&& 15) + 1) % 3 := rfl

theorem rr_lt (c s : ℕ) : rr c s < 3 := Nat.mod_lt _ (by norm_num)

theorem cast_eq_of_dvd {a : ℤ} {b : ℕ} (h : (3 : ℤ) ∣ (b : ℤ) - a) :
    ((a : ℤ) : ZMod 3) = ((b : ℕ) : ZMod 3) := by
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact_mod_cast h

theorem rr_dvd {c s : ℕ} (j : Fin 6) (hs : s = 4 * j) :
    (3 : ℤ) ∣ ((rr c s : ℕ) : ℤ) - decodeVec (τ := .E6) c j := by
  subst hs
  rw [rr_def, hex_eq]
  change (3 : ℤ) ∣ (((c / 16 ^ (j : ℕ) % 16 + 1) % 3 : ℕ) : ℤ) -
    (((c / 16 ^ (j : ℕ) % 16 : ℕ) : ℤ) - 8)
  generalize c / 16 ^ (j : ℕ) % 16 = h
  omega

theorem decodeVec_cast (c : ℕ) (j : Fin 6) :
    ((decodeVec (τ := .E6) c j : ℤ) : ZMod 3) = ((rr c (4 * j) : ℕ) : ZMod 3) :=
  cast_eq_of_dvd (rr_dvd j rfl)

theorem dd_lt (a b : ℕ) : dd a b < 3 := Nat.mod_lt _ (by norm_num)

theorem pr_kvR {c c1 : ℕ} (h : pr c (kvR c1) = 0) :
    triPairing (τ := .E6) (vec3OfIndex c) (decodeVec c1) = 0 :=
  pr_sound (a := fun j => rr c1 (4 * j)) (u := decodeVec (τ := .E6) c1) (fun _ => rr_lt _ _)
    (decodeVec_cast c1) h

theorem pr_kvD {c c1 c2 : ℕ} (h : pr c (kvD c1 c2) = 0) :
    triPairing (τ := .E6) (vec3OfIndex c) (decodeVec c1 - decodeVec c2) = 0 :=
  pr_sound (a := fun j => dd (rr c1 (4 * j)) (rr c2 (4 * j)))
    (u := decodeVec (τ := .E6) c1 - decodeVec c2) (fun _ => dd_lt _ _)
    (fun j => by
      change ((decodeVec (τ := .E6) c1 j - decodeVec (τ := .E6) c2 j : ℤ) : ZMod 3) = _
      refine cast_eq_of_dvd ?_
      have h1 := rr_dvd (c := c1) j rfl
      have h2 := rr_dvd (c := c2) j rfl
      change (3 : ℤ) ∣ (((rr c1 (4 * j) + 2 * rr c2 (4 * j)) % 3 : ℕ) : ℤ) - _
      omega) h

theorem pr_kvT {c n : ℕ} (h : pr c (kvT n) = 0) :
    triPairing (τ := .E6) (vec3OfIndex c) (digLift n) = 0 :=
  pr_sound (a := fun j => n / 3 ^ (j : ℕ) % 3) (u := digLift n)
    (fun _ => Nat.mod_lt _ (by norm_num)) (fun _ => Int.cast_natCast _) h

theorem formF_def (v c : ℕ) : formF v c =
    kd v 0 * (rr c 0 + rr c 8) + (kd v 2 * (rr c 4 + rr c 12) +
    (kd v 4 * (rr c 8 + (rr c 0 + rr c 12)) +
    (kd v 6 * (rr c 12 + (rr c 4 + (rr c 8 + rr c 16))) +
    (kd v 8 * (rr c 16 + (rr c 12 + rr c 20)) + kd v 10 * (rr c 20 + rr c 16))))) := rfl

theorem symmetrizedCartan_E6 (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
  simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem iform_E6 (x y : Fin 6 → ℤ) : iform (τ := .E6) x y =
    2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5) -
      (x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 + x 2 * y 3 + x 3 * y 2 + x 3 * y 4 +
        x 4 * y 3 + x 4 * y 5 + x 5 * y 4) := by
  unfold iform
  simp only [symmetrizedCartan_E6]
  change ∑ i : Fin 6, ∑ j : Fin 6, x i * Tag.cartanE 6 i j * y j = _
  simp only [Fin.sum_univ_six]
  simp [Tag.cartanE]
  ring

theorem iform_sound {n c : ℕ} (h : 0 < formF (kvT n) c % 3) :
    ¬ (3 : ℤ) ∣ iform (τ := .E6) (digLift n) (decodeVec c) := by
  intro hdvd
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := kd_pk_all (Nat.mod_lt (n / 1) (by norm_num))
    (Nat.mod_lt (n / 3) (by norm_num)) (Nat.mod_lt (n / 9) (by norm_num))
    (Nat.mod_lt (n / 27) (by norm_num)) (Nat.mod_lt (n / 81) (by norm_num))
    (Nat.mod_lt (n / 243) (by norm_num))
  have hk : kvT n = pk (n / 1 % 3) (n / 3 % 3) (n / 9 % 3) (n / 27 % 3) (n / 81 % 3)
      (n / 243 % 3) := rfl
  have hF : ((formF (kvT n) c : ℕ) : ℤ) =
      ((n / 1 % 3 : ℕ) : ℤ) * ((rr c 0 : ℕ) + (rr c 8 : ℕ)) +
      (((n / 3 % 3 : ℕ) : ℤ) * ((rr c 4 : ℕ) + (rr c 12 : ℕ)) +
      (((n / 9 % 3 : ℕ) : ℤ) * ((rr c 8 : ℕ) + ((rr c 0 : ℕ) + (rr c 12 : ℕ))) +
      (((n / 27 % 3 : ℕ) : ℤ) * ((rr c 12 : ℕ) + ((rr c 4 : ℕ) + ((rr c 8 : ℕ) + (rr c 16 : ℕ)))) +
      (((n / 81 % 3 : ℕ) : ℤ) * ((rr c 16 : ℕ) + ((rr c 12 : ℕ) + (rr c 20 : ℕ))) +
        ((n / 243 % 3 : ℕ) : ℤ) * ((rr c 20 : ℕ) + (rr c 16 : ℕ)))))) := by
    rw [formF_def, hk, k0, k1, k2, k3, k4, k5]
    simp only [Nat.cast_add, Nat.cast_mul]
  have hI := iform_E6 (digLift n) (decodeVec (τ := .E6) c)
  have x0 : digLift n (0 : Fin 6) = ((n / 1 % 3 : ℕ) : ℤ) := rfl
  have x1 : digLift n (1 : Fin 6) = ((n / 3 % 3 : ℕ) : ℤ) := rfl
  have x2 : digLift n (2 : Fin 6) = ((n / 9 % 3 : ℕ) : ℤ) := rfl
  have x3 : digLift n (3 : Fin 6) = ((n / 27 % 3 : ℕ) : ℤ) := rfl
  have x4 : digLift n (4 : Fin 6) = ((n / 81 % 3 : ℕ) : ℤ) := rfl
  have x5 : digLift n (5 : Fin 6) = ((n / 243 % 3 : ℕ) : ℤ) := rfl
  rw [x0, x1, x2, x3, x4, x5] at hI
  rw [hI] at hdvd
  obtain ⟨qi, hqi⟩ := hdvd
  obtain ⟨q0, hq0⟩ := rr_dvd (c := c) (s := 0) (0 : Fin 6) rfl
  obtain ⟨q1, hq1⟩ := rr_dvd (c := c) (s := 4) (1 : Fin 6) rfl
  obtain ⟨q2, hq2⟩ := rr_dvd (c := c) (s := 8) (2 : Fin 6) rfl
  obtain ⟨q3, hq3⟩ := rr_dvd (c := c) (s := 12) (3 : Fin 6) rfl
  obtain ⟨q4, hq4⟩ := rr_dvd (c := c) (s := 16) (4 : Fin 6) rfl
  obtain ⟨q5, hq5⟩ := rr_dvd (c := c) (s := 20) (5 : Fin 6) rfl
  have hF3 : (3 : ℤ) ∣ ((formF (kvT n) c : ℕ) : ℤ) := by
    refine ⟨-qi + (((n / 1 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (0 : Fin 6) +
      ((n / 3 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (1 : Fin 6) +
      ((n / 9 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (2 : Fin 6) +
      ((n / 27 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (3 : Fin 6) +
      ((n / 81 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (4 : Fin 6) +
      ((n / 243 % 3 : ℕ) : ℤ) * decodeVec (τ := .E6) c (5 : Fin 6)) +
      (((n / 1 % 3 : ℕ) : ℤ) * (q0 + q2) + ((n / 3 % 3 : ℕ) : ℤ) * (q1 + q3) +
        ((n / 9 % 3 : ℕ) : ℤ) * (q2 + q0 + q3) + ((n / 27 % 3 : ℕ) : ℤ) * (q3 + q1 + q2 + q4) +
        ((n / 81 % 3 : ℕ) : ℤ) * (q4 + q3 + q5) + ((n / 243 % 3 : ℕ) : ℤ) * (q5 + q4)), ?_⟩
    rw [hF]
    linear_combination ((n / 1 % 3 : ℕ) : ℤ) * (hq0 + hq2) +
      ((n / 3 % 3 : ℕ) : ℤ) * (hq1 + hq3) + ((n / 9 % 3 : ℕ) : ℤ) * (hq2 + hq0 + hq3) +
      ((n / 27 % 3 : ℕ) : ℤ) * (hq3 + hq1 + hq2 + hq4) +
      ((n / 81 % 3 : ℕ) : ℤ) * (hq4 + hq3 + hq5) + ((n / 243 % 3 : ℕ) : ℤ) * (hq5 + hq4) -
      hqi
  omega

theorem normB_iff (c : ℕ) : normB c = true ↔ c = 0 ∨ (1 ≤ c ∧ c < 2) ∨ (3 ≤ c ∧ c < 6) ∨
    (9 ≤ c ∧ c < 18) ∨ (27 ≤ c ∧ c < 54) ∨ (81 ≤ c ∧ c < 162) ∨ (243 ≤ c ∧ c < 486) := by
  change orB (Nat.beq c 0) (orB (andB (Nat.ble 1 c) (Nat.blt c 2)) (orB (andB (Nat.ble 3 c)
    (Nat.blt c 6)) (orB (andB (Nat.ble 9 c) (Nat.blt c 18)) (orB (andB (Nat.ble 27 c)
    (Nat.blt c 54)) (orB (andB (Nat.ble 81 c) (Nat.blt c 162)) (andB (Nat.ble 243 c)
    (Nat.blt c 486))))))) = true ↔ _
  simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq,
    Nat.blt_eq]

theorem lt_of_normB {c : ℕ} (h : normB c = true) : c < 486 := by
  rw [normB_iff] at h
  omega

@[expose] def codeOf (p : ℕ) : ℕ :=
  if p < 2 then p else if p < 5 then p + 1 else if p < 14 then p + 4 else if p < 41 then p + 13
  else if p < 122 then p + 40 else p + 121

theorem posOf_facts : ∀ c < 486, normB c = true → posOf c < 365 ∧ codeOf (posOf c) = c := by
  decide +kernel

theorem posOf_lt {c : ℕ} (h : normB c = true) : posOf c < 365 :=
  (posOf_facts c (lt_of_normB h) h).1

theorem posOf_inj {c c' : ℕ} (h : normB c = true) (h' : normB c' = true)
    (e : posOf c = posOf c') : c = c' := by
  rw [← (posOf_facts c (lt_of_normB h) h).2, ← (posOf_facts c' (lt_of_normB h') h').2, e]

theorem codesOK_sound {cs : List ℕ} {v1 v2 : ℕ} (h : codesOK cs v1 v2 = true) :
    ∀ c ∈ cs, normB c = true ∧ pr c v1 = 0 ∧ pr c v2 = 0 := by
  unfold codesOK at h
  rw [allL_eq_true] at h
  intro c hc
  have := h c hc
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at this
  exact this

theorem hexEq_sound {c1 c2 c3 j : ℕ} (h : hexEq c1 c2 c3 (4 * j) = true) :
    (((c1 / 16 ^ j % 16 : ℕ) : ℤ) - 8) + (((c2 / 16 ^ j % 16 : ℕ) : ℤ) - 8) =
      ((c3 / 16 ^ j % 16 : ℕ) : ℤ) - 8 := by
  change Nat.beq (((c1 >>> (4 * j)) &&& 15) + ((c2 >>> (4 * j)) &&& 15))
    (((c3 >>> (4 * j)) &&& 15) + 8) = true at h
  rw [Nat.beq_eq, hex_eq, hex_eq, hex_eq] at h
  omega

theorem sumOK_sound {c1 c2 c3 : ℕ} (h : sumOK c1 c2 c3 = true) :
    decodeVec (τ := .E6) c1 + decodeVec c2 = decodeVec c3 := by
  unfold sumOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  funext j
  rw [Pi.add_apply]
  fin_cases j
  · exact hexEq_sound (j := 0) h0
  · exact hexEq_sound (j := 1) h1
  · exact hexEq_sound (j := 2) h2
  · exact hexEq_sound (j := 3) h3
  · exact hexEq_sound (j := 4) h4
  · exact hexEq_sound (j := 5) h5

theorem recOK_sound {R : ℕ} {r : List ℕ} (h : recOK R r = true) :
    (∀ c ∈ codesOf r, normB c = true) ∧
    ((hd r = 0 ∧ hd (tl r) < 72 ∧ ∀ c ∈ codesOf r,
        triPairing (τ := .E6) (vec3OfIndex c) (decodeVec (fld R 24 (hd (tl r)))) = 0) ∨
     (hd r = 1 ∧ hd (tl r) < 72 ∧ hd (tl (tl r)) < 72 ∧ hd (tl (tl (tl r))) < 72 ∧
      decodeVec (τ := .E6) (fld R 24 (hd (tl r))) + decodeVec (fld R 24 (hd (tl (tl r)))) =
        decodeVec (fld R 24 (hd (tl (tl (tl r))))) ∧
      ¬ (3 : ℤ) ∣ iform (τ := .E6) (digLift (hd (tl (tl (tl (tl r))))))
        (decodeVec (fld R 24 (hd (tl (tl (tl r)))))) ∧
      ∀ c ∈ codesOf r, triPairing (τ := .E6) (vec3OfIndex c)
          (decodeVec (fld R 24 (hd (tl r))) - decodeVec (fld R 24 (hd (tl (tl r))))) = 0 ∧
        triPairing (τ := .E6) (vec3OfIndex c) (digLift (hd (tl (tl (tl (tl r)))))) = 0)) := by
  unfold recOK at h
  simp only [letN_eq] at h
  cases hk : Nat.beq (hd r) 0
  · rw [hk] at h
    change andB (Nat.beq (hd r) 1) _ = true at h
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨hk1, hi1, hi2, hi3, -, hsum, hform, hcodes⟩ := h
    have hc := codesOK_sound hcodes
    refine ⟨fun c hc' => (hc c hc').1, Or.inr ⟨hk1, hi1, hi2, hi3, sumOK_sound hsum,
      iform_sound hform, fun c hc' => ⟨pr_kvD (hc c hc').2.1, pr_kvT (hc c hc').2.2⟩⟩⟩
  · rw [hk] at h
    change andB (Nat.blt (hd (tl r)) 72) _ = true at h
    simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hi1, hcodes⟩ := h
    have hc := codesOK_sound hcodes
    exact ⟨fun c hc' => (hc c hc').1, Or.inl ⟨Nat.eq_of_beq_eq_true hk, hi1,
      fun c hc' => pr_kvR (hc c hc').2.1⟩⟩

theorem recsOK_sound {R : ℕ} {ws : List (List ℕ)} (h : recsOK R ws = true) :
    ∀ r ∈ ws, recOK R r = true := by
  induction ws with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons w ws ih =>
    change andB (recOK R w) (recsOK R ws) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · exact ih h.2 r hr

@[expose] noncomputable def repFold (p : ℕ) (ws : List (List ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun r _ ih => letN (plOf (codesOf r)) fun PL =>
      Bool.rec (motive := fun _ => ℕ) ih (Nat.lor (rkOf PL (codesOf r)) ih) (bitB PL p)) ws

theorem repOK_eq (p : ℕ) (ws : List (List ℕ)) :
    repOK p ws = forceN (1 <<< 133225 - 1) (fun F => Nat.beq F (repFold p ws)) := rfl

theorem testBit_plOf {cs : List ℕ} {z : ℕ} (h : (plOf cs).testBit z = true) :
    ∃ c ∈ cs, posOf c = z := by
  induction cs with
  | nil => exact absurd h (by change ¬ (Nat.testBit 0 z = true); rw [Nat.zero_testBit]; decide)
  | cons c cs ih =>
    change ((1 <<< posOf c) ||| plOf cs).testBit z = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨c', hc', e⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hc', e⟩

theorem plOf_lt {cs : List ℕ} {m : ℕ} (h : ∀ c ∈ cs, posOf c < m) : plOf cs < 2 ^ m := by
  induction cs with
  | nil => exact Nat.two_pow_pos m
  | cons c cs ih =>
    change (1 <<< posOf c) ||| plOf cs < 2 ^ m
    rw [Nat.one_shiftLeft]
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (h c List.mem_cons_self))
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem testBit_rkOf {PL : ℕ} {cs : List ℕ} {k : ℕ} (h : (rkOf PL cs).testBit k = true) :
    ∃ c ∈ cs, 365 * posOf c ≤ k ∧ PL.testBit (k - 365 * posOf c) = true := by
  induction cs with
  | nil => exact absurd h (by change ¬ (Nat.testBit 0 k = true); rw [Nat.zero_testBit]; decide)
  | cons c cs ih =>
    change ((PL <<< (365 * posOf c)) ||| rkOf PL cs).testBit k = true at h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨c', hc', e⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hc', e⟩

theorem testBit_repFold {p : ℕ} {ws : List (List ℕ)} {k : ℕ} (h : (repFold p ws).testBit k = true) :
    ∃ r ∈ ws, bitB (plOf (codesOf r)) p = true ∧
      (rkOf (plOf (codesOf r)) (codesOf r)).testBit k = true := by
  induction ws with
  | nil => exact absurd h (by change ¬ (Nat.testBit 0 k = true); rw [Nat.zero_testBit]; decide)
  | cons r ws ih =>
    change (letN (plOf (codesOf r)) fun PL => Bool.rec (motive := fun _ => ℕ) (repFold p ws)
      (Nat.lor (rkOf PL (codesOf r)) (repFold p ws)) (bitB PL p)).testBit k = true at h
    rw [letN_eq] at h
    cases hb : bitB (plOf (codesOf r)) p
    · rw [hb] at h
      change (repFold p ws).testBit k = true at h
      obtain ⟨r', hr', e⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
    · rw [hb] at h
      change (rkOf (plOf (codesOf r)) (codesOf r) ||| repFold p ws).testBit k = true at h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨r, List.mem_cons_self, hb, h⟩
      · obtain ⟨r', hr', e⟩ := ih h
        exact ⟨r', List.mem_cons_of_mem _ hr', e⟩

set_option exponentiation.threshold 140000 in
theorem repOK_sound {p : ℕ} {ws : List (List ℕ)} (h : repOK p ws = true)
    (hpos : ∀ r ∈ ws, ∀ c ∈ codesOf r, posOf c < 365) {y z : ℕ} (hy : y < 365) (hz : z < 365) :
    ∃ r ∈ ws, (∃ c ∈ codesOf r, posOf c = p) ∧ (∃ c ∈ codesOf r, posOf c = y) ∧
      (∃ c ∈ codesOf r, posOf c = z) := by
  rw [repOK_eq, forceN_eq, Nat.beq_eq, Nat.one_shiftLeft] at h
  have hk : (repFold p ws).testBit (365 * y + z) = true := by
    have e := Nat.testBit_two_pow_sub_one 133225 (365 * y + z)
    rw [h] at e
    rw [e, decide_eq_true_eq]
    omega
  obtain ⟨r, hr, hb, hrk⟩ := testBit_repFold hk
  obtain ⟨c, hc, hle, hbit⟩ := testBit_rkOf hrk
  have hPL := plOf_lt (hpos r hr)
  have hlt : 365 * y + z - 365 * posOf c < 365 := by
    by_contra hge
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hPL
      (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hbit
    exact absurd hbit (by decide)
  have hq : posOf c = y := by omega
  have hz' : 365 * y + z - 365 * posOf c = z := by omega
  rw [hz'] at hbit
  rw [bitB_eq] at hb
  exact ⟨r, hr, testBit_plOf hb, ⟨c, hc, hq⟩, testBit_plOf hbit⟩

@[expose] noncomputable def wordsGo (rs : List ℕ) (ws : List (List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun w _ ih n => letN n fun n =>
      andB (letN (applyW w n) fun m => anyL rs fun r => Nat.beq m r) (ih (Nat.succ n))) ws

theorem wordsGo_sound {rs : List ℕ} :
    ∀ (ws : List (List ℕ)) (n : ℕ), wordsGo rs ws n = true →
      ∀ k < ws.length, applyW (ws.getD k []) (n + k) ∈ rs
  | [], _, _, k, hk => absurd hk (by simp)
  | w :: ws, n, h, k, hk => by
    change (letN n fun n => andB (letN (applyW w n) fun m => anyL rs fun r => Nat.beq m r)
      (wordsGo rs ws (Nat.succ n))) = true at h
    simp only [letN_eq, andB_eq, Bool.and_eq_true] at h
    cases k with
    | zero => exact mem_of_anyL h.1
    | succ k =>
      have := wordsGo_sound ws (n + 1) h.2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem wordsOK_sound {rs : List ℕ} {ws : List (List ℕ)} (h : wordsOK rs ws = true) :
    ∀ n < ws.length, applyW (ws.getD n []) n ∈ rs := by
  intro n hn
  have := wordsGo_sound ws 0 h n hn
  rwa [Nat.zero_add] at this

@[expose] def charAct (x : Fin Tag.E6.rank → ZMod 3) (i : ℕ) : Fin Tag.E6.rank → ZMod 3 :=
  if h : i < Tag.E6.rank then triReflect (τ := .E6) ⟨i, h⟩ x else x

theorem cb_spec : ∀ i (hi : i < Tag.E6.rank) j (hj : j < Tag.E6.rank),
    ((cb i j : ℕ) : ZMod 3) + ((Tag.E6.cartan ⟨i, hi⟩ ⟨j, hj⟩ : ℤ) : ZMod 3) = 0 := by
  decide +kernel

theorem cb_big {i j : ℕ} (hi : 6 ≤ i) : cb i j = 0 := by
  change (52487049861 >>> (6 * i + j)) &&& 1 = 0
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
  · rfl
  · calc 52487049861 < 2 ^ 36 := by norm_num
      _ ≤ 2 ^ (6 * i + j) := Nat.pow_le_pow_right (by norm_num) (by omega)

@[expose] noncomputable def actA (n i k : ℕ) : ℕ := n / 3 ^ k % 3 + n / 3 ^ i % 3 * cb i k

theorem actK_eq (n i : ℕ) : actK n i = actA n i 0 % 3 + (3 * (actA n i 1 % 3) +
    (9 * (actA n i 2 % 3) + (27 * (actA n i 3 % 3) + (81 * (actA n i 4 % 3) +
      243 * (actA n i 5 % 3))))) := by
  unfold actK
  rw [letN_eq]
  rfl

theorem actK_digit (n i : ℕ) : ∀ k < 6, actK n i / 3 ^ k % 3 = actA n i k % 3 := by
  intro k hk
  rw [actK_eq]
  interval_cases k <;> simp only [Nat.reducePow] <;> omega

theorem actK_spec (n i : ℕ) : vec3OfIndex (τ := .E6) (actK n i) = charAct (vec3OfIndex n) i := by
  funext j
  have hr : charAct (vec3OfIndex (τ := .E6) n) i j = vec3OfIndex (τ := .E6) n j +
      ((n / 3 ^ i % 3 : ℕ) : ZMod 3) * ((cb i j : ℕ) : ZMod 3) := by
    unfold charAct
    split_ifs with h
    · have hcb := cb_spec i h j j.2
      simp only [triReflect, vec3OfIndex, Fin.eta] at hcb ⊢
      linear_combination (0 - ((n / 3 ^ i % 3 : ℕ) : ZMod 3)) * hcb
    · have h6 : Tag.E6.rank = 6 := rfl
      rw [cb_big (by omega : 6 ≤ i)]
      simp
  rw [hr]
  simp only [vec3OfIndex]
  rw [actK_digit n i j j.2, ZMod.natCast_mod, actA, Nat.cast_add, Nat.cast_mul]

theorem applyW_cons (i : ℕ) (w : List ℕ) (n : ℕ) : applyW (i :: w) n = applyW w (actK n i) := by
  change letN (actK n i) (applyW w) = _
  rw [letN_eq]

theorem applyW_spec : ∀ (w : List ℕ) (n : ℕ),
    vec3OfIndex (τ := .E6) (applyW w n) = w.foldl charAct (vec3OfIndex n)
  | [], _ => rfl
  | i :: w, n => by rw [applyW_cons, applyW_spec w, actK_spec, List.foldl_cons]

theorem digsM_sound {a n m : ℕ} (h : digsM a n m = true) :
    ∀ j, vec3OfIndex (τ := .E6) n j = (a : ZMod 3) * vec3OfIndex (τ := .E6) m j := by
  have key : ∀ p, digM a n m p = true →
      ((n / p % 3 : ℕ) : ZMod 3) = (a : ZMod 3) * ((m / p % 3 : ℕ) : ZMod 3) := by
    intro p hp
    have e : n / p % 3 = a * (m / p % 3) % 3 := Nat.eq_of_beq_eq_true hp
    rw [e, ZMod.natCast_mod, Nat.cast_mul]
  unfold digsM at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  intro j
  fin_cases j
  · exact key 1 h0
  · exact key 3 h1
  · exact key 9 h2
  · exact key 27 h3
  · exact key 81 h4
  · exact key 243 h5

theorem normOK_sound {N : ℕ} (h : normOK N = true) : ∀ n < N, normB (normC n) = true ∧
    ((∀ j, vec3OfIndex (τ := .E6) n j = vec3OfIndex (τ := .E6) (normC n) j) ∨
      (∀ j, vec3OfIndex (τ := .E6) n j = 2 * vec3OfIndex (τ := .E6) (normC n) j)) := by
  induction N with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ N ih =>
    change andB (letN (normC N) fun m => andB (normB m) (orB (digsM 1 N m) (digsM 2 N m)))
      (normOK N) = true at h
    simp only [letN_eq, andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hb, hd⟩, hN⟩ := h
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact ih hN n hn
    · refine ⟨hb, ?_⟩
      rcases hd with hd | hd
      · left
        intro j
        rw [digsM_sound hd j, Nat.cast_one, one_mul]
      · right
        intro j
        rw [digsM_sound hd j]
        norm_num

@[expose] noncomputable def rootsGo (R : ℕ) (C : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun k => Nat.beq k (nat_lit 72))
    (fun c _ ih k => andB (Nat.beq (fld R 24 k) c) (ih (Nat.succ k))) C

theorem rootsGo_sound {R : ℕ} : ∀ (C : List ℕ) (k : ℕ), rootsGo R C k = true →
    k + C.length = 72 ∧ ∀ m < C.length, fld R 24 (k + m) = C.getD m 0
  | [], k, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun m hm => absurd hm (by simp)⟩
  | c :: C, k, h => by
    change andB (Nat.beq (fld R 24 k) c) (rootsGo R C (Nat.succ k)) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨hl, hm⟩ := rootsGo_sound C (k + 1) h.2
    refine ⟨by rw [List.length_cons]; omega, fun m hm' => ?_⟩
    cases m with
    | zero => simpa using h.1
    | succ m =>
      have := hm m (by simpa using hm')
      rw [show k + (m + 1) = k + 1 + m by omega, this]
      simp

theorem rootsOK_sound {R : ℕ} {C : List ℕ} (h : rootsOK R C = true) :
    C.length = 72 ∧ ∀ k < 72, fld R 24 k = C.getD k 0 := by
  obtain ⟨hl, hm⟩ := rootsGo_sound C 0 h
  rw [Nat.zero_add] at hl
  refine ⟨hl, fun k hk => ?_⟩
  have := hm k (hl ▸ hk)
  rwa [Nat.zero_add] at this

end CFSG.KC.E6TwA2

end
