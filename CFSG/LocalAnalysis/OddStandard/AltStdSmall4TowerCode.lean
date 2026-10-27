module

public import Certificates.Data.CFSGNative.SCATWreathCode
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup CFSG.SCATWreath

theorem length_filter_range (p : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter p).length = Nat.card {c : ℕ // c < n ∧ p c = true} := by
  classical
  have hnd : ((List.range n).filter p).Nodup := (List.nodup_range).filter p
  rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  simp [List.mem_filter, List.mem_range]

theorem length_filter_range_comp {n : ℕ} {φ : ℕ → ℕ} (hφ : ∀ c < n, φ c < n)
    (hinj : ∀ a < n, ∀ b < n, φ a = φ b → a = b) (p : ℕ → Bool) :
    ((List.range n).filter fun c => p (φ c)).length = ((List.range n).filter p).length := by
  rw [length_filter_range, length_filter_range]
  refine Nat.card_eq_of_bijective (fun c => ⟨φ c.1, hφ c.1 c.2.1, c.2.2⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (hinj x.1 x.2.1 y.1 y.2.1 (congrArg Subtype.val hxy))
  · rintro ⟨b, hb, hpb⟩
    have hsurj : ∀ b < n, ∃ a < n, φ a = b := by
      have hinj' : Function.Injective fun a : Fin n => (⟨φ a.1, hφ a.1 a.2⟩ : Fin n) :=
        fun a a' h => Fin.ext (hinj a.1 a.2 a'.1 a'.2 (congrArg Fin.val h))
      intro b hb
      obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hinj') ⟨b, hb⟩
      exact ⟨a.1, a.2, congrArg Fin.val ha⟩
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    exact ⟨⟨a, ha, hpb⟩, rfl⟩

variable {G : Type*} [Group G]

structure IsModel (K : Subgroup G) (n : ℕ) (mul : ℕ → ℕ → ℕ) (dec : ℕ → G) : Prop where
  mem : ∀ c < n, dec c ∈ K
  inj : ∀ a < n, ∀ b < n, dec a = dec b → a = b
  surj : ∀ x ∈ K, ∃ c < n, dec c = x
  mul_lt : ∀ a < n, ∀ b < n, mul a b < n
  dec_mul : ∀ a < n, ∀ b < n, dec (mul a b) = dec a * dec b
  zero_lt : 0 < n
  dec_zero : dec 0 = 1

namespace IsModel

variable {K : Subgroup G} {n : ℕ} {mul : ℕ → ℕ → ℕ} {dec : ℕ → G}

open Classical in
noncomputable def code (M : IsModel K n mul dec) (x : G) : ℕ :=
  if h : x ∈ K then (M.surj x h).choose else 0

variable (M : IsModel K n mul dec)
include M

theorem code_lt {x : G} (hx : x ∈ K) : M.code x < n := by
  rw [code, dif_pos hx]
  exact (M.surj x hx).choose_spec.1

theorem dec_code {x : G} (hx : x ∈ K) : dec (M.code x) = x := by
  rw [code, dif_pos hx]
  exact (M.surj x hx).choose_spec.2

theorem code_dec {c : ℕ} (hc : c < n) : M.code (dec c) = c :=
  M.inj _ (M.code_lt (M.mem c hc)) c hc (M.dec_code (M.mem c hc))

theorem eq_iff {a b : ℕ} (ha : a < n) (hb : b < n) : dec a = dec b ↔ a = b :=
  ⟨M.inj a ha b hb, fun h => h ▸ rfl⟩

theorem dec_eq_one_iff {c : ℕ} (hc : c < n) : dec c = 1 ↔ c = 0 := by
  rw [← M.dec_zero, M.eq_iff hc M.zero_lt]

theorem code_one : M.code 1 = 0 := by
  rw [← M.dec_zero, M.code_dec M.zero_lt]

theorem code_mul {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    M.code (x * y) = mul (M.code x) (M.code y) := by
  have h := M.dec_mul _ (M.code_lt hx) _ (M.code_lt hy)
  rw [M.dec_code hx, M.dec_code hy] at h
  rw [← h, M.code_dec (M.mul_lt _ (M.code_lt hx) _ (M.code_lt hy))]

theorem comm_iff {a b : ℕ} (ha : a < n) (hb : b < n) :
    mul a b = mul b a ↔ dec a * dec b = dec b * dec a := by
  rw [← M.dec_mul a ha b hb, ← M.dec_mul b hb a ha,
    M.eq_iff (M.mul_lt a ha b hb) (M.mul_lt b hb a ha)]

theorem dec_inv {c i : ℕ} (hc : c < n) (hi : i < n) (h : mul c i = 0) : dec i = (dec c)⁻¹ := by
  have h1 := M.dec_mul c hc i hi
  rw [h, M.dec_zero] at h1
  exact (inv_eq_of_mul_eq_one_right h1.symm).symm

theorem dec_conj {d u i : ℕ} (hd : d < n) (hu : u < n) (hi : i < n) (h : mul d i = 0) :
    dec (mul (mul d u) i) = dec d * dec u * (dec d)⁻¹ := by
  rw [M.dec_mul _ (M.mul_lt d hd u hu) i hi, M.dec_mul d hd u hu, M.dec_inv hd hi h]

theorem conj_lt {d u i : ℕ} (hd : d < n) (hu : u < n) (hi : i < n) : mul (mul d u) i < n :=
  M.mul_lt _ (M.mul_lt d hd u hu) i hi

theorem pw_lt {c : ℕ} (hc : c < n) (k : ℕ) : pw mul c k < n := by
  induction k with
  | zero => exact M.zero_lt
  | succ k ih => exact M.mul_lt c hc _ ih

theorem dec_pw {c : ℕ} (hc : c < n) (k : ℕ) : dec (pw mul c k) = dec c ^ k := by
  induction k with
  | zero =>
    show dec 0 = dec c ^ 0
    rw [pow_zero]
    exact M.dec_zero
  | succ k ih =>
    show dec (mul c (pw mul c k)) = dec c ^ (k + 1)
    rw [M.dec_mul c hc _ (M.pw_lt hc k), ih, pow_succ']

theorem pw_eq_zero_iff {c : ℕ} (hc : c < n) (k : ℕ) : pw mul c k = 0 ↔ dec c ^ k = 1 := by
  rw [← M.dec_pw hc, M.dec_eq_one_iff (M.pw_lt hc k)]

theorem count_eq (P : G → Prop) [DecidablePred P] :
    ((List.range n).filter fun c => decide (P (dec c))).length =
      Nat.card {x : G // x ∈ K ∧ P x} := by
  rw [length_filter_range]
  refine Nat.card_eq_of_bijective (fun c => ⟨dec c.1, M.mem c.1 c.2.1, by simpa using c.2.2⟩)
    ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (M.inj x.1 x.2.1 y.1 y.2.1 (congrArg Subtype.val hxy))
  · rintro ⟨x, hxK, hPx⟩
    obtain ⟨c, hc, rfl⟩ := M.surj x hxK
    exact ⟨⟨c, hc, by simpa using hPx⟩, rfl⟩

theorem card_cent_eq {r : ℕ} (hr : r < n) :
    Nat.card (K ⊓ centralizer {dec r} : Subgroup G) = cntC mul (List.range n) r := by
  classical
  have h := M.count_eq fun x => dec r * x = x * dec r
  rw [cntC]
  have e : ((List.range n).filter fun c => mul r c == mul c r) =
      ((List.range n).filter fun c => decide (dec r * dec c = dec c * dec r)) := by
    refine List.filter_congr fun c hc => ?_
    rw [List.mem_range] at hc
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    exact M.comm_iff hr hc
  rw [e, h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [mem_inf, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem dec_sq_iff {c : ℕ} (hc : c < n) : dec c ^ 2 = 1 ∧ dec c ≠ 1 ↔ c ≠ 0 ∧ mul c c = 0 := by
  rw [pow_two, ← M.dec_mul c hc c hc, M.dec_eq_one_iff (M.mul_lt c hc c hc), ne_eq,
    M.dec_eq_one_iff hc]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem mem_invols {c : ℕ} : c ∈ invols n mul ↔ c < n ∧ c ≠ 0 ∧ mul c c = 0 := by
  simp [invols, List.mem_filter, List.mem_range]

theorem ninv_cent_eq {r : ℕ} (hr : r < n) :
    Nat.card {x : (K ⊓ centralizer {dec r} : Subgroup G) // x ^ 2 = 1 ∧ x ≠ 1} =
      cntC mul (invols n mul) r := by
  classical
  have h := M.count_eq fun x => dec r * x = x * dec r ∧ x ^ 2 = 1 ∧ x ≠ 1
  have e : (invols n mul).filter (fun c => mul r c == mul c r) =
      ((List.range n).filter fun c =>
        decide (dec r * dec c = dec c * dec r ∧ dec c ^ 2 = 1 ∧ dec c ≠ 1)) := by
    rw [invols, List.filter_filter]
    refine List.filter_congr fun c hc => ?_
    rw [List.mem_range] at hc
    rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, beq_iff_eq,
      decide_eq_true_eq, M.comm_iff hr hc, M.dec_sq_iff hc]
  rw [cntC, e, h]
  have hfwd : ∀ x : {x : (K ⊓ centralizer {dec r} : Subgroup G) // x ^ 2 = 1 ∧ x ≠ 1},
      (x.1 : G) ∈ K ∧ dec r * x.1 = x.1 * dec r ∧ (x.1 : G) ^ 2 = 1 ∧ (x.1 : G) ≠ 1 := by
    intro x
    refine ⟨(mem_inf.1 x.1.2).1, (mem_centralizer_singleton_iff.1 (mem_inf.1 x.1.2).2).symm,
      ?_, ?_⟩
    · have h2 := congrArg Subtype.val x.2.1
      simpa using h2
    · intro h1
      exact x.2.2 (Subtype.ext (by simpa using h1))
  have hbwd : ∀ y : {x : G // x ∈ K ∧ dec r * x = x * dec r ∧ x ^ 2 = 1 ∧ x ≠ 1},
      y.1 ∈ (K ⊓ centralizer {dec r} : Subgroup G) :=
    fun y => mem_inf.2 ⟨y.2.1, mem_centralizer_singleton_iff.2 y.2.2.1.symm⟩
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, hfwd x⟩
      invFun := fun y => ⟨⟨y.1, hbwd y⟩, ?_, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · exact Subtype.ext (by simpa using y.2.2.2.1)
  · intro h1
    exact y.2.2.2.2 (by simpa using congrArg Subtype.val h1)

end IsModel

theorem ordLoop_congr {mul mul' : ℕ → ℕ → ℕ} {c c' : ℕ}
    (h : ∀ k, pw mul c k = 0 ↔ pw mul' c' k = 0) :
    ∀ (f k : ℕ), ordLoop mul c f (pw mul c k) k = ordLoop mul' c' f (pw mul' c' k) k := by
  intro f
  induction f with
  | zero => intro k; rfl
  | succ f ih =>
    intro k
    simp only [ordLoop]
    have hk := h k
    by_cases h0 : pw mul c k = 0
    · rw [if_pos (by simpa using h0), if_pos (by simpa using hk.1 h0)]
    · rw [if_neg (by simpa using h0), if_neg (by simpa using fun h' => h0 (hk.2 h'))]
      exact ih (k + 1)

theorem ordc_eq_of_iff {mul mul' : ℕ → ℕ → ℕ} {c c' : ℕ}
    (h : ∀ k, pw mul c k = 0 ↔ pw mul' c' k = 0) : ordc mul c = ordc mul' c' :=
  ordLoop_congr h 64 1

end CFSG.OddStandard.AltStdSmall4.Tower
