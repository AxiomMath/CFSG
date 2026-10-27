module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KS.Fi24Pc

variable {G : Type*} [Group G]

@[expose] def dg (u k : ℕ) : ℕ := u / 4 ^ k % 4

@[expose] noncomputable def nvFrom (x : ℕ → G) (u i : ℕ) : G :=
  ((List.range' i (16 - i)).map fun k => x k ^ dg u k).prod

@[expose] noncomputable def nv (x : ℕ → G) (u : ℕ) : G := nvFrom x u 0

@[expose] def Nsub (x : ℕ → G) (i : ℕ) : Subgroup G := Subgroup.closure (x '' Set.Ico i 16)

structure PcPres (x : ℕ → G) (pw : ℕ → ℕ) (cj : ℕ → ℕ → ℕ) : Prop where
  pow_eq : ∀ j < 16, x j ^ 3 = nv x (pw j)
  pow_dg : ∀ j < 16, ∀ k ≤ j, dg (pw j) k = 0
  conj_eq : ∀ j k, j < k → k < 16 → (x j)⁻¹ * x k * x j = nv x (cj j k)
  conj_dg : ∀ j k, j < k → k < 16 → ∀ m < k, dg (cj j k) m = 0
  conj_dg_self : ∀ j k, j < k → k < 16 → dg (cj j k) k = 1

variable {x : ℕ → G}

theorem nvFrom_of_ge {u i : ℕ} (hi : 16 ≤ i) : nvFrom x u i = 1 := by
  unfold nvFrom
  rw [show 16 - i = 0 by omega, List.range'_zero, List.map_nil, List.prod_nil]

theorem nvFrom_succ {u i : ℕ} (hi : i < 16) : nvFrom x u i = x i ^ dg u i * nvFrom x u (i + 1) := by
  unfold nvFrom
  rw [show 16 - i = (16 - (i + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.prod_cons]

theorem nvFrom_mem (u : ℕ) : ∀ i, nvFrom x u i ∈ Nsub x i := by
  intro i
  induction h : 16 - i generalizing i with
  | zero => rw [nvFrom_of_ge (by omega)]; exact one_mem _
  | succ n ih =>
    rw [nvFrom_succ (by omega)]
    refine mul_mem (pow_mem (Subgroup.subset_closure
      (Set.mem_image_of_mem x (show i ∈ Set.Ico i 16 from ⟨le_refl _, by omega⟩))) _) ?_
    exact Subgroup.closure_mono (Set.image_mono (Set.Ico_subset_Ico_left (Nat.le_succ i)))
      (ih (i + 1) (by omega))

theorem Nsub_anti {i j : ℕ} (h : i ≤ j) : Nsub x j ≤ Nsub x i :=
  Subgroup.closure_mono (Set.image_mono (Set.Ico_subset_Ico_left h))

theorem x_mem {i k : ℕ} (hi : i ≤ k) (hk : k < 16) : x k ∈ Nsub x i :=
  Subgroup.subset_closure ⟨k, ⟨hi, hk⟩, rfl⟩

theorem nvFrom_zero {u i j : ℕ} (hij : i ≤ j) (h : ∀ m, i ≤ m → m < j → dg u m = 0) :
    nvFrom x u i = nvFrom x u j := by
  induction h' : j - i generalizing i with
  | zero => rw [show i = j by omega]
  | succ n ih =>
    by_cases hi : i < 16
    · rw [nvFrom_succ hi, h i le_rfl (by omega), pow_zero, one_mul]
      exact ih (by omega) (fun m hm hmj => h m (by omega) hmj) (by omega)
    · rw [nvFrom_of_ge (by omega), nvFrom_of_ge (by omega)]

theorem nv_mem {u i : ℕ} (h : ∀ m < i, dg u m = 0) : nv x u ∈ Nsub x i := by
  by_cases hi : i ≤ 16
  · unfold nv
    rw [nvFrom_zero (Nat.zero_le i) (fun m _ hm => h m hm)]
    exact nvFrom_mem u i
  · unfold nv
    rw [nvFrom_zero (j := 16) (Nat.zero_le _) (fun m _ hm => h m (by omega)), nvFrom_of_ge le_rfl]
    exact one_mem _

theorem Nsub_top : Nsub x 16 = ⊥ := by
  unfold Nsub
  rw [Set.Ico_self, Set.image_empty, Subgroup.closure_empty]

section Pres

variable {pw : ℕ → ℕ} {cj : ℕ → ℕ → ℕ} (hP : PcPres x pw cj)
include hP

theorem cube_mem {i : ℕ} (hi : i < 16) : x i ^ 3 ∈ Nsub x (i + 1) := by
  rw [hP.pow_eq i hi]
  exact nv_mem fun m hm => hP.pow_dg i hi m (by omega)

theorem conj_inv_mem {k i : ℕ} (hk : k < 16) {n : G} (hn : n ∈ Nsub x i) :
    (x k)⁻¹ * n * x k ∈ Nsub x i := by
  by_cases hki : i ≤ k
  · have := x_mem (x := x) hki hk
    exact mul_mem (mul_mem (inv_mem this) hn) this
  · induction hn using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hy
      rw [hP.conj_eq k m (by omega) hm2]
      exact Nsub_anti hm1 (nv_mem fun m' hm' => hP.conj_dg k m (by omega) hm2 m' hm')
    | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
    | mul a b _ _ ha hb =>
      have e : (x k)⁻¹ * (a * b) * x k = ((x k)⁻¹ * a * x k) * ((x k)⁻¹ * b * x k) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : (x k)⁻¹ * a⁻¹ * x k = ((x k)⁻¹ * a * x k)⁻¹ := by group
      rw [e]
      exact inv_mem ha

theorem conjPow_inv_mem {k i : ℕ} (hk : k < 16) {n : G} (hn : n ∈ Nsub x i) (e : ℕ) :
    (x k ^ e)⁻¹ * n * x k ^ e ∈ Nsub x i := by
  induction e generalizing n with
  | zero => simpa using hn
  | succ e ih =>
    have := conj_inv_mem hP hk (ih hn)
    have e1 : (x k ^ (e + 1))⁻¹ * n * x k ^ (e + 1) = (x k)⁻¹ * ((x k ^ e)⁻¹ * n * x k ^ e) * x k := by
      rw [pow_succ]; group
    rw [e1]
    exact this

variable [Finite G]

theorem conj_mem' {k i : ℕ} (hk : k < 16) {n : G} (hn : n ∈ Nsub x i) :
    x k * n * (x k)⁻¹ ∈ Nsub x i := by
  let f : Nsub x i → Nsub x i := fun m => ⟨(x k)⁻¹ * m * x k, conj_inv_mem hP hk m.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have : (x k)⁻¹ * (a : G) * x k = (x k)⁻¹ * b * x k := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.1 hf) ⟨n, hn⟩
  have : (x k)⁻¹ * (m : G) * x k = n := congrArg Subtype.val hm
  have e : x k * n * (x k)⁻¹ = m := by rw [← this]; group
  rw [e]
  exact m.2

theorem conj_mem {i : ℕ} {g : G} (hg : g ∈ Nsub x 0) {n : G} (hn : n ∈ Nsub x i) :
    g * n * g⁻¹ ∈ Nsub x i := by
  suffices h : ∀ n ∈ Nsub x i, g * n * g⁻¹ ∈ Nsub x i ∧ g⁻¹ * n * g ∈ Nsub x i from (h n hn).1
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hy
    exact fun n hn => ⟨conj_mem' hP hk hn, conj_inv_mem hP hk hn⟩
  | one => exact fun n hn => by simpa using hn
  | mul a b _ _ ha hb =>
    intro n hn
    constructor
    · have e : a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact (ha _ (hb n hn).1).1
    · have e : (a * b)⁻¹ * n * (a * b) = b⁻¹ * (a⁻¹ * n * a) * b := by group
      rw [e]
      exact (hb _ (ha n hn).2).2
  | inv a _ ha =>
    intro n hn
    constructor
    · simpa using (ha n hn).2
    · simpa using (ha n hn).1

theorem decomp {i : ℕ} (hi : i < 16) {n : G} (hn : n ∈ Nsub x i) :
    ∃ e < 3, (x i ^ e)⁻¹ * n ∈ Nsub x (i + 1) := by
  have h3 := cube_mem hP hi
  induction hn using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hy
    by_cases hmi : m = i
    · subst hmi
      exact ⟨1, by norm_num, by rw [pow_one, inv_mul_cancel]; exact one_mem _⟩
    · exact ⟨0, by norm_num, by rw [pow_zero, inv_one, one_mul]; exact x_mem (by omega) hm2⟩
  | one => exact ⟨0, by norm_num, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, he, ha'⟩ := ha
    obtain ⟨f, hf, hb'⟩ := hb
    have hc := conjPow_inv_mem hP hi ha' f
    by_cases hef : e + f < 3
    · refine ⟨e + f, hef, ?_⟩
      have eq : (x i ^ (e + f))⁻¹ * (a * b) =
          ((x i ^ f)⁻¹ * ((x i ^ e)⁻¹ * a) * x i ^ f) * ((x i ^ f)⁻¹ * b) := by
        rw [pow_add]; group
      rw [eq]
      exact mul_mem hc hb'
    · refine ⟨e + f - 3, by omega, ?_⟩
      have eq : (x i ^ (e + f - 3))⁻¹ * (a * b) =
          x i ^ 3 * (((x i ^ f)⁻¹ * ((x i ^ e)⁻¹ * a) * x i ^ f) * ((x i ^ f)⁻¹ * b)) := by
        have : x i ^ (e + f) = x i ^ 3 * x i ^ (e + f - 3) := by
          rw [← pow_add]; congr 1; omega
        rw [show (x i ^ (e + f - 3))⁻¹ = x i ^ 3 * (x i ^ (e + f))⁻¹ by rw [this]; group, pow_add]
        group
      rw [eq]
      exact mul_mem h3 (mul_mem hc hb')
  | inv a _ ha =>
    obtain ⟨e, he, ha'⟩ := ha
    by_cases e0 : e = 0
    · subst e0
      rw [pow_zero, inv_one, one_mul] at ha'
      exact ⟨0, by norm_num, by rw [pow_zero, inv_one, one_mul]; exact inv_mem ha'⟩
    · refine ⟨3 - e, by omega, ?_⟩
      have hc := conjPow_inv_mem hP hi (inv_mem ha') (3 - e)
      have eq : (x i ^ (3 - e))⁻¹ * a⁻¹ =
          ((x i ^ (3 - e))⁻¹ * ((x i ^ e)⁻¹ * a)⁻¹ * x i ^ (3 - e)) * (x i ^ 3)⁻¹ := by
        have : x i ^ 3 = x i ^ e * x i ^ (3 - e) := by rw [← pow_add]; congr 1; omega
        rw [this]
        group
      rw [eq]
      exact mul_mem hc (inv_mem h3)

theorem card_step {i : ℕ} (hi : i < 16) : Nat.card (Nsub x i) ≤ 3 * Nat.card (Nsub x (i + 1)) := by
  let f : Fin 3 × Nsub x (i + 1) → Nsub x i := fun p =>
    ⟨x i ^ (p.1 : ℕ) * p.2, mul_mem (pow_mem (x_mem le_rfl hi) _) (Nsub_anti (Nat.le_succ i) p.2.2)⟩
  have hf : Function.Surjective f := by
    intro n
    obtain ⟨e, he, hn⟩ := decomp hP hi n.2
    refine ⟨(⟨e, he⟩, ⟨_, hn⟩), Subtype.ext ?_⟩
    change x i ^ e * ((x i ^ e)⁻¹ * n) = n
    group
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this

theorem card_le_pow : ∀ i ≤ 16, Nat.card (Nsub x i) * 3 ^ i ≤ 3 ^ 16 * Nat.card (Nsub x 16) := by
  intro i hi
  induction h : 16 - i generalizing i with
  | zero => rw [show i = 16 by omega, mul_comm]
  | succ n ih =>
    have := ih (i + 1) (by omega) (by omega)
    have h2 := card_step hP (i := i) (by omega)
    calc Nat.card (Nsub x i) * 3 ^ i ≤ 3 * Nat.card (Nsub x (i + 1)) * 3 ^ i :=
          Nat.mul_le_mul_right _ h2
      _ = Nat.card (Nsub x (i + 1)) * 3 ^ (i + 1) := by ring
      _ ≤ _ := this

theorem card_le : Nat.card (Nsub x 0) ≤ 3 ^ 16 := by
  have := card_le_pow hP 0 (by norm_num)
  rwa [Nsub_top, Subgroup.card_bot, pow_zero, mul_one, mul_one] at this

theorem card_eq (hl : 3 ^ 16 ≤ Nat.card (Nsub x 0)) {i : ℕ} (hi : i ≤ 16) :
    Nat.card (Nsub x i) = 3 ^ (16 - i) := by
  have h1 := card_le_pow hP i hi
  rw [Nsub_top, Subgroup.card_bot, mul_one] at h1
  have h2 : ∀ j ≤ i, Nat.card (Nsub x 0) ≤ 3 ^ j * Nat.card (Nsub x j) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have := card_step hP (i := j) (by omega)
      calc Nat.card (Nsub x 0) ≤ 3 ^ j * Nat.card (Nsub x j) := ih (by omega)
        _ ≤ 3 ^ j * (3 * Nat.card (Nsub x (j + 1))) := Nat.mul_le_mul_left _ this
        _ = 3 ^ (j + 1) * Nat.card (Nsub x (j + 1)) := by ring
  have h3 := le_trans hl (h2 i le_rfl)
  have e : (3 : ℕ) ^ 16 = 3 ^ i * 3 ^ (16 - i) := by rw [← pow_add]; congr 1; omega
  rw [e] at h3 h1
  have hp : 0 < 3 ^ i := by positivity
  apply le_antisymm
  · rw [mul_comm] at h1
    exact Nat.le_of_mul_le_mul_left h1 hp
  · exact Nat.le_of_mul_le_mul_left h3 hp

theorem pow_not_mem (hl : 3 ^ 16 ≤ Nat.card (Nsub x 0)) {i : ℕ} (hi : i < 16) {e : ℕ} (he : e < 3)
    (he0 : e ≠ 0) : x i ^ e ∉ Nsub x (i + 1) := by
  intro h
  have hx : x i ∈ Nsub x (i + 1) := by
    rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
    · simpa using h
    · have e1 : x i = x i ^ 3 * (x i ^ 2)⁻¹ := by group
      rw [e1]
      exact mul_mem (cube_mem hP hi) (inv_mem h)
  have hle : Nsub x i ≤ Nsub x (i + 1) := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    by_cases hmi : m = i
    · subst hmi; exact hx
    · exact x_mem (by omega) hm2
  have := Subgroup.card_le_of_le hle
  rw [card_eq hP hl (by omega), card_eq hP hl (by omega)] at this
  have e2 : 16 - i = (16 - (i + 1)) + 1 := by omega
  rw [e2, pow_succ] at this
  have : 0 < 3 ^ (16 - (i + 1)) := by positivity
  omega

theorem dg_zero (hl : 3 ^ 16 ≤ Nat.card (Nsub x 0)) {u i : ℕ} (hu16 : u < 4 ^ 16)
    (hu : ∀ k, dg u k < 3) (h : nv x u ∈ Nsub x i) : ∀ k < i, dg u k = 0 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_contra hne
    have hk16 : k < 16 := by
      by_contra h16
      have : u / 4 ^ k = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hu16 (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact hne (by unfold dg; rw [this])
    have e : nv x u = x k ^ dg u k * nvFrom x u (k + 1) := by
      unfold nv
      rw [nvFrom_zero (Nat.zero_le k) (fun m _ hm => ih m hm (by omega)), nvFrom_succ hk16]
    have hmem : x k ^ dg u k ∈ Nsub x (k + 1) := by
      have h1 : nv x u ∈ Nsub x (k + 1) := Nsub_anti (by omega) h
      rw [e] at h1
      have := mul_mem h1 (inv_mem (nvFrom_mem u (k + 1)))
      simpa using this
    exact pow_not_mem hP hl hk16 (hu k) hne hmem

theorem comm_mem {i : ℕ} (hi : i < 16) {g : G} (hg : g ∈ Nsub x 0) :
    (x i)⁻¹ * g⁻¹ * x i * g ∈ Nsub x (i + 1) := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hy
    rcases lt_trichotomy k i with hki | rfl | hik
    · have e2 : nv x (cj k i) = x i * nvFrom x (cj k i) (i + 1) := by
        unfold nv
        rw [nvFrom_zero (Nat.zero_le i) (fun m _ hm => hP.conj_dg k i hki hi m hm), nvFrom_succ hi,
          hP.conj_dg_self k i hki hi, pow_one]
      have e1 : (x i)⁻¹ * (x k)⁻¹ * x i * x k = (x i)⁻¹ * ((x k)⁻¹ * x i * x k) := by group
      rw [e1, hP.conj_eq k i hki hi, e2, ← mul_assoc, inv_mul_cancel, one_mul]
      exact nvFrom_mem _ _
    · rw [inv_mul_cancel_right, inv_mul_cancel]
      exact one_mem _
    · have e2 : nv x (cj i k) = x k * nvFrom x (cj i k) (k + 1) := by
        unfold nv
        rw [nvFrom_zero (Nat.zero_le k) (fun m _ hm => hP.conj_dg i k hik hk m hm), nvFrom_succ hk,
          hP.conj_dg_self i k hik hk, pow_one]
      have e1 : (x i)⁻¹ * (x k)⁻¹ * x i * x k = ((x i)⁻¹ * x k * x i)⁻¹ * x k := by group
      rw [e1, hP.conj_eq i k hik hk, e2, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem (Nsub_anti (by omega) (nvFrom_mem _ _))
  | one => simp
  | mul a b ha' hb' ha hb =>
    have e : (x i)⁻¹ * (a * b)⁻¹ * x i * (a * b) =
        ((x i)⁻¹ * b⁻¹ * x i * b) * (b⁻¹ * ((x i)⁻¹ * a⁻¹ * x i * a) * b⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem hb (conj_mem hP (inv_mem hb') ha)
  | inv a ha' ha =>
    have e : (x i)⁻¹ * a⁻¹⁻¹ * x i * a⁻¹ = a * ((x i)⁻¹ * a⁻¹ * x i * a)⁻¹ * a⁻¹ := by group
    rw [e]
    exact conj_mem hP ha' (inv_mem ha)

theorem cube_mem_of {i : ℕ} {Y h : G} (hY : Y ∈ Nsub x 0) (h3 : h ^ 3 = 1)
    (hm : Y⁻¹ * h ∈ Nsub x i) : Y ^ 3 ∈ Nsub x i := by
  have q1 := conj_mem hP (inv_mem (pow_mem hY 2)) hm
  have q2 := conj_mem hP (inv_mem hY) hm
  have e : Y ^ 3 = h ^ 3 * ((Y ^ 2)⁻¹ * (Y⁻¹ * h) * (Y ^ 2)⁻¹⁻¹ *
      ((Y⁻¹ * (Y⁻¹ * h) * Y⁻¹⁻¹) * (Y⁻¹ * h)))⁻¹ := by group
  rw [e, h3, one_mul]
  exact inv_mem (mul_mem q1 (mul_mem q2 hm))

theorem fuse_one {i : ℕ} {Y C B h m : G} (hC : C ∈ Nsub x 0) (hB : B ∈ Nsub x (i + 1))
    (hf : C * Y = Y * x i * C * B) (hm : m ∈ Nsub x (i + 1)) (hh : h = Y * x i * m) :
    Y⁻¹ * (C⁻¹ * h * C⁻¹⁻¹) ∈ Nsub x (i + 1) := by
  have e1 : Y⁻¹ * C⁻¹ = (Y * x i * C * B)⁻¹ := by rw [← hf, mul_inv_rev]
  have e2 : Y⁻¹ * (C⁻¹ * h * C⁻¹⁻¹) = (Y⁻¹ * C⁻¹) * (Y * x i * m) * C := by rw [hh, inv_inv]; group
  rw [e2, e1]
  have e3 : (Y * x i * C * B)⁻¹ * (Y * x i * m) * C = B⁻¹ * (C⁻¹ * m * C⁻¹⁻¹) := by group
  rw [e3]
  exact mul_mem (inv_mem hB) (conj_mem hP (inv_mem hC) hm)

theorem fuse_two {i : ℕ} (hi : i < 16) {Y C B h m : G} (hC : C ∈ Nsub x 0) (hB : B ∈ Nsub x (i + 1))
    (hf : C * Y = Y * x i * C * B) (hm : m ∈ Nsub x (i + 1)) (hh : h = Y * x i ^ 2 * m) :
    ∃ m' ∈ Nsub x (i + 1), C⁻¹ * h * C⁻¹⁻¹ = Y * x i * m' := by
  refine ⟨((x i)⁻¹ * B⁻¹ * x i) * ((x i)⁻¹ * C⁻¹ * x i * C) * (C⁻¹ * m * C⁻¹⁻¹),
    mul_mem (mul_mem (conj_inv_mem hP hi (inv_mem hB)) (comm_mem hP hi hC))
      (conj_mem hP (inv_mem hC) hm), ?_⟩
  have e0 : Y * x i = C * Y * B⁻¹ * C⁻¹ := by
    calc Y * x i = (Y * x i * C * B) * B⁻¹ * C⁻¹ := by group
      _ = C * Y * B⁻¹ * C⁻¹ := by rw [← hf]
  calc C⁻¹ * h * C⁻¹⁻¹ = C⁻¹ * (Y * x i) * x i * m * C := by rw [hh, inv_inv, pow_two]; group
    _ = C⁻¹ * (C * Y * B⁻¹ * C⁻¹) * x i * m * C := by rw [e0]
    _ = _ := by group

end Pres

@[expose] noncomputable def pre (x : ℕ → G) (u m : ℕ) : G :=
  ((List.range m).map fun k => x k ^ dg u k).prod

theorem nv_eq_pre {u m : ℕ} (hm : m ≤ 16) : nv x u = pre x u m * nvFrom x u m := by
  induction m with
  | zero => simp [pre, nv]
  | succ m ih =>
    rw [ih (by omega), nvFrom_succ (by omega)]
    unfold pre
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      mul_assoc]

theorem pre_congr {u v m : ℕ} (h : ∀ k < m, dg u k = dg v k) : pre x u m = pre x v m := by
  unfold pre
  congr 1
  exact List.map_congr_left fun k hk => by rw [h k (List.mem_range.1 hk)]

theorem dg_of_lt {y k : ℕ} (hy : y < 4 ^ k) : dg y k = 0 := by
  unfold dg
  rw [Nat.div_eq_of_lt hy]

theorem dg_add_lt {y e i k : ℕ} (hk : k < i) : dg (y + e * 4 ^ i) k = dg y k := by
  unfold dg
  have : 4 ^ i = 4 ^ k * (4 * 4 ^ (i - k - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [this, show y + e * (4 ^ k * (4 * 4 ^ (i - k - 1))) = y + (e * 4 * 4 ^ (i - k - 1)) * 4 ^ k by ring,
    Nat.add_mul_div_right _ _ (by positivity), show e * 4 * 4 ^ (i - k - 1) = 4 * (e * 4 ^ (i - k - 1)) by ring,
    Nat.add_mul_mod_self_left]

theorem dg_add_self {y e i : ℕ} (hy : y < 4 ^ i) (he : e < 4) : dg (y + e * 4 ^ i) i = e := by
  unfold dg
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hy, zero_add, Nat.mod_eq_of_lt he]

theorem dg_add_gt {y e i k : ℕ} (hy : y < 4 ^ i) (he : e < 3) (hk : i < k) : dg (y + e * 4 ^ i) k = 0 := by
  apply dg_of_lt
  have h1 : e * 4 ^ i ≤ 3 * 4 ^ i := Nat.mul_le_mul_right _ (by omega)
  have h2 : 4 ^ i + 3 * 4 ^ i = 4 ^ (i + 1) := by ring
  have h3 : 4 ^ (i + 1) ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem nv_add {y e i : ℕ} (hi : i < 16) (hy : y < 4 ^ i) (he : e < 3) :
    nv x (y + e * 4 ^ i) = nv x y * x i ^ e := by
  rw [nv_eq_pre (m := i) (by omega), nv_eq_pre (u := y) (m := i) (by omega),
    pre_congr (v := y) (fun k hk => dg_add_lt hk), nvFrom_succ hi, dg_add_self hy (by omega),
    nvFrom_zero (j := 16) (by omega) (fun m hm _ => dg_add_gt hy he (by omega)), nvFrom_of_ge le_rfl,
    nvFrom_zero (u := y) (j := 16) (by omega) (fun m hm _ => dg_of_lt
      (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hm))), nvFrom_of_ge le_rfl]
  simp

theorem nv_zero : nv x 0 = 1 := by
  unfold nv
  rw [nvFrom_zero (j := 16) (Nat.zero_le _) (fun m _ _ => by simp [dg]), nvFrom_of_ge le_rfl]

section Chain

variable {α : Type*} [MulAction G α]

@[expose] def stabN (P : Subgroup G) (b : ℕ → α) (n : ℕ) : Subgroup G where
  carrier := {g | g ∈ P ∧ ∀ m < n, g • b m = b m}
  mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun m hm => by rw [mul_smul, hh.2 m hm, hg.2 m hm]⟩
  one_mem' := ⟨one_mem _, fun m _ => one_smul G _⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun m hm => by rw [inv_smul_eq_iff, hg.2 m hm]⟩

@[expose] def stabEquiv (P : Subgroup G) (b : ℕ → α) (n : ℕ) :
    MulAction.stabilizer (stabN P b n) (b n) ≃ stabN P b (n + 1) where
  toFun g := ⟨g.1.1, g.1.2.1, fun m hm => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact g.1.2.2 m hm
    · have := MulAction.mem_stabilizer_iff.1 g.2
      rwa [Subgroup.smul_def] at this⟩
  invFun g := ⟨⟨g.1, g.2.1, fun m hm => g.2.2 m (by omega)⟩, by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact g.2.2 n (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_stabN_step [Finite G] (P : Subgroup G) (b : ℕ → α) (n : ℕ) :
    Nat.card (MulAction.orbit (stabN P b n) (b n)) * Nat.card (stabN P b (n + 1)) =
      Nat.card (stabN P b n) := by
  rw [← Nat.card_congr (stabEquiv P b n), ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (stabN P b n) (b n))]

theorem card_chain [Finite G] [Finite α] (P : Subgroup G) (b : ℕ → α) (H : ℕ → Subgroup G)
    (hH : ∀ l, H l ≤ P) (hfix : ∀ l, ∀ g ∈ H l, ∀ m < l, g • b m = b m) (n : ℕ) :
    (∏ l ∈ Finset.range n, Nat.card (MulAction.orbit (H l) (b l))) * Nat.card (stabN P b n) ≤
      Nat.card P := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, one_mul]
    apply Subgroup.card_le_of_le
    exact fun g hg => hg.1
  | succ n ih =>
    have hsub : MulAction.orbit (H n) (b n) ⊆ MulAction.orbit (stabN P b n) (b n) := by
      rintro _ ⟨g, rfl⟩
      exact ⟨⟨g.1, hH n g.2, fun m hm => hfix n g.1 g.2 m hm⟩, rfl⟩
    have h1 := Nat.card_mono (Set.toFinite _) hsub
    have h2 := card_stabN_step P b n
    rw [Finset.prod_range_succ, mul_assoc]
    calc _ ≤ (∏ l ∈ Finset.range n, Nat.card (MulAction.orbit (H l) (b l))) *
          (Nat.card (MulAction.orbit (stabN P b n) (b n)) * Nat.card (stabN P b (n + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
      _ = _ := by rw [h2]
      _ ≤ _ := ih

end Chain

end CFSG.KS.Fi24Pc

end
