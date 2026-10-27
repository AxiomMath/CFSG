module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {G : Type*} [Group G]

structure LocalData (t s d : G) (J B W : Subgroup G) : Prop where
  t_sq : t * t = 1
  t_ne_one : t ≠ 1
  s_sq : s * s = 1
  s_ne : s ≠ t
  s_ne_one : s ≠ 1
  ts : t * s = s * t
  J_le : J ≤ Subgroup.centralizer ({t} : Set G)
  J_conj : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∀ x ∈ J, c * x * c⁻¹ ∈ J
  t_mem : t ∈ J
  J_inv : ∀ x ∈ J, x * x = 1 → x = 1 ∨ x = t
  B_le : B ≤ Subgroup.centralizer ({t} : Set G)
  B_conj : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∀ x ∈ B, c * x * c⁻¹ ∈ B
  B_comm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  B_odd : ∀ x ∈ B, Odd (orderOf x)
  JB_comm : ∀ x ∈ J, ∀ y ∈ B, x * y = y * x
  JB_disj : J ⊓ B = ⊥
  s_inv : ∀ x ∈ B, s * x * s⁻¹ = x⁻¹
  cover : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∃ x ∈ J, ∃ y ∈ B, c = x * y ∨ c = x * y * s
  odd_mem : ∀ c ∈ Subgroup.centralizer ({t} : Set G), Odd (orderOf c) → c ∈ J ⊔ B
  W_mem : ∀ x, x ∈ W ↔ x ∈ J ∧ x * s = s * x ∧ Odd (orderOf x)
  W_cyclic : IsCyclic W
  CJs : ∀ x ∈ J, x * s = s * x → x ∈ Subgroup.zpowers t ⊔ W
  d_mem : d ∈ J
  d_sq : d * d = t
  d_s : d * s * d⁻¹ = t * s
  d_inv : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹
  cent_W : ∀ w ∈ W, w ≠ 1 → ∀ x ∈ J, x * w = w * x → x * s = s * x

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, K.one_mem, (mul_one y).symm⟩
    · exact ⟨1, H.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := ihx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := ihy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    have hc : k₁ * h₂ = h₂ * k₁ := (hHK h₂ hh₂ k₁ hk₁).symm
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [hc]
      _ = h₁ * h₂ * (k₁ * k₂) := by group
  | inv x _ ihx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := ihx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [mul_inv_rev]
    exact (hHK h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).symm

theorem eq_one_of_mul_self_eq_one_of_odd {x : G} (hx : Odd (orderOf x)) (h2 : x * x = 1) :
    x = 1 := by
  have h := orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hx
    exact absurd hx (by decide)

theorem mem_zpowers_sq_of_odd {x : G} (hx : Odd (orderOf x)) :
    x ∈ Subgroup.zpowers (x * x) := by
  obtain ⟨k, hk⟩ := hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨((k + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_two, ← pow_mul]
  have h : x ^ (2 * (k + 1)) = x ^ (orderOf x) * x := by
    rw [hk, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
  rw [h, pow_orderOf_eq_one, one_mul]

theorem odd_orderOf_mul_of_commute {x y : G} (hxy : Commute x y) (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) : Odd (orderOf (x * y)) := by
  have hdvd : orderOf (x * y) ∣ orderOf x * orderOf y := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hxy.mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, one_mul, mul_comm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  exact (hx.mul hy).of_dvd_nat hdvd

theorem odd_orderOf_of_mul {x y : G} (hxy : Commute x y) (hxy' : Odd (orderOf (x * y)))
    (hy : Odd (orderOf y)) : Odd (orderOf x) := by
  have h : x = x * y * y⁻¹ := by group
  rw [h]
  refine odd_orderOf_mul_of_commute ?_ hxy' (by rwa [orderOf_inv])
  exact ((hxy.mul_left (Commute.refl y)).inv_right).symm.symm

theorem zpowers_cases_of_mul_self {x : G} (hx : x * x = 1) :
    ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := by
  intro y hy
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk := Int.mul_ediv_add_emod k 2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hk, h0, add_zero, zpow_mul, zpow_ofNat, hx2, one_zpow]
  · right
    rw [← hk, h1, zpow_add, zpow_mul, zpow_ofNat, hx2, one_zpow, one_mul, zpow_one]

theorem mem_of_index_two_of_odd {X : Type*} [Group X] {Y : Subgroup X} (hY : Y.index = 2)
    {x : X} (hx : Odd (orderOf x)) : x ∈ Y := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x * (x ^ 2) ^ k = 1 := by
    rw [← pow_mul, ← pow_succ', show 2 * k + 1 = orderOf x by omega, pow_orderOf_eq_one]
  rw [eq_inv_of_mul_eq_one_left h1]
  exact Y.inv_mem (Y.pow_mem (Subgroup.sq_mem_of_index_two hY x) k)

variable {t s d : G} {J B W : Subgroup G}

namespace LocalData

variable (h : LocalData t s d J B W)
include h

theorem s_mem_C : s ∈ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.ts.symm

theorem d_mem_C : d ∈ Subgroup.centralizer ({t} : Set G) := h.J_le h.d_mem

theorem W_le_J : W ≤ J := fun x hx => ((h.W_mem x).mp hx).1

theorem W_comm_s : ∀ w ∈ W, w * s = s * w := fun x hx => ((h.W_mem x).mp hx).2.1

theorem W_odd : ∀ w ∈ W, Odd (orderOf w) := fun x hx => ((h.W_mem x).mp hx).2.2

theorem W_comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  have := h.W_cyclic
  intro x hx y hy
  have hc := (IsCyclic.commGroup (α := W)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val hc

theorem t_comm_J : ∀ x ∈ J, t * x = x * t := fun _ hx =>
  (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le hx)).symm

theorem t_comm_W : ∀ w ∈ W, t * w = w * t := fun w hw => h.t_comm_J w (h.W_le_J hw)

theorem tW_comm : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ W, x * y = y * x := by
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ((Commute.zpow_left (h.t_comm_W y hy) k))

theorem zpowers_t_cases : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := by
  intro x hx
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h.t_sq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk := Int.mul_ediv_add_emod k 2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hk, h0, add_zero, zpow_mul, zpow_ofNat, ht2, one_zpow]
  · right
    rw [← hk, h1, zpow_add, zpow_mul, zpow_ofNat, ht2, one_zpow, one_mul, zpow_one]

theorem s_inv_eq : s⁻¹ = s := (eq_inv_of_mul_eq_one_left h.s_sq).symm

theorem t_inv_eq : t⁻¹ = t := (eq_inv_of_mul_eq_one_left h.t_sq).symm

theorem t_orderOf : orderOf t = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne_one

theorem not_odd_t : ¬ Odd (orderOf t) := by
  rw [h.t_orderOf]
  decide

theorem B_comm_W : ∀ x ∈ B, ∀ w ∈ W, x * w = w * x := fun x hx w hw =>
  (h.JB_comm w (h.W_le_J hw) x hx).symm

theorem tW_s_comm : ∀ x ∈ Subgroup.zpowers t ⊔ W, x * s = s * x := by
  intro x hx
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup h.tW_comm hx
  rcases h.zpowers_t_cases a ha with ha1 | ha1 <;> rw [ha1]
  · rw [one_mul]
    exact h.W_comm_s w hw
  · rw [mul_assoc, h.W_comm_s w hw, ← mul_assoc, h.ts, mul_assoc]

theorem tW_le_C : Subgroup.zpowers t ⊔ W ≤ Subgroup.centralizer ({t} : Set G) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact h.W_le_J.trans h.J_le

theorem tW_sq_cases {x : G} (hx : x ∈ Subgroup.zpowers t ⊔ W) (hx2 : x * x = 1) :
    x = 1 ∨ x = t := by
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup h.tW_comm hx
  have ha2 : a * a = 1 := by
    rcases h.zpowers_t_cases a ha with ha1 | ha1 <;> rw [ha1]
    · exact one_mul 1
    · exact h.t_sq
  have hw2 : w * w = 1 := by
    have hc := h.tW_comm a ha w hw
    have e : a * w * (a * w) = a * a * (w * w) := by
      calc a * w * (a * w) = a * (w * a) * w := by group
        _ = a * (a * w) * w := by rw [hc]
        _ = a * a * (w * w) := by group
    rw [e, ha2, one_mul] at hx2
    exact hx2
  rw [eq_one_of_mul_self_eq_one_of_odd (h.W_odd w hw) hw2, mul_one]
  exact h.zpowers_t_cases a ha

theorem mem_W_of_odd {x : G} (hx : x ∈ Subgroup.zpowers t ⊔ W) (hodd : Odd (orderOf x)) :
    x ∈ W := by
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup h.tW_comm hx
  rcases h.zpowers_t_cases a ha with ha1 | ha1
  · rwa [ha1, one_mul]
  · exfalso
    apply h.not_odd_t
    rw [ha1] at hodd
    have hc : Commute t w := h.t_comm_W w hw
    exact odd_orderOf_of_mul hc hodd (h.W_odd w hw)

theorem mem_of_commute (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) {x : G} (hx : x ∈ J)
    (hc : ∀ w ∈ W₀, x * w = w * x) : x ∈ Subgroup.zpowers t ⊔ W := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  exact h.CJs x hx (h.cent_W w (hW₀ hw) hw1' x hx (hc w hw))

theorem mem_of_mem_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) {x : G}
    (hx : x ∈ J) (hxN : x ∈ Subgroup.normalizer (W₀ : Set G)) :
    x ∈ Subgroup.zpowers t ⊔ W ∨ d⁻¹ * x ∈ Subgroup.zpowers t ⊔ W := by
  have hsi := h.s_inv_eq
  obtain ⟨k, hkdef⟩ : ∃ k, k = x * s * x⁻¹ * s := ⟨_, rfl⟩
  have hkJ : k ∈ J := by
    have h1 : s * x⁻¹ * s⁻¹ ∈ J := h.J_conj s h.s_mem_C x⁻¹ (J.inv_mem hx)
    rw [hsi] at h1
    have : k = x * (s * x⁻¹ * s) := by rw [hkdef]; group
    rw [this]
    exact J.mul_mem hx h1
  have hkc : ∀ w ∈ W₀, k * w = w * k := by
    intro w hw
    have hw' : x⁻¹ * w * x ∈ W₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) w).mp hw
      simpa using this
    have h1 : s * w = w * s := (h.W_comm_s w (hW₀ hw)).symm
    have h2 : s * (x⁻¹ * w * x) = x⁻¹ * w * x * s := (h.W_comm_s _ (hW₀ hw')).symm
    calc k * w = x * s * x⁻¹ * (s * w) := by rw [hkdef]; group
      _ = x * s * x⁻¹ * (w * s) := by rw [h1]
      _ = x * (s * (x⁻¹ * w * x)) * x⁻¹ * s := by group
      _ = x * (x⁻¹ * w * x * s) * x⁻¹ * s := by rw [h2]
      _ = w * k := by rw [hkdef]; group
  have hk := h.mem_of_commute W₀ hW₀ hne hkJ hkc
  have hks : k * s = s * k := h.tW_s_comm k hk
  have hk2 : k * k = 1 := by
    have hy : x * s * x⁻¹ * (x * s * x⁻¹) = 1 := by
      calc x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
        _ = 1 := by rw [h.s_sq, mul_one, mul_inv_cancel]
    have hy' : k * s = x * s * x⁻¹ := by
      rw [hkdef, mul_assoc (x * s * x⁻¹) s s, h.s_sq, mul_one]
    calc k * k = k * (s * s) * k := by rw [h.s_sq, mul_one]
      _ = k * s * (s * k) := by group
      _ = k * s * (k * s) := by rw [hks]
      _ = 1 := by rw [hy', hy]
  rcases h.tW_sq_cases hk hk2 with hk1 | hkt
  · left
    apply h.CJs x hx
    have : x * s * x⁻¹ * s = 1 := hkdef ▸ hk1
    calc x * s = x * s * x⁻¹ * s * (s * x) := by
          rw [mul_assoc (x * s * x⁻¹) s (s * x), ← mul_assoc s s x, h.s_sq, one_mul]; group
      _ = s * x := by rw [this, one_mul]
  · right
    apply h.CJs (d⁻¹ * x) (J.mul_mem (J.inv_mem h.d_mem) hx)
    have hxs : x * s * x⁻¹ = t * s := by
      have : x * s * x⁻¹ * s = t := hkdef ▸ hkt
      calc x * s * x⁻¹ = x * s * x⁻¹ * s * s := by rw [mul_assoc _ s s, h.s_sq, mul_one]
        _ = t * s := by rw [this]
    have hds := h.d_s
    calc d⁻¹ * x * s = d⁻¹ * (x * s * x⁻¹) * x := by group
      _ = d⁻¹ * (d * s * d⁻¹) * x := by rw [hxs, hds]
      _ = s * (d⁻¹ * x) := by group

theorem B_le_centralizer_W : B ≤ Subgroup.centralizer (W : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (h.B_comm_W x hx w hw).symm

omit h in
theorem mem_normalizer_of_commute (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) {x : G}
    (hx : ∀ w ∈ W, x * w = w * x) : x ∈ Subgroup.normalizer (W₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hx w (hW₀ hw), mul_inv_cancel_right]
    exact hw
  · intro hw
    have hw' := hW₀ hw
    have hxw := hx _ hw'
    have : w = x⁻¹ * (x * w * x⁻¹) * x := by group
    rw [this]
    have hcomm : x⁻¹ * (x * w * x⁻¹) * x = x * w * x⁻¹ := by
      have h2 : (x * w * x⁻¹) * x = x * (x * w * x⁻¹) := hxw.symm
      calc x⁻¹ * (x * w * x⁻¹) * x = x⁻¹ * ((x * w * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * w * x⁻¹)) := by rw [h2]
        _ = x * w * x⁻¹ := by group
    rw [hcomm]
    exact hw

omit h in
theorem mem_normalizer_of_inv (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) {g : G}
    (hg : ∀ w ∈ W, g * w * g⁻¹ = w⁻¹) : g ∈ Subgroup.normalizer (W₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hg x (hW₀ hx)]
    exact W₀.inv_mem hx
  · intro hx
    have hu : g * (g * x * g⁻¹)⁻¹ * g⁻¹ = g * x * g⁻¹ := by
      rw [hg _ (W.inv_mem (hW₀ hx)), inv_inv]
    have h1 : (g * x * g⁻¹)⁻¹ = g⁻¹ * (g * x * g⁻¹) * g := by
      calc (g * x * g⁻¹)⁻¹ = g⁻¹ * (g * (g * x * g⁻¹)⁻¹ * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hu]
    have : x = (g * x * g⁻¹)⁻¹ := by rw [h1]; group
    rw [this]
    exact W₀.inv_mem hx

theorem s_mem_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) :
    s ∈ Subgroup.normalizer (W₀ : Set G) :=
  mem_normalizer_of_commute W₀ hW₀ fun w hw => (h.W_comm_s w hw).symm

theorem B_le_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) :
    B ≤ Subgroup.normalizer (W₀ : Set G) := fun y hy =>
  mem_normalizer_of_commute W₀ hW₀ fun w hw => h.B_comm_W y hy w hw

theorem W_le_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) :
    W ≤ Subgroup.normalizer (W₀ : Set G) := fun y hy =>
  mem_normalizer_of_commute W₀ hW₀ fun w hw => h.W_comm y hy w hw

theorem d_mem_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) :
    d ∈ Subgroup.normalizer (W₀ : Set G) :=
  mem_normalizer_of_inv W₀ hW₀ h.d_inv

theorem normalizer_cases (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) {c : G}
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) (hcN : c ∈ Subgroup.normalizer (W₀ : Set G)) :
    ∃ a ∈ Subgroup.zpowers t ⊔ W, ∃ y ∈ B, ∃ i j : ℕ, i < 2 ∧ j < 2 ∧
      c = d ^ i * a * y * s ^ j := by
  obtain ⟨x, hx, y, hy, hc'⟩ := h.cover c hc
  have hyN := h.B_le_normalizer W₀ hW₀ hy
  have hsN := h.s_mem_normalizer W₀ hW₀
  rcases hc' with rfl | rfl
  · have hxN : x ∈ Subgroup.normalizer (W₀ : Set G) := by
      have : x = x * y * y⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hyN)
    rcases h.mem_of_mem_normalizer W₀ hW₀ hne hx hxN with hxa | hxa
    · exact ⟨x, hxa, y, hy, 0, 0, by norm_num, by norm_num, by group⟩
    · exact ⟨d⁻¹ * x, hxa, y, hy, 1, 0, by norm_num, by norm_num, by group⟩
  · have hxN : x ∈ Subgroup.normalizer (W₀ : Set G) := by
      have : x = x * y * s * s⁻¹ * y⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hsN))
        (Subgroup.inv_mem _ hyN)
    rcases h.mem_of_mem_normalizer W₀ hW₀ hne hx hxN with hxa | hxa
    · exact ⟨x, hxa, y, hy, 0, 1, by norm_num, by norm_num, by group⟩
    · exact ⟨d⁻¹ * x, hxa, y, hy, 1, 1, by norm_num, by norm_num, by group⟩

theorem d_mul_sq {a : G} (ha : a ∈ Subgroup.zpowers t ⊔ W) : d * a * (d * a) = t := by
  obtain ⟨a₁, ha₁, w, hw, rfl⟩ := exists_mul_of_mem_sup h.tW_comm ha
  have hdw := h.d_inv w hw
  have hdt : d * t = t * d := (h.t_comm_J d h.d_mem).symm
  have htw : t * w = w * t := h.t_comm_W w hw
  have hdw' : d * w = w⁻¹ * d := by
    calc d * w = d * w * d⁻¹ * d := by group
      _ = w⁻¹ * d := by rw [hdw]
  rcases h.zpowers_t_cases a₁ ha₁ with ha1 | ha1 <;> rw [ha1]
  · calc d * (1 * w) * (d * (1 * w)) = d * w * d * w := by group
      _ = w⁻¹ * (d * d) * w := by rw [hdw']; group
      _ = t := by rw [h.d_sq, mul_assoc, htw, inv_mul_cancel_left]
  · calc d * (t * w) * (d * (t * w)) = (d * t) * w * (d * t) * w := by group
      _ = t * (d * w) * t * d * w := by rw [hdt]; group
      _ = t * w⁻¹ * (d * t) * d * w := by rw [hdw']; group
      _ = t * w⁻¹ * t * (d * d) * w := by rw [hdt]; group
      _ = t * (w⁻¹ * (t * t) * w) := by rw [h.d_sq]; group
      _ = t := by rw [h.t_sq, mul_one, inv_mul_cancel, mul_one]

theorem mem_sup_of_odd_of_mem_normalizer (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥)
    {c : G} (hc : c ∈ Subgroup.centralizer ({t} : Set G))
    (hcN : c ∈ Subgroup.normalizer (W₀ : Set G)) (hodd : Odd (orderOf c)) : c ∈ W ⊔ B := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup h.JB_comm (h.odd_mem _ hc hodd)
  have hyN := h.B_le_normalizer W₀ hW₀ hy
  have hxN : x ∈ Subgroup.normalizer (W₀ : Set G) := by
    have : x = x * y * y⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hyN)
  have hxy : Commute x y := h.JB_comm x hx y hy
  have hxodd : Odd (orderOf x) := odd_orderOf_of_mul hxy hodd (h.B_odd y hy)
  rcases h.mem_of_mem_normalizer W₀ hW₀ hne hx hxN with hxa | hxa
  · exact Subgroup.mul_mem_sup (h.mem_W_of_odd hxa hxodd) hy
  · exfalso
    have hsq : x * x = t := by
      have := h.d_mul_sq hxa
      rwa [mul_inv_cancel_left] at this
    have hmem := mem_zpowers_sq_of_odd hxodd
    rw [hsq] at hmem
    rcases h.zpowers_t_cases _ hmem with h1 | h1
    · rw [h1, one_mul] at hsq
      exact h.t_ne_one hsq.symm
    · rw [h1] at hsq
      apply h.t_ne_one
      calc t = t * t * t⁻¹ := by group
        _ = 1 := by rw [hsq, mul_inv_cancel]

theorem centralizer_inf_normalizer_eq (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) :
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G) =
      W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) := by
  apply le_antisymm
  · rintro c ⟨hc, hcN⟩
    obtain ⟨a, ha, y, hy, i, j, -, -, rfl⟩ := h.normalizer_cases W₀ hW₀ hne hc hcN
    set X : Subgroup G := W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s)
    have hdX : d ∈ X := Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
    have hsX : s ∈ X := Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hyX : y ∈ X := Subgroup.mem_sup_left (Subgroup.mem_sup_right hy)
    have haX : a ∈ X := by
      refine (sup_le ?_ ?_ : Subgroup.zpowers t ⊔ W ≤ X) ha
      · rw [Subgroup.zpowers_le, ← h.d_sq]
        exact X.mul_mem hdX hdX
      · exact le_sup_left.trans le_sup_left
    exact X.mul_mem (X.mul_mem (X.mul_mem (X.pow_mem hdX i) haX) hyX) (X.pow_mem hsX j)
  · have hC : W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) ≤
        Subgroup.centralizer ({t} : Set G) := by
      refine sup_le (sup_le (h.W_le_J.trans h.J_le) h.B_le) (sup_le ?_ ?_)
      · rw [Subgroup.zpowers_le]
        exact h.d_mem_C
      · rw [Subgroup.zpowers_le]
        exact h.s_mem_C
    have hN : W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) ≤
        Subgroup.normalizer (W₀ : Set G) := by
      refine sup_le (sup_le (h.W_le_normalizer W₀ hW₀) (h.B_le_normalizer W₀ hW₀))
        (sup_le ?_ ?_)
      · rw [Subgroup.zpowers_le]
        exact h.d_mem_normalizer W₀ hW₀
      · rw [Subgroup.zpowers_le]
        exact h.s_mem_normalizer W₀ hW₀
    exact le_inf hC hN

theorem eq_of_isPGroup_of_le (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥)
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPle : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (W₀ : Set G))
    (hDP : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤ P) :
    P = Subgroup.zpowers d ⊔ Subgroup.zpowers s := by
  apply le_antisymm _ hDP
  intro c hc
  obtain ⟨a, ha, z, hz, i, j, -, -, rfl⟩ :=
    h.normalizer_cases W₀ hW₀ hne (hPle hc).1 (hPle hc).2
  have hdP : d ∈ P := hDP (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  have hsP : s ∈ P := hDP (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hazP : a * z ∈ P := by
    have : a * z = (d ^ i)⁻¹ * (d ^ i * a * z * s ^ j) * (s ^ j)⁻¹ := by group
    rw [this]
    exact P.mul_mem (P.mul_mem (P.inv_mem (P.pow_mem hdP i)) hc) (P.inv_mem (P.pow_mem hsP j))
  obtain ⟨a₁, ha₁, w, hw, rfl⟩ := exists_mul_of_mem_sup h.tW_comm ha
  set D8 : Subgroup G := Subgroup.zpowers d ⊔ Subgroup.zpowers s
  have ha₁D : a₁ ∈ D8 := by
    rcases h.zpowers_t_cases a₁ ha₁ with ha1 | ha1 <;> rw [ha1]
    · exact D8.one_mem
    · rw [← h.d_sq]
      exact D8.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  have hwz : w * z = 1 := by
    have hcomm : Commute w z := (h.B_comm_W z hz w hw).symm
    have hodd : Odd (orderOf (w * z)) :=
      odd_orderOf_mul_of_commute hcomm (h.W_odd w hw) (h.B_odd z hz)
    have ha₁c : Commute a₁ (w * z) := by
      rcases h.zpowers_t_cases a₁ ha₁ with ha1 | ha1 <;> rw [ha1]
      · exact Commute.one_left _
      · refine Commute.mul_right (h.t_comm_W w hw) ?_
        exact (Subgroup.mem_centralizer_singleton_iff.mp (h.B_le hz)).symm
    have ha₁2 : a₁ ^ 2 = 1 := by
      rcases h.zpowers_t_cases a₁ ha₁ with ha1 | ha1 <;> rw [ha1]
      · exact one_pow 2
      · rw [pow_two]
        exact h.t_sq
    obtain ⟨k, hk⟩ := hP ⟨a₁ * w * z, hazP⟩
    have hk' : (a₁ * (w * z)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa [mul_assoc] using this
    have hk2 : (w * z) ^ 2 ^ (k + 1) = 1 := by
      have e : (a₁ * (w * z)) ^ 2 ^ (k + 1) = a₁ ^ 2 ^ (k + 1) * (w * z) ^ 2 ^ (k + 1) :=
        ha₁c.mul_pow _
      have ha : a₁ ^ 2 ^ (k + 1) = 1 := by
        rw [pow_succ' 2 k, pow_mul, ha₁2, one_pow]
      rw [ha, one_mul] at e
      rw [← e, pow_succ, pow_mul, hk', one_pow]
    have hdvd := orderOf_dvd_of_pow_eq_one hk2
    have hcop : Nat.Coprime (orderOf (w * z)) (2 ^ (k + 1)) :=
      (Nat.coprime_two_right.mpr hodd).pow_right (k + 1)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have : d ^ i * (a₁ * w) * z * s ^ j = d ^ i * a₁ * (w * z) * s ^ j := by group
  rw [this, hwz, mul_one]
  exact D8.mul_mem (D8.mul_mem (D8.pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) i)
    ha₁D) (D8.pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)) j)

end LocalData

end CFSG.Semidihedral.FixedCoreNontrivial
