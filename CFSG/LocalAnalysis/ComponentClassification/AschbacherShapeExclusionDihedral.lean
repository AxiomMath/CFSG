module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic
public import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup
open scoped commutatorElement

namespace DihedralTimesTwo

variable {X : Type*} [Group X]

structure Data (T : Subgroup X) (r u e : X) (n : ℕ) : Prop where
  hn : 2 ≤ n
  rT : r ∈ T
  uT : u ∈ T
  eT : e ∈ T
  ro : orderOf r = 2 ^ n
  u2 : u ^ 2 = 1
  e2 : e ^ 2 = 1
  ur : u * r * u⁻¹ = r⁻¹
  er : e * r = r * e
  eu : e * u = u * e
  nf : ∀ g ∈ T, ∃ i : ℤ, g = r ^ i ∨ g = r ^ i * e ∨ g = u * r ^ i ∨ g = u * r ^ i * e
  eD : ∀ i : ℤ, e ≠ r ^ i ∧ e ≠ u * r ^ i

theorem mem_normalizer_of_inv {r b : X} (hb : ∀ k : ℤ, b * r ^ k * b⁻¹ = r ^ (-k)) :
    b ∈ normalizer (zpowers r : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    rw [hb k]
    exact zpow_mem (mem_zpowers r) _
  · intro hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg
    have hb' := hb (-k)
    rw [neg_neg] at hb'
    have : g = r ^ (-k) := by
      calc g = b⁻¹ * (b * g * b⁻¹) * b := by group
        _ = b⁻¹ * (b * r ^ (-k) * b⁻¹) * b := by rw [← hk, hb']
        _ = r ^ (-k) := by group
    rw [this]
    exact zpow_mem (mem_zpowers r) _

namespace Data

variable {T : Subgroup X} {r u e : X} {n : ℕ}

theorem u_inv (h : Data T r u e n) : u⁻¹ = u := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, h.u2]

theorem e_inv (h : Data T r u e n) : e⁻¹ = e := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, h.e2]

theorem u_mul_u (h : Data T r u e n) : u * u = 1 := by rw [← pow_two, h.u2]

theorem e_mul_e (h : Data T r u e n) : e * e = 1 := by rw [← pow_two, h.e2]

theorem conj_zpow (h : Data T r u e n) (k : ℤ) : u * r ^ k * u⁻¹ = r ^ (-k) := by
  rw [← _root_.conj_zpow, h.ur, inv_zpow']

theorem zpow_mul_u (h : Data T r u e n) (k : ℤ) : r ^ k * u = u * r ^ (-k) := by
  have := h.conj_zpow (-k)
  rw [neg_neg] at this
  calc r ^ k * u = (u * r ^ (-k) * u⁻¹) * u := by rw [this]
    _ = u * r ^ (-k) := by group

theorem e_comm_zpow (h : Data T r u e n) (k : ℤ) : e * r ^ k = r ^ k * e :=
  (Commute.zpow_right h.er k).eq

@[expose] def z (_ : Data T r u e n) : X := r ^ (2 : ℤ) ^ (n - 1)

theorem z_def (h : Data T r u e n) : h.z = r ^ (2 : ℤ) ^ (n - 1) := rfl

theorem zpow_eq_one_iff (h : Data T r u e n) (k : ℤ) : r ^ k = 1 ↔ (2 ^ n : ℤ) ∣ k := by
  rw [orderOf_dvd_iff_zpow_eq_one.symm, h.ro]
  push_cast
  rfl

theorem z_sq (h : Data T r u e n) : h.z ^ 2 = 1 := by
  have h2 : ((2 : ℤ) ^ (n - 1)) * 2 = 2 ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel (by have := h.hn; omega)]
  rw [z_def, ← zpow_natCast, ← zpow_mul, h.zpow_eq_one_iff]
  push_cast
  exact ⟨1, by rw [mul_one, h2]⟩

theorem z_ne_one (h : Data T r u e n) : h.z ≠ 1 := by
  rw [z_def, Ne, h.zpow_eq_one_iff]
  rintro ⟨c, hc⟩
  have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by have := h.hn; omega)]
  rw [h2] at hc
  have : (1 : ℤ) = 2 * c := by nlinarith
  omega

theorem z_comm_u (h : Data T r u e n) : h.z * u = u * h.z := by
  rw [z_def, h.zpow_mul_u]
  congr 1
  rw [zpow_neg, ← h.z_def, inv_eq_iff_mul_eq_one, ← pow_two, h.z_sq]

theorem sq_eq_zpow (h : Data T r u e n) {g : X} (hg : g ∈ T) : ∃ k : ℤ, g ^ 2 = r ^ (2 * k) := by
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ := h.nf g hg
  · exact ⟨i, by rw [← zpow_natCast, ← zpow_mul, mul_comm]; rfl⟩
  · refine ⟨i, ?_⟩
    calc (r ^ i * e) ^ 2 = r ^ i * (e * r ^ i) * e := by rw [pow_two]; group
      _ = r ^ i * r ^ i * (e * e) := by rw [h.e_comm_zpow]; group
      _ = r ^ (2 * i) := by rw [h.e_mul_e, mul_one, ← zpow_add, two_mul]
  · refine ⟨0, ?_⟩
    rw [mul_zero, zpow_zero]
    calc (u * r ^ i) ^ 2 = u * (r ^ i * u) * r ^ i := by rw [pow_two]; group
      _ = (u * u) * (r ^ (-i) * r ^ i) := by rw [h.zpow_mul_u]; group
      _ = 1 := by simp [h.u_mul_u]
  · refine ⟨0, ?_⟩
    rw [mul_zero, zpow_zero]
    calc (u * r ^ i * e) ^ 2 = u * r ^ i * (e * u) * r ^ i * e := by rw [pow_two]; group
      _ = u * (r ^ i * u) * (e * r ^ i) * e := by rw [h.eu]; group
      _ = (u * u) * (r ^ (-i) * r ^ i) * (e * e) := by
          rw [h.zpow_mul_u, h.e_comm_zpow]; group
      _ = 1 := by simp [h.u_mul_u, h.e_mul_e]

theorem zpow_sq_eq_one (h : Data T r u e n) {k : ℤ} (hk : (r ^ k) ^ 2 = 1) :
    r ^ k = 1 ∨ r ^ k = h.z := by
  have h2 : (2 : ℤ) ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by have := h.hn; omega)]
  rw [← zpow_natCast, ← zpow_mul, h.zpow_eq_one_iff, h2] at hk
  obtain ⟨c, hc⟩ := hk
  have hk' : k = 2 ^ (n - 1) * c := by
    push_cast at hc
    linarith
  rw [hk', zpow_mul, ← h.z_def]
  obtain ⟨d, rfl | rfl⟩ := Int.even_or_odd' c
  · left
    rw [zpow_mul, zpow_two, ← pow_two, h.z_sq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, h.z_sq, one_zpow, one_mul, zpow_one]

theorem involution_cases (h : Data T r u e n) {g : X} (hg : g ∈ T) (hg2 : g ^ 2 = 1) :
    g = 1 ∨ g = h.z ∨ g = e ∨ g = h.z * e ∨ (∃ i : ℤ, g = u * r ^ i) ∨
      ∃ i : ℤ, g = u * r ^ i * e := by
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ := h.nf g hg
  · rcases h.zpow_sq_eq_one hg2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hsq : (r ^ i) ^ 2 = 1 := by
      have : (r ^ i * e) ^ 2 = (r ^ i) ^ 2 * e ^ 2 :=
        (Commute.mul_pow (h.e_comm_zpow i).symm 2)
      rwa [this, h.e2, mul_one] at hg2
    rcases h.zpow_sq_eq_one hsq with h1 | h1
    · rw [h1, one_mul]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h1]
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))))

theorem e_ne_one (h : Data T r u e n) : e ≠ 1 := by
  have := (h.eD 0).1
  rwa [zpow_zero] at this

theorem orderOf_e (h : Data T r u e n) : orderOf e = 2 := orderOf_eq_prime h.e2 h.e_ne_one

theorem e_ne_zpow_two (h : Data T r u e n) (k : ℤ) : e ≠ r ^ (2 * k) ∧ h.z * e ≠ r ^ (2 * k) := by
  refine ⟨(h.eD _).1, fun he => (h.eD (2 * k - 2 ^ (n - 1))).1 ?_⟩
  calc e = h.z⁻¹ * (h.z * e) := by group
    _ = r ^ (2 * k - 2 ^ (n - 1)) := by
        rw [he, h.z_def, ← zpow_neg, ← zpow_add]
        ring_nf

theorem central (h : Data T r u e n) :
    h.z ∈ centralizer (T : Set X) ∧ e ∈ centralizer (T : Set X) ∧
      h.z * e ∈ centralizer (T : Set X) := by
  have hcomm : ∀ c : X, (∀ k : ℤ, c * r ^ k = r ^ k * c) → c * u = u * c → c * e = e * c →
      c ∈ centralizer (T : Set X) := by
    intro c hr hu he
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl | rfl | rfl | rfl⟩ := h.nf g hg
    · exact (hr i).symm
    · calc r ^ i * e * c = r ^ i * (e * c) := by group
        _ = c * (r ^ i * e) := by rw [← he, ← mul_assoc, ← hr i]; group
    · calc u * r ^ i * c = u * (r ^ i * c) := by group
        _ = c * (u * r ^ i) := by rw [← hr i, ← mul_assoc, ← hu]; group
    · calc u * r ^ i * e * c = u * r ^ i * (e * c) := by group
        _ = c * (u * r ^ i * e) := by
            rw [← he, ← mul_assoc, mul_assoc u, ← hr i, ← mul_assoc, ← hu]; group
  have hz : h.z ∈ centralizer (T : Set X) := by
    refine hcomm _ (fun k => ?_) h.z_comm_u ((h.e_comm_zpow _).symm)
    rw [h.z_def, ← zpow_add, ← zpow_add, add_comm]
  have he : e ∈ centralizer (T : Set X) :=
    hcomm _ h.e_comm_zpow h.eu rfl
  refine ⟨hz, he, mul_mem hz he⟩

theorem u_not_mem (h : Data T r u e n) : u ∉ zpowers r := by
  intro hu
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hu
  have hc : u * r * u⁻¹ = r := by rw [← hj]; group
  rw [h.ur] at hc
  have hr2 : r ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hc]
    exact inv_mul_cancel r
  have hdvd := orderOf_dvd_of_pow_eq_one hr2
  rw [h.ro] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.hn
  omega

theorem ue_not_mem (h : Data T r u e n) : u * e ∉ zpowers r := by
  intro hue
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hue
  apply (h.eD j).2
  calc e = u⁻¹ * (u * e) := by group
    _ = u * r ^ j := by rw [← hj, h.u_inv]

theorem u_mem_normalizer (h : Data T r u e n) : u ∈ normalizer (zpowers r : Set X) :=
  mem_normalizer_of_inv h.conj_zpow

theorem ue_mem_normalizer (h : Data T r u e n) : u * e ∈ normalizer (zpowers r : Set X) :=
  mem_normalizer_of_inv fun k => by
    calc u * e * r ^ k * (u * e)⁻¹ = u * (e * r ^ k * e⁻¹) * u⁻¹ := by group
      _ = r ^ (-k) := by rw [h.e_comm_zpow, mul_inv_cancel_right, h.conj_zpow]

theorem u_sq_mem (h : Data T r u e n) : u ^ 2 ∈ zpowers r := by
  rw [h.u2]
  exact one_mem _

theorem ue_sq_mem (h : Data T r u e n) : (u * e) ^ 2 ∈ zpowers r := by
  have : (u * e) ^ 2 = 1 := by
    rw [(Commute.mul_pow h.eu.symm 2), h.u2, h.e2, one_mul]
  rw [this]
  exact one_mem _

theorem mem_D (h : Data T r u e n) {g : X} (hg : g ∈ zpowers r ⊔ zpowers u) :
    (∃ i : ℤ, g = r ^ i) ∨ ∃ i : ℤ, g = u * r ^ i := by
  rcases (Lemma37.mem_sup_zpowers_iff h.u_mem_normalizer h.u_sq_mem).1 hg with h1 | h1
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    exact Or.inl ⟨i, hi.symm⟩
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    refine Or.inr ⟨i, ?_⟩
    rw [hi, h.u_inv, ← mul_assoc, h.u_mul_u, one_mul]

theorem mem_D' (h : Data T r u e n) {g : X} (hg : g ∈ zpowers r ⊔ zpowers (u * e)) :
    (∃ i : ℤ, g = r ^ i) ∨ ∃ i : ℤ, g = u * r ^ i * e := by
  rcases (Lemma37.mem_sup_zpowers_iff h.ue_mem_normalizer h.ue_sq_mem).1 hg with h1 | h1
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    exact Or.inl ⟨i, hi.symm⟩
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    refine Or.inr ⟨i, ?_⟩
    calc g = u * e * ((u * e)⁻¹ * g) := by group
      _ = u * r ^ i * e := by rw [← hi, mul_assoc, h.e_comm_zpow, ← mul_assoc]

theorem e_not_mem_D (h : Data T r u e n) : e ∉ zpowers r ⊔ zpowers u := by
  intro he
  rcases h.mem_D he with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (h.eD i).1 hi
  · exact (h.eD i).2 hi

theorem e_not_mem_D' (h : Data T r u e n) : e ∉ zpowers r ⊔ zpowers (u * e) := by
  intro he
  rcases h.mem_D' he with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (h.eD i).1 hi
  · apply h.u_not_mem
    have h1 : u * r ^ i = 1 := by
      calc u * r ^ i = u * r ^ i * e * e⁻¹ := by group
        _ = 1 := by rw [← hi, mul_inv_cancel]
    have : u = r ^ (-i) := by
      calc u = u * r ^ i * (r ^ i)⁻¹ := by group
        _ = r ^ (-i) := by rw [h1, one_mul, zpow_neg]
    rw [this]
    exact zpow_mem (mem_zpowers r) _

theorem D_le (h : Data T r u e n) : zpowers r ⊔ zpowers u ≤ T :=
  sup_le (zpowers_le.2 h.rT) (zpowers_le.2 h.uT)

theorem D'_le (h : Data T r u e n) : zpowers r ⊔ zpowers (u * e) ≤ T :=
  sup_le (zpowers_le.2 h.rT) (zpowers_le.2 (mul_mem h.uT h.eT))

theorem card_D [Finite X] (h : Data T r u e n) :
    Nat.card (zpowers r ⊔ zpowers u : Subgroup X) = 2 * 2 ^ n := by
  rw [Lemma37.card_sup_zpowers h.u_mem_normalizer h.u_sq_mem h.u_not_mem, Nat.card_zpowers,
    h.ro]

theorem card_D' [Finite X] (h : Data T r u e n) :
    Nat.card (zpowers r ⊔ zpowers (u * e) : Subgroup X) = 2 * 2 ^ n := by
  rw [Lemma37.card_sup_zpowers h.ue_mem_normalizer h.ue_sq_mem h.ue_not_mem, Nat.card_zpowers,
    h.ro]

theorem card_T [Finite X] (h : Data T r u e n) : Nat.card T = 2 * (2 * 2 ^ n) := by
  set D := zpowers r ⊔ zpowers u with hD
  have heN : e ∈ normalizer (D : Set X) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
    exact (mem_centralizer_iff.1 h.central.2.1 g (h.D_le hg))
  have he2 : e ^ 2 ∈ D := by rw [h.e2]; exact one_mem _
  have hTeq : D ⊔ zpowers e = T := by
    apply le_antisymm (sup_le h.D_le (zpowers_le.2 h.eT))
    intro g hg
    have hrD : ∀ i : ℤ, r ^ i ∈ D := fun i => mem_sup_left (zpow_mem (mem_zpowers r) i)
    have huD : ∀ i : ℤ, u * r ^ i ∈ D := fun i =>
      mul_mem (mem_sup_right (mem_zpowers u)) (hrD i)
    have heD : e ∈ D ⊔ zpowers e := mem_sup_right (mem_zpowers e)
    obtain ⟨i, rfl | rfl | rfl | rfl⟩ := h.nf g hg
    · exact mem_sup_left (hrD i)
    · exact mul_mem (mem_sup_left (hrD i)) heD
    · exact mem_sup_left (huD i)
    · exact mul_mem (mem_sup_left (huD i)) heD
  rw [← hTeq, Lemma37.card_sup_zpowers heN he2 h.e_not_mem_D, h.card_D]

theorem isConj_u (h : Data T r u e n) (i j : ℤ) : IsConj (u * r ^ i) (u * r ^ (i + 2 * j)) := by
  refine isConj_iff.2 ⟨r ^ (-j), ?_⟩
  calc r ^ (-j) * (u * r ^ i) * (r ^ (-j))⁻¹ = (r ^ (-j) * u) * r ^ i * r ^ j := by group
    _ = u * r ^ (i + 2 * j) := by rw [h.zpow_mul_u, neg_neg]; group

theorem isConj_ue (h : Data T r u e n) (i j : ℤ) :
    IsConj (u * r ^ i * e) (u * r ^ (i + 2 * j) * e) := by
  refine isConj_iff.2 ⟨r ^ (-j), ?_⟩
  calc r ^ (-j) * (u * r ^ i * e) * (r ^ (-j))⁻¹
      = (r ^ (-j) * u) * r ^ i * (e * r ^ j) := by group
    _ = u * r ^ (i + 2 * j) * e := by rw [h.zpow_mul_u, neg_neg, h.e_comm_zpow]; group

end Data

theorem isConj_map {Y : Type*} [Group Y] (α : X ≃* Y) {v w : X} (hvw : IsConj v w) :
    IsConj (α v) (α w) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hvw
  exact isConj_iff.2 ⟨α c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem isConj_of_conj (v c : X) : IsConj v (c⁻¹ * v * c) :=
  isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩

theorem exists_eq_add_two_mul {i j : ℤ} (h : Even (j - i)) : ∃ k : ℤ, j = i + 2 * k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by linarith⟩

variable {T : Subgroup X} {r u e : X} {n : ℕ}

theorem isolated_of_dihedral_times_two [Finite X] (hperf : commutator X = ⊤) (P : Sylow 2 X)
    (h : Data (P : Subgroup X) r u e n) (α : X ≃* X) (hαr : α r = r⁻¹) {a : ℤ} (ha : Odd a)
    (hαu : α u = u * r ^ a) (hαe : α e = e ∨ α e = h.z * e) :
    ∀ g : X, g⁻¹ * h.z * g ∈ (P : Subgroup X) → g⁻¹ * h.z * g = h.z := by
  set y₀ : X := r ^ (2 : ℤ) ^ (n - 2) with hy₀
  have hy₀P : y₀ ∈ (P : Subgroup X) := zpow_mem h.rT _
  have hy₀z : h.z = y₀ ^ 2 := by
    rw [hy₀, h.z_def, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, ← pow_succ,
      show n - 2 + 1 = n - 1 by have := h.hn; omega]
  have hnot : ∀ v, (v = e ∨ v = h.z * e) → ¬ IsConj h.z v := by
    intro v hv hzv
    obtain ⟨c, hc⟩ := isConj_iff.1 hzv
    have hvc : v ∈ centralizer ((P : Subgroup X) : Set X) := by
      rcases hv with rfl | rfl
      · exact h.central.2.1
      · exact h.central.2.2
    obtain ⟨y', hy'P, hy'⟩ := exists_sq_of_conj_central P hvc h.central.1
      (g := c) (by rw [← hc]; group) hy₀P hy₀z
    obtain ⟨k, hk⟩ := h.sq_eq_zpow hy'P
    rw [hk] at hy'
    rcases hv with rfl | rfl
    · exact (h.e_ne_zpow_two k).1 hy'
    · exact (h.e_ne_zpow_two k).2 hy'
  have hcardD : Nat.card (P : Subgroup X) =
      2 * Nat.card (zpowers r ⊔ zpowers u : Subgroup X) := by rw [h.card_T, h.card_D]
  have hcardD' : Nat.card (P : Subgroup X) =
      2 * Nat.card (zpowers r ⊔ zpowers (u * e) : Subgroup X) := by rw [h.card_T, h.card_D']
  have hsqc : ∀ c v : X, v ^ 2 = 1 → (c⁻¹ * v * c) ^ 2 = 1 := fun c v hv => by
    rw [show c⁻¹ * v * c = c⁻¹ * v * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hv]
    group
  have hnot_r : ∀ c : X, ∀ i : ℤ, c⁻¹ * e * c = r ^ i → False := by
    intro c i hci
    have hsq : (r ^ i) ^ 2 = 1 := by rw [← hci]; exact hsqc c e h.e2
    rcases h.zpow_sq_eq_one hsq with h1 | h1
    · apply h.e_ne_one
      calc e = c * (c⁻¹ * e * c) * c⁻¹ := by group
        _ = 1 := by rw [hci, h1]; group
    · exact hnot e (Or.inl rfl) ((isConj_of_conj e c).trans (by rw [hci, h1])).symm
  obtain ⟨c₀, hc₀⟩ := exists_conj_mem_of_index_two hperf P h.D_le hcardD h.eT h.e_not_mem_D
    h.orderOf_e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ℤ, IsConj e (u * r ^ i₀) := by
    rcases h.mem_D hc₀ with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact (hnot_r c₀ i hi).elim
    · exact ⟨i, by rw [← hi]; exact isConj_of_conj e c₀⟩
  obtain ⟨c₁, hc₁⟩ := exists_conj_mem_of_index_two hperf P h.D'_le hcardD' h.eT
    h.e_not_mem_D' h.orderOf_e
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ℤ, IsConj e (u * r ^ i₁ * e) := by
    rcases h.mem_D' hc₁ with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact (hnot_r c₁ i hi).elim
    · exact ⟨i, by rw [← hi]; exact isConj_of_conj e c₁⟩
  have hαpow : ∀ i : ℤ, α (r ^ i) = r ^ (-i) := fun i => by rw [map_zpow, hαr, inv_zpow']
  have hα₀ : IsConj (α e) (u * r ^ (a - i₀)) := by
    have := isConj_map α hi₀
    rwa [map_mul, hαu, hαpow, mul_assoc, ← zpow_add, ← sub_eq_add_neg] at this
  obtain ⟨b, hb⟩ := ha
  have hQ : ∀ w : X, (IsConj w e ∨ IsConj w (α e)) → IsConj w e ∨ IsConj w (h.z * e) := by
    rintro w (hw | hw)
    · exact Or.inl hw
    · rcases hαe with he | he
      · exact Or.inl (he ▸ hw)
      · exact Or.inr (he ▸ hw)
  have hU : ∀ i : ℤ, IsConj (u * r ^ i) e ∨ IsConj (u * r ^ i) (h.z * e) := by
    intro i
    apply hQ
    rcases Int.even_or_odd (i - i₀) with hev | ⟨j, hj⟩
    · obtain ⟨k, hk⟩ := exists_eq_add_two_mul hev
      left
      rw [hk]
      exact ((h.isConj_u i₀ k).symm.trans hi₀.symm)
    · right
      have hk : i = (a - i₀) + 2 * (j + i₀ - b) := by linarith
      rw [hk]
      exact (h.isConj_u (a - i₀) (j + i₀ - b)).symm.trans hα₀.symm
  obtain ⟨ε, hε, hα₁⟩ : ∃ ε : ℤ, Even ε ∧ IsConj (α e) (u * r ^ (a - i₁ + ε) * e) := by
    have hmap := isConj_map α hi₁
    rw [map_mul, map_mul, hαu, hαpow] at hmap
    rcases hαe with he | he
    · refine ⟨0, ⟨0, by ring⟩, ?_⟩
      rw [he] at hmap ⊢
      convert hmap using 1
      group
    · refine ⟨2 ^ (n - 1), ?_, ?_⟩
      · exact (Int.even_pow' (by have := h.hn; omega)).2 even_two
      · rw [he] at hmap ⊢
        convert hmap using 1
        rw [h.z_def]
        group
  have hUe : ∀ i : ℤ, IsConj (u * r ^ i * e) e ∨ IsConj (u * r ^ i * e) (h.z * e) := by
    intro i
    apply hQ
    rcases Int.even_or_odd (i - i₁) with hev | ⟨j, hj⟩
    · obtain ⟨k, hk⟩ := exists_eq_add_two_mul hev
      left
      rw [hk]
      exact ((h.isConj_ue i₁ k).symm.trans hi₁.symm)
    · right
      obtain ⟨f, hf⟩ := hε
      have hk : i = (a - i₁ + ε) + 2 * (j + i₁ - b - f) := by linarith
      rw [hk]
      exact (h.isConj_ue (a - i₁ + ε) (j + i₁ - b - f)).symm.trans hα₁.symm
  intro g hg
  set w := g⁻¹ * h.z * g with hwdef
  have hzw : IsConj h.z w := isConj_of_conj h.z g
  have hw2 : w ^ 2 = 1 := hsqc g h.z h.z_sq
  have hnot' : ∀ w', (IsConj w' e ∨ IsConj w' (h.z * e)) → IsConj h.z w' → False := by
    rintro w' (hw | hw) hzw'
    · exact hnot e (Or.inl rfl) (hzw'.trans hw)
    · exact hnot _ (Or.inr rfl) (hzw'.trans hw)
  rcases h.involution_cases hg hw2 with h1 | h1 | h1 | h1 | ⟨i, h1⟩ | ⟨i, h1⟩
  · exfalso
    apply h.z_ne_one
    calc h.z = g * w * g⁻¹ := by rw [hwdef]; group
      _ = 1 := by rw [h1]; group
  · exact h1
  · rw [h1] at hzw
    exact (hnot e (Or.inl rfl) hzw).elim
  · rw [h1] at hzw
    exact (hnot _ (Or.inr rfl) hzw).elim
  · rw [h1] at hzw
    exact (hnot' _ (hU i) hzw).elim
  · rw [h1] at hzw
    exact (hnot' _ (hUe i) hzw).elim

theorem commutator_eq_top_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) : commutator Y = ⊤ := by
  rcases (commutator_normal (⊤ : Subgroup Y) ⊤).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hmem : ⁅a, b⁆ ∈ commutator Y := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [_root_.commutator_def, h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · rw [_root_.commutator_def, h]

theorem false_of_dihedral_times_two {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) (P : Sylow 2 Y) {r u e : Y} {n : ℕ}
    (h : Data (P : Subgroup Y) r u e n) (α : Y ≃* Y) (hαr : α r = r⁻¹) {a : ℤ} (ha : Odd a)
    (hαu : α u = u * r ^ a) (hαe : α e = e ∨ α e = h.z * e) : False := by
  have hiso := isolated_of_dihedral_times_two (commutator_eq_top_of_simple hnonab) P h α hαr ha
    hαu hαe
  have hzP : h.z ∈ (P : Subgroup Y) := zpow_mem h.rT _
  have hzZ : (⟨h.z, hzP⟩ : (P : Subgroup Y)) ∈ center (P : Subgroup Y) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 h.central.1 g g.2)
  have hzo : orderOf (⟨h.z, hzP⟩ : (P : Subgroup Y)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime h.z_sq h.z_ne_one
  obtain ⟨g, hgP, hgz⟩ :=
    CFSG.RankTwoShapes.simple_central_sylow_involution_movement hnonab P _ hzZ hzo
  exact hgz (hiso g hgP)

end DihedralTimesTwo

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
