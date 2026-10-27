module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalCore

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_two_closure_dihedral {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab4 : (a * b) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) := by
  set r : X := a * b with hr
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbr : b = a * r := by
    rw [hr]
    calc b = (a * a) * b := by rw [ha, one_mul]
      _ = a * (a * b) := by group
  have hconj1 : a * r * a⁻¹ = r⁻¹ := by
    rw [hr, hainv]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, hainv]
  have hconj : ∀ j : ℤ, a * r ^ j * a⁻¹ = r ^ (-j) := by
    intro j
    rw [← conj_zpow, hconj1, inv_zpow']
  have hra : ∀ j : ℤ, r ^ j * a = a * r ^ (-j) := by
    intro j
    have h := hconj (-j)
    rw [neg_neg, hainv] at h
    calc r ^ j * a = (a * r ^ (-j) * a) * a := by rw [h]
      _ = a * r ^ (-j) * (a * a) := by group
      _ = a * r ^ (-j) := by rw [ha, mul_one]
  have h1 : ∀ i j : ℤ, r ^ i * (a * r ^ j) = a * r ^ (j - i) := by
    intro i j
    calc r ^ i * (a * r ^ j) = (r ^ i * a) * r ^ j := by group
      _ = (a * r ^ (-i)) * r ^ j := by rw [hra i]
      _ = a * (r ^ (-i) * r ^ j) := by group
      _ = a * r ^ (j - i) := by rw [← zpow_add, neg_add_eq_sub]
  have h2 : ∀ i j : ℤ, (a * r ^ i) * (a * r ^ j) = r ^ (j - i) := by
    intro i j
    calc (a * r ^ i) * (a * r ^ j) = a * (r ^ i * a) * r ^ j := by group
      _ = a * (a * r ^ (-i)) * r ^ j := by rw [hra i]
      _ = (a * a) * (r ^ (-i) * r ^ j) := by group
      _ = r ^ (j - i) := by rw [ha, one_mul, ← zpow_add, neg_add_eq_sub]
  let S₈ : Subgroup X :=
    { carrier := {x | ∃ i : ℤ, x = r ^ i ∨ x = a * r ^ i}
      mul_mem' := by
        rintro x y ⟨i, hi | hi⟩ ⟨j, hj | hj⟩
        · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
        · exact ⟨j - i, Or.inr (by rw [hi, hj, h1])⟩
        · exact ⟨i + j, Or.inr (by rw [hi, hj, mul_assoc, ← zpow_add])⟩
        · exact ⟨j - i, Or.inl (by rw [hi, hj, h2])⟩
      one_mem' := ⟨0, Or.inl (by simp)⟩
      inv_mem' := by
        rintro x ⟨i, hi | hi⟩
        · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [hi]
          exact inv_eq_of_mul_eq_one_right (by rw [h2, sub_self, zpow_zero]) }
  have hr4 : r ^ (4 : ℤ) = 1 := by simpa using hab4
  have hS₈ : IsPGroup 2 S₈ := by
    intro x
    obtain ⟨i, hi | hi⟩ := x.2
    · refine ⟨2, Subtype.ext ?_⟩
      show (x : X) ^ (2 ^ 2) = 1
      have : (x : X) ^ (2 ^ 2) = (r ^ (4 : ℤ)) ^ i := by
        rw [hi, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
        congr 1
        omega
      rw [this, hr4, one_zpow]
    · refine ⟨1, Subtype.ext ?_⟩
      show (x : X) ^ (2 ^ 1) = 1
      rw [hi, pow_one, pow_two, h2, sub_self, zpow_zero]
  have hle : Subgroup.closure ({a, b} : Set X) ≤ S₈ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · exact ⟨1, Or.inr (by rw [hbr]; simp)⟩
  exact hS₈.to_le hle

omit [Finite X] in
theorem exists_involution_of_isPGroup' {B : Subgroup X} (hB2 : IsPGroup 2 B) (hB : B ≠ ⊥)
    [Finite B] : ∃ y ∈ B, y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hB (Subgroup.card_eq_one.mp (by simpa using hn))
  have h2 : 2 ∣ Nat.card B := by
    rw [hn]; exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy' : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨y, y.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one (y : X)
    rwa [hy', sq] at this
  · intro h
    rw [h, orderOf_one] at hy'
    omega

theorem nasc_of_single_class {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab4 : (a * b) ^ 4 = 1) (hnc : a * b ≠ b * a)
    (hconj : ∀ y : X, y * y = 1 → y ≠ 1 → IsConj y a) :
    NoStrongAb (⊤ : Subgroup X) := by
  intro Q B hQ hBQ hBcomm hcl
  by_contra hB
  have hD := isPGroup_two_closure_dihedral ha hb hab4
  obtain ⟨m, -, hm⟩ := EscapingLocal.exists_conj_mem_of_isPGroup hQ.1 hQ.2.1 hQ.2.2
    (le_top : Subgroup.closure ({a, b} : Set X) ≤ ⊤) hD
  have haD : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have ha1 : m * a * m⁻¹ ∈ Q := hm a haD
  have hb1 : m * b * m⁻¹ ∈ Q := hm b hbD
  obtain ⟨y, hyB, hy2, hy1⟩ := exists_involution_of_isPGroup' (hQ.2.1.to_le hBQ) hB
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj y hy2 hy1)
  have hb1' : b ≠ 1 := fun h => hnc (by rw [h]; simp)
  obtain ⟨c', hc'⟩ := isConj_iff.mp (hconj b hb hb1')
  have hmem_a : m * a * m⁻¹ ∈ B := by
    have e : ((m * c)⁻¹)⁻¹ * y * (m * c)⁻¹ = m * a * m⁻¹ := by rw [← hc]; group
    have := hcl y hyB (m * c)⁻¹ (Subgroup.mem_top _) (by rw [e]; exact ha1)
    rwa [e] at this
  have hmem_b : m * b * m⁻¹ ∈ B := by
    have hbe : b = c'⁻¹ * a * c' := by rw [← hc']; group
    have e : ((m * c'⁻¹ * c)⁻¹)⁻¹ * y * (m * c'⁻¹ * c)⁻¹ = m * b * m⁻¹ := by
      rw [hbe, ← hc]; group
    have := hcl y hyB (m * c'⁻¹ * c)⁻¹ (Subgroup.mem_top _) (by rw [e]; exact hb1)
    rwa [e] at this
  have hcomm := hBcomm.is_comm.comm ⟨_, hmem_a⟩ ⟨_, hmem_b⟩
  have hcomm' : (m * a * m⁻¹) * (m * b * m⁻¹) = (m * b * m⁻¹) * (m * a * m⁻¹) :=
    congrArg Subtype.val hcomm
  apply hnc
  have : m * (a * b) * m⁻¹ = m * (b * a) * m⁻¹ := by
    calc m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      _ = (m * b * m⁻¹) * (m * a * m⁻¹) := hcomm'
      _ = m * (b * a) * m⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel this)

theorem eq_of_sq_eq_one_of_isCyclic {T : Subgroup X} (hT : IsCyclic T) {x y : X} (hx : x ∈ T)
    (hy : y ∈ T) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have : Fintype T := Fintype.ofFinite T
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) (by norm_num)
  have h1x : (⟨x, hx⟩ : T) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have h1y : (⟨y, hy⟩ : T) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hxy : (⟨x, hx⟩ : T) ≠ ⟨y, hy⟩ := fun h => hne (congrArg Subtype.val h)
  have hsub : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset T) ⊆
      Finset.univ.filter (fun a : T => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · apply Subtype.ext; simpa [sq] using hx2
    · apply Subtype.ext; simpa [sq] using hy2
  have h3 : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset T).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, ⟨x, hx⟩, ⟨y, hy⟩, h1x.symm, h1y.symm, hxy, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem nasc_of_torus {T₀ : Subgroup X} (hT : IsCyclic T₀) {w : X} (hw2 : w * w = 1)
    (hw : w ∉ T₀) (hinv : ∀ x ∈ T₀, w * x * w⁻¹ = x⁻¹)
    (hconj : ∀ y : X, y * y = 1 → y ≠ 1 → ∃ x ∈ T₀, IsConj y x)
    (h4 : 4 ∣ Nat.card T₀) : NoStrongAb (⊤ : Subgroup X) := by
  obtain ⟨g, hg⟩ := hT.exists_generator
  have hord : orderOf g = Nat.card T₀ := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := h4
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card T₀ := Nat.card_pos
    omega
  have hrord : orderOf ((g : X) ^ k) = 4 := by
    rw [← Subgroup.orderOf_coe g] at hord
    rw [orderOf_pow_of_dvd hk0 (by rw [hord, hk]; exact Dvd.intro_left 4 rfl), hord, hk]
    exact Nat.mul_div_cancel 4 (Nat.pos_of_ne_zero hk0)
  set r : X := (g : X) ^ k with hr
  have hrT : r ∈ T₀ := T₀.pow_mem g.2 k
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwr : w * r * w = r⁻¹ := by
    have := hinv r hrT
    rwa [hwinv] at this
  have hr4 : r ^ 4 = 1 := by rw [← hrord]; exact pow_orderOf_eq_one r
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hrord] at this
    omega
  have hb : (w * r) * (w * r) = 1 := by
    calc (w * r) * (w * r) = (w * r * w) * r := by group
      _ = r⁻¹ * r := by rw [hwr]
      _ = 1 := by group
  have hab : w * (w * r) = r := by rw [← mul_assoc, hw2, one_mul]
  have hab4 : (w * (w * r)) ^ 4 = 1 := by rw [hab]; exact hr4
  have hnc : w * (w * r) ≠ (w * r) * w := by
    rw [hab]
    intro h
    have h' : (w * r) * w = r⁻¹ := hwr
    rw [h'] at h
    apply hr2
    calc r ^ 2 = r * r := sq r
      _ = r * r⁻¹⁻¹ := by rw [inv_inv]
      _ = r * (r⁻¹)⁻¹ := rfl
      _ = 1 := by rw [← h]; group
  have hinvolx : ∀ y x : X, y * y = 1 → y ≠ 1 → IsConj y x → x * x = 1 ∧ x ≠ 1 := by
    intro y x hy hy1 hyx
    obtain ⟨c, hc⟩ := isConj_iff.mp hyx
    refine ⟨?_, ?_⟩
    · rw [← hc]
      calc c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
        _ = 1 := by rw [hy]; group
    · rintro rfl
      apply hy1
      calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [hc]
        _ = 1 := by group
  have hw1 : w ≠ 1 := fun h => hw (h ▸ T₀.one_mem)
  obtain ⟨xw, hxwT, hxw⟩ := hconj w hw2 hw1
  obtain ⟨hxw2, hxw1⟩ := hinvolx w xw hw2 hw1 hxw
  refine nasc_of_single_class hw2 hb hab4 hnc (fun y hy hy1 => ?_)
  obtain ⟨x, hxT, hx⟩ := hconj y hy hy1
  obtain ⟨hx2, hx1⟩ := hinvolx y x hy hy1 hx
  have := eq_of_sq_eq_one_of_isCyclic hT hxT hxwT hx2 hxw2 hx1 hxw1
  subst this
  exact hx.trans hxw.symm

theorem odd_torus_data {T₀ : Subgroup X} (hT : IsCyclic T₀)
    (hconj : ∀ y : X, y * y = 1 → y ≠ 1 → ∃ x ∈ T₀, IsConj y x)
    (hcent : ∀ x ∈ T₀, x ≠ 1 → x * x = 1 →
      Nat.card (Subgroup.centralizer ({x} : Set X)) = 2 * Nat.card T₀)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hcard : Nat.card T₀ = 2 * m) :
    ∀ t : X, t * t = 1 → t ≠ 1 → ∃ T : Subgroup X, (∀ y ∈ T, y * t = t * y) ∧
      (∀ c : X, c * t = t * c → ∀ y ∈ T, c * y * c⁻¹ ∈ T) ∧ IsCyclic T ∧
      ¬ 2 ∣ Nat.card T ∧ T ≠ ⊥ := by
  intro t ht2 ht1
  have hcomm : IsMulCommutative T₀ := by
    have := hT
    infer_instance
  have hT₀comm : ∀ y ∈ T₀, ∀ z ∈ T₀, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨x, hxT, hx⟩ := hconj t ht2 ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  have hx2 : x * x = 1 := by
    rw [← hc]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply ht1
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = c⁻¹ * 1 * c := by rw [hc]
      _ = 1 := by group
  set C : Subgroup X := Subgroup.centralizer ({x} : Set X) with hC
  have hT₀C : T₀ ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hT₀comm y hy x hxT)
  have hC2 : Nat.card C = 2 * Nat.card T₀ := hcent x hxT hx1 hx2
  have hindex : (T₀.subgroupOf C).index = 2 := by
    have h1 := Subgroup.card_mul_index (T₀.subgroupOf C)
    have h2 : Nat.card (T₀.subgroupOf C) = Nat.card T₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀C).toEquiv
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    rw [h2, hC2] at h1
    have : Nat.card T₀ * (T₀.subgroupOf C).index = Nat.card T₀ * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hnorm : (T₀.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hindex
  have hCconj : ∀ k ∈ C, ∀ y ∈ T₀, k * y * k⁻¹ ∈ T₀ := by
    intro k hk y hy
    have := hnorm.conj_mem ⟨y, hT₀C hy⟩ hy ⟨k, hk⟩
    exact this
  let T₁ : Subgroup X :=
    { carrier := {z | z ∈ T₀ ∧ z ^ m = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨T₀.mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hT₀comm a ha b hb).mul_pow, ha', hb', one_mul]
      one_mem' := ⟨T₀.one_mem, one_pow m⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨T₀.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hT₁le : T₁ ≤ T₀ := fun z hz => hz.1
  have hT₁C : ∀ k ∈ C, ∀ y ∈ T₁, k * y * k⁻¹ ∈ T₁ := by
    intro k hk y hy
    refine ⟨hCconj k hk y hy.1, ?_⟩
    rw [conj_pow, hy.2]
    group
  have hT₁cyc : IsCyclic T₁ := by
    have : IsCyclic (T₁.subgroupOf T₀) := by
      have := hT
      infer_instance
    exact (Subgroup.subgroupOfEquivOfLe hT₁le).isCyclic.mp this
  have hT₁odd : ¬ 2 ∣ Nat.card T₁ := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg2 : orderOf (g : X) = 2 := by rw [Subgroup.orderOf_coe, hg]
    have : orderOf (g : X) ∣ m := orderOf_dvd_of_pow_eq_one g.2.2
    rw [hg2] at this
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  have hT₁ne : T₁ ≠ ⊥ := by
    obtain ⟨g, hg⟩ := hT.exists_generator
    have hord : orderOf g = Nat.card T₀ := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgm : ((g : X) ^ 2) ^ m = 1 := by
      rw [← pow_mul, ← hcard]
      have := pow_card_eq_one' (G := T₀) (x := g)
      exact congrArg Subtype.val this
    intro hbot
    have hmem : (g : X) ^ 2 ∈ T₁ := ⟨T₀.pow_mem g.2 2, hgm⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : orderOf (g : X) ∣ 2 := orderOf_dvd_of_pow_eq_one hmem
    rw [Subgroup.orderOf_coe, hord, hcard] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  let T : Subgroup X := T₁.map (MulAut.conj c⁻¹).toMonoidHom
  have hmemT : ∀ y : X, y ∈ T ↔ c * y * c⁻¹ ∈ T₁ := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
    · intro h
      exact ⟨c * y * c⁻¹, h, by simp [mul_assoc]⟩
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have h1 := (hmemT y).mp hy
    have h2 : (c * y * c⁻¹) * x = x * (c * y * c⁻¹) := hT₀comm _ (hT₁le h1) x hxT
    rw [← hc] at h2
    have h3 : c * (y * t) * c⁻¹ = c * (t * y) * c⁻¹ := by
      calc c * (y * t) * c⁻¹ = (c * y * c⁻¹) * (c * t * c⁻¹) := by group
        _ = (c * t * c⁻¹) * (c * y * c⁻¹) := h2
        _ = c * (t * y) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  · intro c' hc' y hy
    rw [hmemT] at hy ⊢
    have hk : c * c' * c⁻¹ ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      rw [← hc]
      calc c * c' * c⁻¹ * (c * t * c⁻¹) = c * (c' * t) * c⁻¹ := by group
        _ = c * (t * c') * c⁻¹ := by rw [hc']
        _ = (c * t * c⁻¹) * (c * c' * c⁻¹) := by group
    have := hT₁C _ hk _ hy
    have e : c * (c' * y * c'⁻¹) * c⁻¹ =
        (c * c' * c⁻¹) * (c * y * c⁻¹) * (c * c' * c⁻¹)⁻¹ := by
      group
    rw [e]
    exact this
  · exact ((Subgroup.equivMapOfInjective T₁ (MulAut.conj c⁻¹).toMonoidHom
      (MulAut.conj c⁻¹).injective).isCyclic.mp hT₁cyc)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hT₁odd
  · intro hbot
    exact hT₁ne ((Subgroup.map_eq_bot_iff_of_injective T₁ (MulAut.conj c⁻¹).injective).mp hbot)

theorem two_dvd_card_of_isPGroup {B : Subgroup X} (hB2 : IsPGroup 2 B) (hB : B ≠ ⊥) :
    2 ∣ Nat.card B := by
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hB (Subgroup.card_eq_one.mp (by simpa using hn))
  rw [hn]; exact dvd_pow_self 2 hn0

theorem exists_ne_one_commuting {P B : Subgroup X} (hP : IsPGroup 2 P)
    (hBn : ∀ q ∈ P, ∀ b ∈ B, q * b * q⁻¹ ∈ B) (hB2 : 2 ∣ Nat.card B) :
    ∃ z ∈ B, z ≠ 1 ∧ ∀ q ∈ P, q * z = z * q := by
  classical
  let _ : MulAction P B :=
    { smul := fun q b => ⟨(q : X) * b * (q : X)⁻¹, hBn q q.2 b b.2⟩
      one_smul := fun b => Subtype.ext (by show (1 : X) * b * (1 : X)⁻¹ = b; simp)
      mul_smul := fun q r b => Subtype.ext (by
        show ((q * r : P) : X) * b * ((q * r : P) : X)⁻¹ =
          (q : X) * ((r : X) * b * (r : X)⁻¹) * (q : X)⁻¹
        simp [mul_assoc]) }
  have hsmul : ∀ (q : P) (b : B), ((q • b : B) : X) = (q : X) * b * (q : X)⁻¹ := fun q b => rfl
  have hmod := hP.card_modEq_card_fixedPoints B
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints P B) := by
    have h1 : Nat.card B ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr hB2
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h1)
  have hone : (1 : B) ∈ MulAction.fixedPoints P B := fun q => Subtype.ext (by
    rw [hsmul]; simp)
  have : Nonempty (MulAction.fixedPoints P B) := ⟨⟨1, hone⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints P B) := Nat.card_pos
  have hgt : 1 < Nat.card (MulAction.fixedPoints P B) := by
    have := Nat.le_of_dvd hpos hfix2
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ : ∃ z : MulAction.fixedPoints P B, z ≠ ⟨1, hone⟩ := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (MulAction.fixedPoints P B) :=
      ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  refine ⟨z, z.2, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun q hq => ?_⟩
  have := congrArg Subtype.val (hz ⟨q, hq⟩)
  rw [hsmul] at this
  simp only at this
  calc (q : X) * z = (q * z * q⁻¹) * q := by group
    _ = z * q := by rw [this]

theorem nasc_of_centralizer {a b c : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab4 : (a * b) ^ 4 = 1) (hnc : a * b ≠ b * a) (hac : IsConj a c) (hbc : IsConj b c)
    (hz : ∀ z : X, z * z = 1 → z ≠ 1 → z * a = a * z → z * b = b * z → z = c) :
    NoStrongAb (⊤ : Subgroup X) := by
  intro Q B hQ hBQ hBcomm hcl
  by_contra hB
  have hD := isPGroup_two_closure_dihedral ha hb hab4
  obtain ⟨m, -, hm⟩ := EscapingLocal.exists_conj_mem_of_isPGroup hQ.1 hQ.2.1 hQ.2.2
    (le_top : Subgroup.closure ({a, b} : Set X) ≤ ⊤) hD
  have haD : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have ha1 : m * a * m⁻¹ ∈ Q := hm a haD
  have hb1 : m * b * m⁻¹ ∈ Q := hm b hbD
  have hBn : ∀ q ∈ Q, ∀ x ∈ B, q * x * q⁻¹ ∈ B := by
    intro q hq x hx
    have h := hcl x hx q⁻¹ (Subgroup.mem_top _)
      (by simpa using Q.mul_mem (Q.mul_mem hq (hBQ hx)) (Q.inv_mem hq))
    simpa using h
  obtain ⟨z, hzB, hz1, hzc⟩ := exists_ne_one_commuting hQ.2.1 hBn
    (two_dvd_card_of_isPGroup (hQ.2.1.to_le hBQ) hB)
  let Z : Subgroup X := B ⊓ Subgroup.centralizer (Q : Set X)
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hzZ : z ∈ Z := ⟨hzB, Subgroup.mem_centralizer_iff.mpr (fun q hq => hzc q hq)⟩
    rw [hbot, Subgroup.mem_bot] at hzZ
    exact hz1 hzZ
  have hZ2 : IsPGroup 2 Z := (hQ.2.1.to_le hBQ).to_le inf_le_left
  obtain ⟨y, hyZ, hy2, hy1⟩ := exists_involution_of_isPGroup' hZ2 hZne
  have hyB : y ∈ B := hyZ.1
  have hyc : ∀ q ∈ Q, q * y = y * q := fun q hq =>
    Subgroup.mem_centralizer_iff.mp hyZ.2 q hq
  have hyc' : m⁻¹ * y * m = c := by
    refine hz _ ?_ ?_ ?_ ?_
    · calc m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m := by group
        _ = 1 := by rw [hy2]; group
    · intro h
      apply hy1
      calc y = m * (m⁻¹ * y * m) * m⁻¹ := by group
        _ = 1 := by rw [h]; group
    · have := hyc _ ha1
      calc m⁻¹ * y * m * a = m⁻¹ * (y * (m * a * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * a * m⁻¹) * y) * m := by rw [← this]
        _ = a * (m⁻¹ * y * m) := by group
    · have := hyc _ hb1
      calc m⁻¹ * y * m * b = m⁻¹ * (y * (m * b * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * b * m⁻¹) * y) * m := by rw [← this]
        _ = b * (m⁻¹ * y * m) := by group
  have hyeq : y = m * c * m⁻¹ := by rw [← hyc']; group
  obtain ⟨k, hk⟩ := isConj_iff.mp hac
  obtain ⟨k', hk'⟩ := isConj_iff.mp hbc
  have hmem_a : m * a * m⁻¹ ∈ B := by
    have e : (m * k * m⁻¹)⁻¹ * y * (m * k * m⁻¹) = m * a * m⁻¹ := by
      have hae : a = k⁻¹ * c * k := by rw [← hk]; group
      rw [hyeq, hae]; group
    have := hcl y hyB (m * k * m⁻¹) (Subgroup.mem_top _) (by rw [e]; exact ha1)
    rwa [e] at this
  have hmem_b : m * b * m⁻¹ ∈ B := by
    have e : (m * k' * m⁻¹)⁻¹ * y * (m * k' * m⁻¹) = m * b * m⁻¹ := by
      have hbe : b = k'⁻¹ * c * k' := by rw [← hk']; group
      rw [hyeq, hbe]; group
    have := hcl y hyB (m * k' * m⁻¹) (Subgroup.mem_top _) (by rw [e]; exact hb1)
    rwa [e] at this
  have hcomm := hBcomm.is_comm.comm ⟨_, hmem_a⟩ ⟨_, hmem_b⟩
  have hcomm' : (m * a * m⁻¹) * (m * b * m⁻¹) = (m * b * m⁻¹) * (m * a * m⁻¹) :=
    congrArg Subtype.val hcomm
  apply hnc
  have : m * (a * b) * m⁻¹ = m * (b * a) * m⁻¹ := by
    calc m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      _ = (m * b * m⁻¹) * (m * a * m⁻¹) := hcomm'
      _ = m * (b * a) * m⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel this)

theorem card_sylow_eq {Q : Subgroup X} (hQ : IsSylowTwoOf Q ⊤) {e k : ℕ} (hk : Odd k)
    (hX : Nat.card X = 2 ^ e * k) : Nat.card Q = 2 ^ e := by
  obtain ⟨n, hn⟩ := hQ.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ Q.index := by
    have h : (Q.subgroupOf ⊤).index = Q.index := Subgroup.relIndex_top_right _
    rw [← h]; exact hQ.2.2
  have hmul := Subgroup.card_mul_index Q
  rw [hn, hX] at hmul
  have hidx_odd : Nat.Coprime 2 Q.index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx
  have hk' : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hk
  have h1 : 2 ^ n ∣ 2 ^ e := by
    have : 2 ^ n ∣ 2 ^ e * k := ⟨Q.index, hmul.symm⟩
    exact (Nat.Coprime.pow_left n hk').dvd_of_dvd_mul_right this
  have h2 : 2 ^ e ∣ 2 ^ n := by
    have : 2 ^ e ∣ 2 ^ n * Q.index := ⟨k, hmul⟩
    exact (Nat.Coprime.pow_left e hidx_odd).dvd_of_dvd_mul_right this
  rw [hn]
  exact congrArg (2 ^ ·) (le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2))

@[expose] def OddTorusData (Ω : Type) [Group Ω] : Prop :=
  ∀ t : Ω, t * t = 1 → t ≠ 1 → ∃ T : Subgroup Ω, (∀ y ∈ T, y * t = t * y) ∧
    (∀ c : Ω, c * t = t * c → ∀ y ∈ T, c * y * c⁻¹ ∈ T) ∧ IsCyclic T ∧
    ¬ 2 ∣ Nat.card T ∧ T ≠ ⊥

omit [Finite X] in
theorem oddTorusData_of_mulEquiv {Y : Type} [Group Y] (e : Y ≃* X) (h : OddTorusData X) :
    OddTorusData Y := by
  intro t ht2 ht1
  have het2 : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have het1 : e t ≠ 1 := fun h' => ht1 (e.injective (by rw [h', map_one]))
  obtain ⟨T, hT1, hT2, hTc, hTo, hTne⟩ := h (e t) het2 het1
  refine ⟨T.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hT1 z hz
  · rintro c hc _ ⟨z, hz, rfl⟩
    refine ⟨e c * z * (e c)⁻¹, hT2 (e c) (by rw [← map_mul, ← map_mul, hc]) z hz, ?_⟩
    simp
  · exact (Subgroup.equivMapOfInjective T e.symm.toMonoidHom e.symm.injective).isCyclic.mp hTc
  · rw [Subgroup.card_map_of_injective e.symm.injective]; exact hTo
  · intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective T e.symm.injective).mp hbot)

end CFSG.QuasithinUnique.K1
