module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Dih

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.IVK

namespace CtW

theorem isDihedralOrder_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {m : ℕ}
    (h : IsDihedralOrder Y m) : IsDihedralOrder Y' m := by
  obtain ⟨k, hk, h2, ⟨e'⟩⟩ := h
  exact ⟨k, hk, h2, ⟨e.symm.trans e'⟩⟩

structure Cfg (G : Type) [Group G] (m : ℕ) (T₁ : Subgroup G) (z t : G) : Prop where
  normal : T₁.Normal
  dih : IsDihedralOrder ↥T₁ m
  hz : orderOf z = 2
  ht : orderOf t = 2
  htc : t ∈ center G
  hzt : z ≠ t
  hzT₁ : ∀ a ∈ T₁, z * a = a * z
  hinfU : (zpowers z ⊔ zpowers t) ⊓ T₁ = ⊥
  hC : centralizer ({z} : Set G) = (zpowers z ⊔ zpowers t) ⊔ T₁

@[expose] def Concl (G : Type) [Group G] (m : ℕ) (T₁ : Subgroup G) (z : G) : Prop :=
  ∃ (X : Subgroup G) (y₀ : G), X.Normal ∧ z ∈ X ∧
      (∀ N : Subgroup G, N.Normal → z ∈ N → X ≤ N) ∧
      IsDihedralOrder ↥X m ∧
      (∀ a ∈ X, ∀ b ∈ T₁, a * b = b * a) ∧ X ⊓ T₁ = ⊥ ∧
      (∀ c : G, (∀ a ∈ T₁, c * a = a * c) →
        ∃ x ∈ X, ∃ ζ ∈ T₁, (∀ a ∈ T₁, ζ * a = a * ζ) ∧ c = x * ζ) ∧
      y₀ * y₀ = 1 ∧ X ⊔ T₁ ⊔ zpowers y₀ = ⊤ ∧
      IsDihedralOrder ↥(X ⊔ zpowers y₀) (2 * m) ∧ IsDihedralOrder ↥(T₁ ⊔ zpowers y₀) (2 * m)

variable {G G' : Type} [Group G] [Group G']

theorem map_zpowers_equiv (e : G ≃* G') (z : G) :
    zpowers (e z) = (zpowers z).map e.toMonoidHom :=
  (MonoidHom.map_zpowers e.toMonoidHom z).symm

theorem map_centralizer_singleton (e : G ≃* G') (z : G) :
    centralizer ({e z} : Set G') = (centralizer ({z} : Set G)).map e.toMonoidHom := by
  ext g'
  constructor
  · intro h
    refine ⟨e.symm g', ?_, by simp⟩
    have h' : g' * e z = e z * g' := mem_centralizer_singleton_iff.mp h
    have := congrArg e.symm h'
    show e.symm g' ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    simpa using this
  · rintro ⟨g, hg, rfl⟩
    have hg' : g * z = z * g := mem_centralizer_singleton_iff.mp hg
    rw [mem_centralizer_singleton_iff]
    show e g * e z = e z * e g
    rw [← map_mul, ← map_mul, hg']

theorem Cfg.map {m : ℕ} {T₁ : Subgroup G} {z t : G} (e : G ≃* G') (h : Cfg G m T₁ z t) :
    Cfg G' m (T₁.map e.toMonoidHom) (e z) (e t) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.normal.map e.toMonoidHom e.surjective
  · exact isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective T₁ e.toMonoidHom hinj) h.dih
  · rw [MulEquiv.orderOf_eq]; exact h.hz
  · rw [MulEquiv.orderOf_eq]; exact h.ht
  · rw [Subgroup.mem_center_iff]
    intro g'
    have := Subgroup.mem_center_iff.mp h.htc (e.symm g')
    have h2 := congrArg e this
    simpa using h2
  · exact fun hh => h.hzt (e.injective hh)
  · rintro _ ⟨a, ha, rfl⟩
    show e z * e a = e a * e z
    rw [← map_mul, ← map_mul, h.hzT₁ a ha]
  · rw [map_zpowers_equiv, map_zpowers_equiv, ← Subgroup.map_sup,
      ← Subgroup.map_inf _ _ _ hinj, h.hinfU, Subgroup.map_bot]
  · rw [map_centralizer_singleton, h.hC, Subgroup.map_sup, Subgroup.map_sup,
      map_zpowers_equiv, map_zpowers_equiv]

theorem Concl.map {m : ℕ} {T₁ : Subgroup G} {z : G} (e : G ≃* G') (h : Concl G m T₁ z) :
    Concl G' m (T₁.map e.toMonoidHom) (e z) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  obtain ⟨X, y₀, hXn, hzX, hmin, hdih, hcomm, hinf, hcen, hy₀, hgen, hd1, hd2⟩ := h
  have hzy : zpowers (e y₀) = (zpowers y₀).map e.toMonoidHom := map_zpowers_equiv e y₀
  refine ⟨X.map e.toMonoidHom, e y₀, hXn.map e.toMonoidHom e.surjective, ⟨z, hzX, rfl⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro N' hN' hzN'
    have hN : (N'.comap e.toMonoidHom).Normal := hN'.comap _
    have := hmin (N'.comap e.toMonoidHom) hN (by simpa using hzN')
    exact Subgroup.map_le_iff_le_comap.mpr this
  · exact isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective X e.toMonoidHom hinj) hdih
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_inf _ _ _ hinj, hinf, Subgroup.map_bot]
  · intro c' hc'
    have hc : ∀ a ∈ T₁, e.symm c' * a = a * e.symm c' := by
      intro a ha
      have := hc' (e a) ⟨a, ha, rfl⟩
      have h2 := congrArg e.symm this
      simpa using h2
    obtain ⟨x, hx, ζ, hζ, hζc, hxζ⟩ := hcen (e.symm c') hc
    refine ⟨e x, ⟨x, hx, rfl⟩, e ζ, ⟨ζ, hζ, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      show e ζ * e a = e a * e ζ
      rw [← map_mul, ← map_mul, hζc a ha]
    · rw [← map_mul, ← hxζ]
      simp
  · rw [← map_mul, hy₀, map_one]
  · rw [hzy, ← Subgroup.map_sup, ← Subgroup.map_sup, hgen]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · have : X.map e.toMonoidHom ⊔ zpowers (e y₀) = (X ⊔ zpowers y₀).map e.toMonoidHom := by
      rw [hzy, Subgroup.map_sup]
    rw [this]
    exact isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective _ e.toMonoidHom hinj) hd1
  · have : T₁.map e.toMonoidHom ⊔ zpowers (e y₀) = (T₁ ⊔ zpowers y₀).map e.toMonoidHom := by
      rw [hzy, Subgroup.map_sup]
    rw [this]
    exact isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective _ e.toMonoidHom hinj) hd2

theorem Concl.of_map {m : ℕ} {T₁ : Subgroup G} {z : G} (e : G ≃* G')
    (h : Concl G' m (T₁.map e.toMonoidHom) (e z)) : Concl G m T₁ z := by
  have h2 := Concl.map e.symm h
  have e1 : (T₁.map e.toMonoidHom).map e.symm.toMonoidHom = T₁ := by
    rw [Subgroup.map_map]
    ext x
    simp
  have e2 : e.symm (e z) = z := by simp
  rw [e1, e2] at h2
  exact h2

theorem card_of_isDihedralOrder {Y : Type} [Group Y] {m : ℕ} (h : IsDihedralOrder Y m) :
    Nat.card Y = m := by
  obtain ⟨k, hk, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk]

section Model

open DihedralGroup

@[expose] def pz (k : ℕ) : ZMod (2 * k) →+* ZMod 2 := ZMod.castHom (dvd_mul_right 2 k) (ZMod 2)

@[expose] def par (k : ℕ) : DihedralGroup (2 * k) → ZMod 2
  | r a => pz k a
  | sr a => pz k a

theorem z2_aux (u v : ZMod 2) : u - v = v + u := by
  revert u v; decide

theorem z2_neg (x : ZMod 2) : -x = x := by
  revert x; decide

variable {k : ℕ}

theorem par_mul (x y : DihedralGroup (2 * k)) : par k (x * y) = par k x + par k y := by
  rcases x with a | a <;> rcases y with b | b
  · simp only [par, r_mul_r, map_add]
  · simp only [par, r_mul_sr]; rw [map_sub]; exact z2_aux _ _
  · simp only [par, sr_mul_r, map_add]
  · simp only [par, sr_mul_sr]; rw [map_sub]; exact z2_aux _ _

theorem par_one : par k (1 : DihedralGroup (2 * k)) = 0 := by
  rw [one_def]; simp [par]

theorem par_inv (x : DihedralGroup (2 * k)) : par k x⁻¹ = par k x := by
  rcases x with a | a
  · simp only [par, inv_r]; rw [map_neg]; exact z2_neg _
  · simp only [par, inv_sr]

@[expose] def Bsub (k : ℕ) : Subgroup (DihedralGroup (2 * k)) where
  carrier := {x | par k x = 0}
  mul_mem' := by
    intro x y hx hy
    change par k (x * y) = 0
    change par k x = 0 at hx
    change par k y = 0 at hy
    rw [par_mul, hx, hy]; rfl
  one_mem' := par_one
  inv_mem' := by
    intro x hx
    change par k x⁻¹ = 0
    change par k x = 0 at hx
    rw [par_inv, hx]

@[expose] def Wsub (k : ℕ) : Subgroup (DihedralGroup (2 * k) × DihedralGroup (2 * k)) where
  carrier := {p | par k p.1 = par k p.2}
  mul_mem' := by
    intro x y hx hy
    change par k (x * y).1 = par k (x * y).2
    change par k x.1 = par k x.2 at hx
    change par k y.1 = par k y.2 at hy
    rw [Prod.fst_mul, Prod.snd_mul, par_mul, par_mul, hx, hy]
  one_mem' := by
    change par k (1 : DihedralGroup (2 * k) × DihedralGroup (2 * k)).1 =
      par k (1 : DihedralGroup (2 * k) × DihedralGroup (2 * k)).2
    rfl
  inv_mem' := by
    intro x hx
    change par k (x⁻¹).1 = par k (x⁻¹).2
    change par k x.1 = par k x.2 at hx
    rw [Prod.fst_inv, Prod.snd_inv, par_inv, par_inv, hx]

theorem mem_Wsub {p : DihedralGroup (2 * k) × DihedralGroup (2 * k)} :
    p ∈ Wsub k ↔ par k p.1 = par k p.2 := Iff.rfl

section Arith

variable [NeZero k]

theorem zm_two_mul_eq_zero_iff (a : ZMod (2 * k)) :
    2 * a = 0 ↔ a = 0 ∨ a = (k : ZMod (2 * k)) := by
  constructor
  · intro h
    have hv : ((2 * a.val : ℕ) : ZMod (2 * k)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h
    rw [ZMod.natCast_eq_zero_iff] at hv
    obtain ⟨j, hj⟩ := hv
    have hlt : a.val < 2 * k := ZMod.val_lt a
    have h1 : a.val = k * j := by
      have : 2 * a.val = 2 * (k * j) := by rw [hj]; ring
      omega
    have hj2 : j < 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 * k ≤ k * j := by nlinarith [Nat.pos_of_ne_zero (NeZero.ne k)]
      omega
    interval_cases j
    · left
      have : a.val = 0 := by simpa using h1
      exact (ZMod.val_eq_zero a).mp this
    · right
      have h3 : a.val = k := by simpa using h1
      calc a = ((a.val : ℕ) : ZMod (2 * k)) := (ZMod.natCast_zmod_val a).symm
        _ = (k : ZMod (2 * k)) := by rw [h3]
  · rintro (h | h)
    · rw [h]; simp
    · rw [h]
      have : (2 : ZMod (2 * k)) * (k : ZMod (2 * k)) = ((2 * k : ℕ) : ZMod (2 * k)) := by
        push_cast; rfl
      rw [this]
      exact ZMod.natCast_self (2 * k)

omit [NeZero k] in
theorem zm_nat_ne_zero {m : ℕ} (hm : 0 < m) (hmk : m < 2 * k) : ((m : ℕ) : ZMod (2 * k)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hm h) (by omega)

theorem zm_k_ne_zero : (k : ZMod (2 * k)) ≠ 0 :=
  zm_nat_ne_zero (Nat.pos_of_ne_zero (NeZero.ne k)) (by have := Nat.pos_of_ne_zero (NeZero.ne k); omega)

omit [NeZero k] in
theorem zm_k_add_k : (k : ZMod (2 * k)) + k = 0 := by
  have : (k : ZMod (2 * k)) + k = ((2 * k : ℕ) : ZMod (2 * k)) := by push_cast; ring
  rw [this]
  exact ZMod.natCast_self (2 * k)

omit [NeZero k] in
theorem zm_four_ne_zero (hk : 3 ≤ k) : (4 : ZMod (2 * k)) ≠ 0 := by
  have := zm_nat_ne_zero (k := k) (m := 4) (by norm_num) (by omega)
  exact_mod_cast this

omit [NeZero k] in
theorem pz_natCast (n : ℕ) : pz k (n : ZMod (2 * k)) = (n : ZMod 2) := map_natCast (pz k) n

omit [NeZero k] in
theorem pz_one : pz k 1 = 1 := map_one (pz k)

omit [NeZero k] in
theorem pz_k (hke : 2 ∣ k) : pz k (k : ZMod (2 * k)) = 0 := by
  rw [pz_natCast]
  obtain ⟨j, hj⟩ := hke
  rw [hj]
  push_cast
  have : (2 : ZMod 2) = 0 := by decide
  rw [this]; simp

theorem pz_eq_zero_iff (a : ZMod (2 * k)) : pz k a = 0 ↔ ∃ b : ZMod (2 * k), a = 2 * b := by
  constructor
  · intro h
    have h1 : pz k ((a.val : ℕ) : ZMod (2 * k)) = 0 := by rw [ZMod.natCast_zmod_val]; exact h
    rw [pz_natCast] at h1
    have h2 : 2 ∣ a.val := (ZMod.natCast_eq_zero_iff a.val 2).mp h1
    obtain ⟨j, hj⟩ := h2
    refine ⟨(j : ZMod (2 * k)), ?_⟩
    rw [← ZMod.natCast_zmod_val a, hj]
    push_cast; rfl
  · rintro ⟨b, rfl⟩
    rw [map_mul]
    have : pz k 2 = 0 := by
      have h2 : ((2 : ℕ) : ZMod (2 * k)) = 2 := by norm_num
      rw [← h2, pz_natCast]
      decide
    rw [this]; simp

end Arith

section DihFacts

variable [NeZero k]

@[expose] def cc (k : ℕ) : DihedralGroup (2 * k) := r (k : ZMod (2 * k))

omit [NeZero k] in
theorem cc_mul_cc : cc k * cc k = 1 := by
  simp only [cc, r_mul_r, one_def]
  rw [zm_k_add_k]

theorem cc_ne_one : cc k ≠ 1 := by
  intro h
  simp only [cc, one_def, r.injEq] at h
  exact zm_k_ne_zero h

omit [NeZero k] in
theorem cc_central (x : DihedralGroup (2 * k)) : x * cc k = cc k * x := by
  have hk2 : (k : ZMod (2 * k)) = -(k : ZMod (2 * k)) := eq_neg_of_add_eq_zero_left zm_k_add_k
  rcases x with a | a
  · simp only [cc, r_mul_r, add_comm]
  · simp only [cc, sr_mul_r, r_mul_sr]
    congr 1
    rw [sub_eq_add_neg, ← hk2]

omit [NeZero k] in
theorem par_cc (hke : 2 ∣ k) : par k (cc k) = 0 := pz_k hke

theorem mul_self_eq_one_iff (x : DihedralGroup (2 * k)) :
    x * x = 1 ↔ x = 1 ∨ x = cc k ∨ ∃ a, x = sr a := by
  rcases x with a | a
  · simp only [r_mul_r, one_def, r.injEq, cc, reduceCtorEq, exists_false, or_false]
    rw [← two_mul, zm_two_mul_eq_zero_iff]
  · simp only [sr_mul_sr, one_def, sub_self, cc, reduceCtorEq, false_or]
    simp

theorem par_eq_zero_of_comm (hke : 2 ∣ k) {x : DihedralGroup (2 * k)}
    (h : x * sr 0 = sr 0 * x) : par k x = 0 := by
  rcases x with a | a
  · rw [r_mul_sr, sr_mul_r] at h
    have h1 : (0 : ZMod (2 * k)) - a = 0 + a := sr.inj h
    have h2 : 2 * a = 0 := by linear_combination -h1
    rcases (zm_two_mul_eq_zero_iff a).mp h2 with h3 | h3
    · simp [par, h3]
    · simp only [par, h3]; exact pz_k hke
  · rw [sr_mul_sr, sr_mul_sr] at h
    have h1 : (0 : ZMod (2 * k)) - a = a - 0 := r.inj h
    have h2 : 2 * a = 0 := by linear_combination -h1
    rcases (zm_two_mul_eq_zero_iff a).mp h2 with h3 | h3
    · simp [par, h3]
    · simp only [par, h3]; exact pz_k hke

@[expose] def alpha (j : ZMod (2 * k)) : DihedralGroup (2 * k) ≃* DihedralGroup (2 * k) where
  toFun x := match x with
    | r a => r a
    | sr a => sr (a + j)
  invFun x := match x with
    | r a => r a
    | sr a => sr (a - j)
  left_inv := by
    rintro (a | a)
    · rfl
    · simp
  right_inv := by
    rintro (a | a)
    · rfl
    · simp
  map_mul' := by
    rintro (a | a) (b | b)
    · rfl
    · simp only [r_mul_sr]; congr 1; ring
    · simp only [sr_mul_r]; congr 1; ring
    · simp only [sr_mul_sr]; congr 1; ring

omit [NeZero k] in
theorem alpha_sr (j a : ZMod (2 * k)) : alpha j (sr a) = sr (a + j) := rfl

end DihFacts

section Normalize

variable [NeZero k]

theorem z2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem pz_eq_one_iff (a : ZMod (2 * k)) : pz k a = 1 → ∃ b : ZMod (2 * k), a = 1 + 2 * b := by
  intro h
  have h1 : pz k (a - 1) = 0 := by
    rw [map_sub, pz_one, h]; exact sub_self _
  obtain ⟨b, hb⟩ := (pz_eq_zero_iff (a - 1)).mp h1
  exact ⟨b, by linear_combination hb⟩

omit [NeZero k] in
theorem r_nat_mem {P : Subgroup (DihedralGroup (2 * k))} (h1 : r (1 : ZMod (2 * k)) ∈ P) (n : ℕ) :
    r ((n : ℕ) : ZMod (2 * k)) ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : r (((n + 1 : ℕ)) : ZMod (2 * k)) = r (n : ZMod (2 * k)) * r 1 := by
      rw [r_mul_r]; push_cast; rfl
    rw [this]
    exact P.mul_mem ih h1

theorem r_all_mem {P : Subgroup (DihedralGroup (2 * k))} (h1 : r (1 : ZMod (2 * k)) ∈ P)
    (a : ZMod (2 * k)) : r a ∈ P := by
  have := r_nat_mem h1 a.val
  rwa [ZMod.natCast_zmod_val] at this

theorem r_two_mul_mem {P : Subgroup (DihedralGroup (2 * k))} (h2 : r (2 : ZMod (2 * k)) ∈ P)
    (b : ZMod (2 * k)) : r (2 * b) ∈ P := by
  have key : ∀ n : ℕ, r (2 * ((n : ℕ) : ZMod (2 * k))) ∈ P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : r (2 * (((n + 1 : ℕ)) : ZMod (2 * k))) = r (2 * (n : ZMod (2 * k))) * r 2 := by
        rw [r_mul_r]; push_cast; congr 1; ring
      rw [this]
      exact P.mul_mem ih h2
  have := key b.val
  rwa [ZMod.natCast_zmod_val] at this

theorem eq_Bsub_of (P : Subgroup (DihedralGroup (2 * k)))
    (ha : ∀ x, x * x ∈ P) (hb : sr (1 : ZMod (2 * k)) ∉ P)
    (hc : ∀ x, x ∈ P ∨ ∃ p ∈ P, x = p * sr 1)
    (hd : ∃ u ∈ P, ∃ v ∈ P, u ≠ v ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * u = 1 ∧ v * v = 1) : P = Bsub k := by
  have L1 : r (2 : ZMod (2 * k)) ∈ P := by
    have := ha (r 1)
    rwa [r_mul_r, one_add_one_eq_two] at this
  have L3 : r (1 : ZMod (2 * k)) ∉ P := by
    intro h1
    have hnr : ∀ a, sr a ∉ P := by
      intro a ha'
      apply hb
      have : sr (1 : ZMod (2 * k)) = sr a * r (1 - a) := by
        rw [sr_mul_r]; congr 1; ring
      rw [this]
      exact P.mul_mem ha' (r_all_mem h1 _)
    obtain ⟨u, hu, v, hv, huv, hu1, hv1, huu, hvv⟩ := hd
    have hu' : u = cc k := by
      rcases (mul_self_eq_one_iff u).mp huu with h | h | ⟨a, ha'⟩
      · exact absurd h hu1
      · exact h
      · exact absurd (ha' ▸ hu) (hnr a)
    have hv' : v = cc k := by
      rcases (mul_self_eq_one_iff v).mp hvv with h | h | ⟨a, ha'⟩
      · exact absurd h hv1
      · exact h
      · exact absurd (ha' ▸ hv) (hnr a)
    exact huv (hu'.trans hv'.symm)
  have L4 : sr (0 : ZMod (2 * k)) ∈ P := by
    rcases hc (sr 0) with h | ⟨p, hp, hpe⟩
    · exact h
    · exfalso
      apply L3
      have : r (1 : ZMod (2 * k)) = p := by
        have h1 : p = sr 0 * (sr 1)⁻¹ := by rw [hpe]; group
        rw [h1, inv_sr, sr_mul_sr]; congr 1; ring
      rw [this]; exact hp
  have L5 : ∀ x, par k x = 0 → x ∈ P := by
    intro x hx
    rcases x with a | a
    · obtain ⟨b, rfl⟩ := (pz_eq_zero_iff a).mp hx
      exact r_two_mul_mem L1 b
    · obtain ⟨b, rfl⟩ := (pz_eq_zero_iff a).mp hx
      have : sr (2 * b) = sr 0 * r (2 * b) := by rw [sr_mul_r, zero_add]
      rw [this]
      exact P.mul_mem L4 (r_two_mul_mem L1 b)
  have L6 : ∀ x ∈ P, par k x = 0 := by
    intro x hx
    rcases x with a | a
    · rcases z2_cases (pz k a) with h | h
      · exact h
      · exfalso
        obtain ⟨b, rfl⟩ := pz_eq_one_iff a h
        apply L3
        have : r (1 : ZMod (2 * k)) = r (1 + 2 * b) * (r (2 * b))⁻¹ := by
          rw [inv_r, r_mul_r]; congr 1; ring
        rw [this]
        exact P.mul_mem hx (P.inv_mem (r_two_mul_mem L1 b))
    · rcases z2_cases (pz k a) with h | h
      · exact h
      · exfalso
        obtain ⟨b, rfl⟩ := pz_eq_one_iff a h
        apply hb
        have : sr (1 : ZMod (2 * k)) = sr (1 + 2 * b) * r (-(2 * b)) := by
          rw [sr_mul_r]; congr 1; ring
        rw [this]
        have h2 : r (-(2 * b)) ∈ P := by
          have := P.inv_mem (r_two_mul_mem L1 b)
          rwa [inv_r] at this
        exact P.mul_mem hx h2
  ext x
  exact ⟨fun hx => L6 x hx, fun hx => L5 x hx⟩

end Normalize

section NormalizeGamma

variable [NeZero k] {Γ : Type} [Group Γ]

theorem normalize (hke : 2 ∣ k) (φ : Γ ≃* DihedralGroup (2 * k)) (P : Subgroup Γ) (ŷ : Γ)
    (h1 : ŷ * ŷ = 1) (h2 : ∀ g ∈ P, ŷ * g * ŷ⁻¹ ∈ P) (h3 : ŷ ∉ P)
    (h4 : ∀ g : Γ, g ∈ P ∨ ∃ p ∈ P, g = p * ŷ)
    (h5 : ∃ u ∈ P, ∃ v ∈ P, u ≠ v ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * u = 1 ∧ v * v = 1) :
    ∃ φ' : Γ ≃* DihedralGroup (2 * k), φ' ŷ = sr 1 ∧ ∀ g, g ∈ P ↔ par k (φ' g) = 0 := by
  have hsq : ∀ g : Γ, g * g ∈ P := by
    intro g
    rcases h4 g with hg | ⟨p, hp, rfl⟩
    · exact P.mul_mem hg hg
    · have : p * ŷ * (p * ŷ) = p * (ŷ * p * ŷ⁻¹) * (ŷ * ŷ) := by group
      rw [this, h1, mul_one]
      exact P.mul_mem hp (h2 p hp)
  have hrefl : ∃ j₀, φ ŷ = sr j₀ := by
    have hyy : φ ŷ * φ ŷ = 1 := by rw [← map_mul, h1, map_one]
    rcases (mul_self_eq_one_iff (φ ŷ)).mp hyy with h | h | h
    · exfalso
      apply h3
      have : ŷ = 1 := φ.injective (by rw [h, map_one])
      rw [this]; exact P.one_mem
    · exfalso
      apply h3
      obtain ⟨h0, hh⟩ := hke
      let g : Γ := φ.symm (r ((h0 : ℕ) : ZMod (2 * k)))
      have hg : g * g = ŷ := by
        apply φ.injective
        rw [map_mul, h]
        simp only [g, MulEquiv.apply_symm_apply, r_mul_r, cc]
        congr 1
        rw [← Nat.cast_add]
        congr 1
        omega
      rw [← hg]
      exact hsq g
    · exact h
  obtain ⟨j₀, hj₀⟩ := hrefl
  let φ'' : Γ ≃* DihedralGroup (2 * k) := φ.trans (alpha (1 - j₀))
  have hφ''y : φ'' ŷ = sr 1 := by
    show alpha (1 - j₀) (φ ŷ) = sr 1
    rw [hj₀, alpha_sr]; congr 1; ring
  set P' : Subgroup (DihedralGroup (2 * k)) := P.map φ''.toMonoidHom with hP'
  have hmem : ∀ x, x ∈ P' ↔ φ''.symm x ∈ P := fun x => Subgroup.mem_map_equiv
  have hPB : P' = Bsub k := by
    apply eq_Bsub_of
    · intro x
      rw [hmem, map_mul]
      exact hsq _
    · intro hmemb
      rw [hmem, ← hφ''y, MulEquiv.symm_apply_apply] at hmemb
      exact h3 hmemb
    · intro x
      rcases h4 (φ''.symm x) with h | ⟨p, hp, hpe⟩
      · left; exact (hmem x).mpr h
      · right
        refine ⟨φ'' p, (hmem _).mpr (by simpa using hp), ?_⟩
        rw [← hφ''y, ← map_mul, ← hpe]; simp
    · obtain ⟨u, hu, v, hv, huv, hu1, hv1, huu, hvv⟩ := h5
      refine ⟨φ'' u, (hmem _).mpr (by simpa using hu), φ'' v, (hmem _).mpr (by simpa using hv), ?_, ?_,
        ?_, ?_, ?_⟩
      · exact fun h => huv (φ''.injective h)
      · exact fun h => hu1 (φ''.injective (by rw [h, map_one]))
      · exact fun h => hv1 (φ''.injective (by rw [h, map_one]))
      · rw [← map_mul, huu, map_one]
      · rw [← map_mul, hvv, map_one]
  refine ⟨φ'', hφ''y, fun g => ?_⟩
  have := hmem (φ'' g)
  rw [MulEquiv.symm_apply_apply, hPB] at this
  exact this.symm

end NormalizeGamma

section Projection

open scoped Pointwise

variable {T : Type} [Group T]

theorem sr_ne_one {n : ℕ} (a : ZMod n) : (sr a : DihedralGroup n) ≠ 1 := by
  intro h
  rw [one_def] at h
  cases h

theorem sr_mul_self_eq_one {n : ℕ} (a : ZMod n) : (sr a : DihedralGroup n) * sr a = 1 := by
  rw [sr_mul_sr, sub_self, one_def]

theorem zpow_invol {y : T} (hy2 : y * y = 1) (i : ℤ) : y ^ i = 1 ∨ y ^ i = y := by
  have hinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  induction i using Int.induction_on with
  | zero => left; simp
  | succ n ih =>
    rcases ih with h | h
    · right; rw [zpow_add_one, h, one_mul]
    · left; rw [zpow_add_one, h, hy2]
  | pred n ih =>
    rcases ih with h | h
    · right; rw [zpow_sub_one, h, one_mul, hinv]
    · left; rw [zpow_sub_one, h, hinv, hy2]

theorem mem_sup_zpowers_iff {B : Subgroup T} {y : T} (hy2 : y * y = 1)
    (hy : ∀ a ∈ B, y * a * y⁻¹ ∈ B) {g : T} (hg : g ∈ B ⊔ zpowers y) :
    g ∈ B ∨ ∃ b ∈ B, g = b * y := by
  have hinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hnorm : zpowers y ≤ normalizer (B : Set T) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hy h hh, fun hh => ?_⟩
    have h1 := hy _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      rw [hinv]
      calc y * (y * h * y) * y = (y * y) * h * (y * y) := by group
        _ = h := by rw [hy2]; group
    rwa [e] at h1
  have h2 := coe_mul_of_right_le_normalizer_left B (zpowers y) hnorm
  have hg' : g ∈ ((B : Set T) * (zpowers y : Set T)) := by rw [← h2]; exact hg
  obtain ⟨b, hb, y', hy', rfl⟩ := Set.mem_mul.mp hg'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy'
  rcases zpow_invol hy2 i with h | h
  · left; rw [h, mul_one]; exact hb
  · right; exact ⟨b, hb, by rw [h]⟩

theorem y_not_mem {B : Subgroup T} {y : T} {k : ℕ} [NeZero k]
    (hB : IsDihedralOrder ↥B (2 * k)) (hBy : IsDihedralOrder ↥(B ⊔ zpowers y) (2 * (2 * k))) :
    y ∉ B := by
  intro hyB
  have h1 := card_of_isDihedralOrder hB
  have h2 := card_of_isDihedralOrder hBy
  have h3 : B ⊔ zpowers y = B := sup_eq_left.mpr (zpowers_le.mpr hyB)
  rw [h3] at h2
  have := NeZero.ne k
  omega

theorem exists_norm_iso {B : Subgroup T} {y : T} {k : ℕ} [NeZero k] (hke : 2 ∣ k)
    (hy2 : y * y = 1) (hy : ∀ a ∈ B, y * a * y⁻¹ ∈ B)
    (hB : IsDihedralOrder ↥B (2 * k)) (hBy : IsDihedralOrder ↥(B ⊔ zpowers y) (2 * (2 * k))) :
    ∃ φ : ↥(B ⊔ zpowers y) ≃* DihedralGroup (2 * k),
      φ ⟨y, mem_sup_right (mem_zpowers y)⟩ = sr 1 ∧
      ∀ g : ↥(B ⊔ zpowers y), (g : T) ∈ B ↔ par k (φ g) = 0 := by
  have hyB : y ∉ B := y_not_mem hB hBy
  obtain ⟨k', hk', -, ⟨φ0⟩⟩ := hBy
  have hk'2 : k' = 2 * k := by omega
  subst hk'2
  let ŷ : ↥(B ⊔ zpowers y) := ⟨y, mem_sup_right (mem_zpowers y)⟩
  let P : Subgroup ↥(B ⊔ zpowers y) := B.subgroupOf (B ⊔ zpowers y)
  have hmemP : ∀ g : ↥(B ⊔ zpowers y), g ∈ P ↔ (g : T) ∈ B := fun g => mem_subgroupOf
  have hk2 : 2 ≤ k := by
    obtain ⟨j, hj⟩ := hke
    have := NeZero.ne k
    omega
  have h1 : ŷ * ŷ = 1 := Subtype.ext hy2
  have h2 : ∀ g ∈ P, ŷ * g * ŷ⁻¹ ∈ P := by
    intro g hg
    rw [hmemP] at hg ⊢
    exact hy _ hg
  have h3 : ŷ ∉ P := by
    rw [hmemP]; exact hyB
  have h4 : ∀ g : ↥(B ⊔ zpowers y), g ∈ P ∨ ∃ p ∈ P, g = p * ŷ := by
    intro g
    rcases mem_sup_zpowers_iff hy2 hy g.2 with hg | ⟨b, hb, hgb⟩
    · left; rw [hmemP]; exact hg
    · right
      refine ⟨⟨b, mem_sup_left hb⟩, (hmemP _).mpr hb, Subtype.ext hgb⟩
  have h5 : ∃ u ∈ P, ∃ v ∈ P, u ≠ v ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * u = 1 ∧ v * v = 1 := by
    obtain ⟨k₀, hk₀, -, ⟨ψ⟩⟩ := hB
    have hk₀' : k₀ = k := by omega
    subst hk₀'
    let ι : ↥B →* ↥(B ⊔ zpowers y) := Subgroup.inclusion le_sup_left
    have hι : Function.Injective ι := Subgroup.inclusion_injective _
    have hne : (sr (0 : ZMod k₀) : DihedralGroup k₀) ≠ sr 1 := by
      intro h
      have h0 : (0 : ZMod k₀) = 1 := sr.inj h
      have h1' : ((1 : ℕ) : ZMod k₀) = 0 := by rw [Nat.cast_one]; exact h0.symm
      have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 1 k₀).mp h1')
      omega
    refine ⟨ι (ψ.symm (sr 0)), ?_, ι (ψ.symm (sr 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmemP]; exact (ψ.symm (sr 0)).2
    · rw [hmemP]; exact (ψ.symm (sr 1)).2
    · intro h; exact hne (ψ.symm.injective (hι h))
    · intro h
      have : ψ.symm (sr 0) = 1 := hι (by rw [h, map_one])
      exact sr_ne_one _ (ψ.symm.injective (this.trans ψ.symm.map_one.symm))
    · intro h
      have : ψ.symm (sr 1) = 1 := hι (by rw [h, map_one])
      exact sr_ne_one _ (ψ.symm.injective (this.trans ψ.symm.map_one.symm))
    · rw [← map_mul, ← map_mul, sr_mul_self_eq_one, map_one, map_one]
    · rw [← map_mul, ← map_mul, sr_mul_self_eq_one, map_one, map_one]
  obtain ⟨φ', hφ'y, hφ'⟩ := normalize hke φ0 P ŷ h1 h2 h3 h4 h5
  exact ⟨φ', hφ'y, fun g => (hmemP g).symm.trans (hφ' g)⟩

end Projection

section Retraction

variable {T : Type} [Group T]

theorem exists_retraction (N G : Subgroup T) [N.Normal] (hinf : G ⊓ N = ⊥) (hsup : G ⊔ N = ⊤) :
    ∃ p : T →* ↥G, (∀ g : ↥G, p (g : T) = g) ∧ ∀ t, p t = 1 ↔ t ∈ N := by
  let ι : ↥G →* T ⧸ N := (QuotientGroup.mk' N).comp G.subtype
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : (g : T) ∈ N := (QuotientGroup.eq_one_iff _).mp hg
    have h2 : (g : T) ∈ G ⊓ N := ⟨g.2, h1⟩
    rw [hinf] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hsurj : Function.Surjective ι := by
    intro x
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    have : t ∈ G ⊔ N := by rw [hsup]; exact mem_top t
    obtain ⟨g, hg, n, hn, rfl⟩ := mem_sup_of_normal_right.mp this
    refine ⟨⟨g, hg⟩, ?_⟩
    show QuotientGroup.mk' N g = QuotientGroup.mk' N (g * n)
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hn1, mul_one]
  let e : ↥G ≃* T ⧸ N := MulEquiv.ofBijective ι ⟨hinj, hsurj⟩
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N), ?_, ?_⟩
  · intro g
    show e.symm (QuotientGroup.mk' N (g : T)) = g
    have : e g = QuotientGroup.mk' N (g : T) := rfl
    rw [← this, MulEquiv.symm_apply_apply]
  · intro t
    show e.symm (QuotientGroup.mk' N t) = 1 ↔ t ∈ N
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff t

end Retraction

section Construct

variable {T : Type} [Group T] {k : ℕ} [NeZero k]

theorem normal_of_commute (B₁ B₂ : Subgroup T) (y : T)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hy2 : y * y = 1)
    (hy₂ : ∀ a ∈ B₂, y * a * y⁻¹ ∈ B₂) (hT : B₁ ⊔ B₂ ⊔ zpowers y = ⊤) : B₂.Normal := by
  have hinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hn1 : B₁ ≤ normalizer (B₂ : Set T) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 := hcomm a ha h hh
      have e : a * h * a⁻¹ = h := by rw [h1]; group
      rw [e]; exact hh
    · intro hh
      have h1 := hcomm a⁻¹ (B₁.inv_mem ha) _ hh
      have e : a⁻¹ * (a * h * a⁻¹) * a = h := by group
      have e2 : a⁻¹ * (a * h * a⁻¹) * a = a * h * a⁻¹ := by rw [h1]; group
      rw [← e, e2]; exact hh
  have hn2 : B₂ ≤ normalizer (B₂ : Set T) := Subgroup.le_normalizer
  have hn3 : zpowers y ≤ normalizer (B₂ : Set T) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hy₂ h hh, fun hh => ?_⟩
    have h1 := hy₂ _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      rw [hinv]
      calc y * (y * h * y) * y = (y * y) * h * (y * y) := by group
        _ = h := by rw [hy2]; group
    rwa [e] at h1
  have hall : normalizer (B₂ : Set T) = ⊤ := by
    rw [eq_top_iff, ← hT]
    exact sup_le (sup_le hn1 hn2) hn3
  exact normalizer_eq_top_iff.mp hall

theorem inf_eq_bot_of_norm {B B' : Subgroup T} {y : T} (hke : 2 ∣ k)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B', a * b = b * a) (hinf : B ⊓ B' = ⊥)
    (φ : ↥(B ⊔ zpowers y) ≃* DihedralGroup (2 * k))
    (hφ : ∀ g : ↥(B ⊔ zpowers y), (g : T) ∈ B ↔ par k (φ g) = 0) :
    (B ⊔ zpowers y) ⊓ B' = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgG, hgB'⟩
  let g' : ↥(B ⊔ zpowers y) := ⟨g, hgG⟩
  let b₀ : ↥(B ⊔ zpowers y) := φ.symm (sr 0)
  have hb₀ : (b₀ : T) ∈ B := (hφ b₀).mpr (by
    show par k (φ (φ.symm (sr 0))) = 0
    rw [MulEquiv.apply_symm_apply]
    show pz k 0 = 0
    exact map_zero _)
  have hc : b₀ * g' = g' * b₀ := Subtype.ext (hcomm _ hb₀ g hgB')
  have hc' : sr 0 * φ g' = φ g' * sr 0 := by
    have := congrArg φ hc
    rw [map_mul, map_mul] at this
    have h0 : φ b₀ = sr 0 := MulEquiv.apply_symm_apply φ _
    rwa [h0] at this
  have hpar : par k (φ g') = 0 := par_eq_zero_of_comm hke hc'.symm
  have hgB : g ∈ B := (hφ g').mpr hpar
  have : g ∈ B ⊓ B' := ⟨hgB, hgB'⟩
  rw [hinf] at this
  exact this

theorem exists_equiv_Wsub (hke : 2 ∣ k)
    (B₁ B₂ : Subgroup T) (y : T)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hinf : B₁ ⊓ B₂ = ⊥)
    (hy2 : y * y = 1)
    (hy₁ : ∀ a ∈ B₁, y * a * y⁻¹ ∈ B₁) (hy₂ : ∀ a ∈ B₂, y * a * y⁻¹ ∈ B₂)
    (hT : B₁ ⊔ B₂ ⊔ zpowers y = ⊤)
    (hB₁ : IsDihedralOrder ↥B₁ (2 * k)) (hB₂ : IsDihedralOrder ↥B₂ (2 * k))
    (hB₁y : IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 * (2 * k)))
    (hB₂y : IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 * (2 * k))) :
    Nonempty (T ≃* ↥(Wsub k)) := by
  obtain ⟨φ₁, hφ₁y, hφ₁⟩ := exists_norm_iso hke hy2 hy₁ hB₁ hB₁y
  obtain ⟨φ₂, hφ₂y, hφ₂⟩ := exists_norm_iso hke hy2 hy₂ hB₂ hB₂y
  have hcomm' : ∀ a ∈ B₂, ∀ b ∈ B₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hinf' : B₂ ⊓ B₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hT' : B₂ ⊔ B₁ ⊔ zpowers y = ⊤ := by rw [sup_comm B₂ B₁]; exact hT
  have hn₁ : B₁.Normal := normal_of_commute B₂ B₁ y hcomm' hy2 hy₁ hT'
  have hn₂ : B₂.Normal := normal_of_commute B₁ B₂ y hcomm hy2 hy₂ hT
  have hG₁ := inf_eq_bot_of_norm hke hcomm hinf φ₁ hφ₁
  have hG₂ := inf_eq_bot_of_norm hke hcomm' hinf' φ₂ hφ₂
  have hs₁ : (B₁ ⊔ zpowers y) ⊔ B₂ = ⊤ := by
    rw [eq_top_iff, ← hT]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
      (le_sup_of_le_left le_sup_right)
  have hs₂ : (B₂ ⊔ zpowers y) ⊔ B₁ = ⊤ := by
    rw [eq_top_iff, ← hT]
    exact sup_le (sup_le le_sup_right (le_sup_of_le_left le_sup_left))
      (le_sup_of_le_left le_sup_right)
  obtain ⟨p₁, hp₁, hp₁k⟩ := exists_retraction B₂ (B₁ ⊔ zpowers y) hG₁ hs₁
  obtain ⟨p₂, hp₂, hp₂k⟩ := exists_retraction B₁ (B₂ ⊔ zpowers y) hG₂ hs₂
  let θ₁ : T →* DihedralGroup (2 * k) := φ₁.toMonoidHom.comp p₁
  let θ₂ : T →* DihedralGroup (2 * k) := φ₂.toMonoidHom.comp p₂
  have hθ₁ : ∀ g : ↥(B₁ ⊔ zpowers y), θ₁ g = φ₁ g := by
    intro g
    show φ₁ (p₁ g) = φ₁ g
    rw [hp₁]
  have hθ₂ : ∀ g : ↥(B₂ ⊔ zpowers y), θ₂ g = φ₂ g := by
    intro g
    show φ₂ (p₂ g) = φ₂ g
    rw [hp₂]
  have hθ₁k : ∀ t, θ₁ t = 1 ↔ t ∈ B₂ := by
    intro t
    show φ₁ (p₁ t) = 1 ↔ t ∈ B₂
    rw [MulEquiv.map_eq_one_iff]
    exact hp₁k t
  have hθ₂k : ∀ t, θ₂ t = 1 ↔ t ∈ B₁ := by
    intro t
    show φ₂ (p₂ t) = 1 ↔ t ∈ B₁
    rw [MulEquiv.map_eq_one_iff]
    exact hp₂k t
  let θ : T →* DihedralGroup (2 * k) × DihedralGroup (2 * k) := θ₁.prod θ₂
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : θ₁ g = 1 := congrArg Prod.fst hg
    have h2 : θ₂ g = 1 := congrArg Prod.snd hg
    have : g ∈ B₁ ⊓ B₂ := ⟨(hθ₂k g).mp h2, (hθ₁k g).mp h1⟩
    rw [hinf] at this
    exact this
  have hyG₁ : y ∈ B₁ ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hyG₂ : y ∈ B₂ ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hθy₁ : θ₁ y = sr 1 := by
    have := hθ₁ ⟨y, hyG₁⟩
    rw [hφ₁y] at this
    exact this
  have hθy₂ : θ₂ y = sr 1 := by
    have := hθ₂ ⟨y, hyG₂⟩
    rw [hφ₂y] at this
    exact this
  have hrange : ∀ g, θ g ∈ Wsub k := by
    let E : Subgroup T :=
      { carrier := {g | par k (θ₁ g) = par k (θ₂ g)}
        mul_mem' := by
          intro a b ha hb
          change par k (θ₁ (a * b)) = par k (θ₂ (a * b))
          change par k (θ₁ a) = par k (θ₂ a) at ha
          change par k (θ₁ b) = par k (θ₂ b) at hb
          rw [map_mul, map_mul, par_mul, par_mul, ha, hb]
        one_mem' := by
          change par k (θ₁ 1) = par k (θ₂ 1)
          rw [map_one, map_one]
        inv_mem' := by
          intro a ha
          change par k (θ₁ a⁻¹) = par k (θ₂ a⁻¹)
          change par k (θ₁ a) = par k (θ₂ a) at ha
          rw [map_inv, map_inv, par_inv, par_inv, ha] }
    have hE : E = ⊤ := by
      rw [eq_top_iff, ← hT]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro g hg
        change par k (θ₁ g) = par k (θ₂ g)
        have e1 : θ₁ g = φ₁ ⟨g, mem_sup_left hg⟩ := hθ₁ ⟨g, mem_sup_left hg⟩
        have e2 : θ₂ g = 1 := (hθ₂k g).mpr hg
        rw [e1, e2, par_one]
        exact (hφ₁ ⟨g, mem_sup_left hg⟩).mp hg
      · intro g hg
        change par k (θ₁ g) = par k (θ₂ g)
        have e1 : θ₂ g = φ₂ ⟨g, mem_sup_left hg⟩ := hθ₂ ⟨g, mem_sup_left hg⟩
        have e2 : θ₁ g = 1 := (hθ₁k g).mpr hg
        rw [e1, e2, par_one]
        exact ((hφ₂ ⟨g, mem_sup_left hg⟩).mp hg).symm
      · rw [zpowers_le]
        change par k (θ₁ y) = par k (θ₂ y)
        rw [hθy₁, hθy₂]
    intro g
    have : g ∈ E := by rw [hE]; exact mem_top g
    exact this
  have hsurj : ∀ w : ↥(Wsub k), ∃ g, θ g = (w : DihedralGroup (2 * k) × DihedralGroup (2 * k)) := by
    have hB1elt : ∀ b : DihedralGroup (2 * k), par k b = 0 → ∃ g : T, θ g = (b, 1) := by
      intro b hb
      let g' : ↥(B₁ ⊔ zpowers y) := φ₁.symm b
      have hg : (g' : T) ∈ B₁ := (hφ₁ g').mpr (by
        show par k (φ₁ (φ₁.symm b)) = 0
        rw [MulEquiv.apply_symm_apply]; exact hb)
      refine ⟨g', Prod.ext ?_ ?_⟩
      · show θ₁ g' = b
        rw [hθ₁]
        exact MulEquiv.apply_symm_apply φ₁ b
      · show θ₂ g' = 1
        exact (hθ₂k _).mpr hg
    have hB2elt : ∀ b : DihedralGroup (2 * k), par k b = 0 → ∃ g : T, θ g = (1, b) := by
      intro b hb
      let g' : ↥(B₂ ⊔ zpowers y) := φ₂.symm b
      have hg : (g' : T) ∈ B₂ := (hφ₂ g').mpr (by
        show par k (φ₂ (φ₂.symm b)) = 0
        rw [MulEquiv.apply_symm_apply]; exact hb)
      refine ⟨g', Prod.ext ?_ ?_⟩
      · show θ₁ g' = 1
        exact (hθ₁k _).mpr hg
      · show θ₂ g' = b
        rw [hθ₂]
        exact MulEquiv.apply_symm_apply φ₂ b
    rintro ⟨⟨a, b⟩, hab⟩
    have hab' : par k a = par k b := hab
    have hsg : par k (sr (1 : ZMod (2 * k))) = 1 := by
      show pz k 1 = 1
      exact pz_one
    rcases z2_cases (par k a) with h0 | h1
    · obtain ⟨g₁, hg₁⟩ := hB1elt a h0
      obtain ⟨g₂, hg₂⟩ := hB2elt b (hab' ▸ h0)
      refine ⟨g₁ * g₂, ?_⟩
      rw [map_mul, hg₁, hg₂]
      simp
    · have hb1 : par k b = 1 := hab' ▸ h1
      have ha' : par k (a * (sr (1 : ZMod (2 * k)))⁻¹) = 0 := by
        rw [par_mul, par_inv, h1, hsg]; decide
      have hb' : par k (b * (sr (1 : ZMod (2 * k)))⁻¹) = 0 := by
        rw [par_mul, par_inv, hb1, hsg]; decide
      obtain ⟨g₁, hg₁⟩ := hB1elt _ ha'
      obtain ⟨g₂, hg₂⟩ := hB2elt _ hb'
      refine ⟨g₁ * g₂ * y, ?_⟩
      have hθy : θ y = (sr 1, sr 1) := Prod.ext hθy₁ hθy₂
      rw [map_mul, map_mul, hg₁, hg₂, hθy]
      simp [inv_sr, mul_assoc]
  exact ⟨MulEquiv.ofBijective (θ.codRestrict (Wsub k) hrange)
    ⟨fun g h hgh => hinj (congrArg Subtype.val hgh), fun w => by
      obtain ⟨g, hg⟩ := hsurj w
      exact ⟨g, Subtype.ext hg⟩⟩⟩

end Construct

section Auto

variable [NeZero k]

@[expose] def swapW (k : ℕ) : ↥(Wsub k) ≃* ↥(Wsub k) where
  toFun w := ⟨(w.1.2, w.1.1), (mem_Wsub.mp w.2).symm⟩
  invFun w := ⟨(w.1.2, w.1.1), (mem_Wsub.mp w.2).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [NeZero k] in
theorem swapW_val (w : ↥(Wsub k)) : (swapW k w).1 = (w.1.2, w.1.1) := rfl

@[expose] def tw (k : ℕ) : DihedralGroup (2 * k) → DihedralGroup (2 * k)
  | r _ => 1
  | sr _ => cc k

omit [NeZero k] in
theorem tw_mul (a b : DihedralGroup (2 * k)) : tw k (a * b) = tw k a * tw k b := by
  rcases a with a | a <;> rcases b with b | b
  · simp [tw]
  · simp [tw, r_mul_sr]
  · simp [tw, sr_mul_r]
  · simp only [tw, sr_mul_sr]; exact (cc_mul_cc).symm

omit [NeZero k] in
theorem tw_tw (a : DihedralGroup (2 * k)) : tw k a * tw k a = 1 := by
  rcases a with a | a
  · simp [tw]
  · exact cc_mul_cc

omit [NeZero k] in
theorem tw_central (a x : DihedralGroup (2 * k)) : tw k a * x = x * tw k a := by
  rcases a with a | a
  · simp [tw]
  · exact (cc_central x).symm

omit [NeZero k] in
theorem par_tw (hke : 2 ∣ k) (a : DihedralGroup (2 * k)) : par k (tw k a) = 0 := by
  rcases a with a | a
  · simp only [tw]; exact par_one
  · exact par_cc hke

@[expose] def twistW (hke : 2 ∣ k) : ↥(Wsub k) ≃* ↥(Wsub k) where
  toFun w := ⟨(w.1.1, w.1.2 * tw k w.1.1), by
    have := mem_Wsub.mp w.2
    show par k w.1.1 = par k (w.1.2 * tw k w.1.1)
    rw [par_mul, par_tw hke, add_zero]; exact this⟩
  invFun w := ⟨(w.1.1, w.1.2 * tw k w.1.1), by
    have := mem_Wsub.mp w.2
    show par k w.1.1 = par k (w.1.2 * tw k w.1.1)
    rw [par_mul, par_tw hke, add_zero]; exact this⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show w.1.2 * tw k w.1.1 * tw k w.1.1 = w.1.2
      rw [mul_assoc, tw_tw, mul_one]
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show w.1.2 * tw k w.1.1 * tw k w.1.1 = w.1.2
      rw [mul_assoc, tw_tw, mul_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show a.1.2 * b.1.2 * tw k (a.1.1 * b.1.1) = a.1.2 * tw k a.1.1 * (b.1.2 * tw k b.1.1)
      rw [tw_mul]
      calc a.1.2 * b.1.2 * (tw k a.1.1 * tw k b.1.1)
          = a.1.2 * (b.1.2 * tw k a.1.1) * tw k b.1.1 := by simp only [mul_assoc]
        _ = a.1.2 * (tw k a.1.1 * b.1.2) * tw k b.1.1 := by rw [tw_central]
        _ = a.1.2 * tw k a.1.1 * (b.1.2 * tw k b.1.1) := by simp only [mul_assoc]

omit [NeZero k] in
theorem twistW_val (hke : 2 ∣ k) (w : ↥(Wsub k)) :
    (twistW hke w).1 = (w.1.1, w.1.2 * tw k w.1.1) := rfl

end Auto

section Card

variable [NeZero k]

theorem z2_add_eq_zero_iff (u v : ZMod 2) : u + v = 0 ↔ u = v := by
  revert u v; decide

@[expose] def chiW (k : ℕ) :
    DihedralGroup (2 * k) × DihedralGroup (2 * k) →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd (par k p.1 + par k p.2)
  map_one' := by
    show Multiplicative.ofAdd (par k (1 : DihedralGroup (2 * k)) + par k (1 : DihedralGroup (2 * k))) = 1
    rw [par_one, add_zero]; rfl
  map_mul' p q := by
    show Multiplicative.ofAdd (par k (p.1 * q.1) + par k (p.2 * q.2)) =
      Multiplicative.ofAdd (par k p.1 + par k p.2) * Multiplicative.ofAdd (par k q.1 + par k q.2)
    rw [← ofAdd_add, par_mul, par_mul]
    congr 1
    ring

omit [NeZero k] in
theorem ker_chiW : (chiW k).ker = Wsub k := by
  ext p
  rw [MonoidHom.mem_ker]
  show Multiplicative.ofAdd (par k p.1 + par k p.2) = 1 ↔ par k p.1 = par k p.2
  rw [← z2_add_eq_zero_iff]
  exact ⟨fun h => h, fun h => h⟩

omit [NeZero k] in
theorem chiW_surjective : Function.Surjective (chiW k) := by
  intro m
  rcases z2_cases (Multiplicative.toAdd m) with h | h
  · refine ⟨1, ?_⟩
    have : m = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h]; rfl
    rw [this, map_one]
  · refine ⟨(sr 1, 1), ?_⟩
    have : m = Multiplicative.ofAdd 1 := by
      apply Multiplicative.toAdd.injective
      rw [h]; rfl
    rw [this]
    show Multiplicative.ofAdd (par k (sr 1) + par k (1 : DihedralGroup (2 * k))) = _
    rw [par_one, add_zero]
    show Multiplicative.ofAdd (pz k 1) = _
    rw [pz_one]

omit [NeZero k] in
theorem card_Wsub : Nat.card ↥(Wsub k) = 8 * k ^ 2 := by
  have h1 := Subgroup.card_mul_index (Wsub k)
  have h2 : (Wsub k).index = 2 := by
    rw [← ker_chiW, Subgroup.index_ker]
    have : (chiW k).range = ⊤ := MonoidHom.range_eq_top.mpr chiW_surjective
    rw [this, Subgroup.card_top]
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    simp
  rw [h2, Nat.card_prod, DihedralGroup.nat_card] at h1
  nlinarith

end Card

section CfgLemmas

variable {G : Type} [Group G] {m : ℕ} {T₁ : Subgroup G} {z t : G}

theorem Cfg.zz (h : Cfg G m T₁ z t) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.hz, pow_two] at this

theorem Cfg.tt (h : Cfg G m T₁ z t) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [h.ht, pow_two] at this

theorem Cfg.z_ne_one (h : Cfg G m T₁ z t) : z ≠ 1 := by
  intro hz
  have := h.hz
  rw [hz, orderOf_one] at this
  omega

theorem Cfg.commU (h : Cfg G m T₁ z t) : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a _ b hb
  have htc := Subgroup.mem_center_iff.mp h.htc
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (show Commute a t from (htc a)) i).eq

theorem Cfg.infU (h : Cfg G m T₁ z t) : zpowers z ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxz, hxt⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxz
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxt
  rcases zpow_invol h.zz i with h1 | h1
  · rw [h1]; exact one_mem _
  · exfalso
    rw [h1] at hj
    rcases zpow_invol h.tt j with h2 | h2
    · rw [h2] at hj; exact h.z_ne_one hj.symm
    · rw [h2] at hj; exact h.hzt hj.symm

theorem Cfg.card_U (h : Cfg G m T₁ z t) : Nat.card ↥(zpowers z ⊔ zpowers t) = 4 := by
  rw [CFSG.GH74.GLS.IVK.Proofs2.card_sup_eq_mul h.commU h.infU, Nat.card_zpowers, Nat.card_zpowers, h.hz, h.ht]

theorem Cfg.commUT (h : Cfg G m T₁ z t) :
    ∀ a ∈ zpowers z ⊔ zpowers t, ∀ b ∈ T₁, a * b = b * a := by
  have h1 : zpowers z ≤ centralizer (T₁ : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro g hg
    exact (h.hzT₁ g hg).symm
  have h2 : zpowers t ≤ centralizer (T₁ : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp h.htc g)
  have h3 : zpowers z ⊔ zpowers t ≤ centralizer (T₁ : Set G) := sup_le h1 h2
  intro a ha b hb
  exact ((mem_centralizer_iff.mp (h3 ha)) b hb).symm

theorem Cfg.card_C (h : Cfg G m T₁ z t) : Nat.card ↥(centralizer ({z} : Set G)) = 4 * m := by
  rw [h.hC, CFSG.GH74.GLS.IVK.Proofs2.card_sup_eq_mul h.commUT h.hinfU, h.card_U, card_of_isDihedralOrder h.dih]

end CfgLemmas

section Classify

variable [NeZero k]

theorem dihedral_noncomm {n : ℕ} (hn : 3 ≤ n) : (r 1 : DihedralGroup n) * sr 0 ≠ sr 0 * r 1 := by
  intro h
  rw [r_mul_sr, sr_mul_r] at h
  have h1 : (0 : ZMod n) - 1 = 0 + 1 := sr.inj h
  have h2 : (2 : ZMod n) = 0 := by linear_combination -h1
  have h3 : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h2
  have h4 := (ZMod.natCast_eq_zero_iff 2 n).mp h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem comm_of_sq_one {G : Type} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  have h2 : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
  rw [inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy, h1] at h2
  exact h2

omit [NeZero k] in
theorem sq_one_of_comm_sr (x : DihedralGroup (2 * k)) (a : ZMod (2 * k))
    (h : x * sr a = sr a * x) : x * x = 1 := by
  rcases x with b | b
  · rw [r_mul_sr, sr_mul_r] at h
    have h1 : a - b = a + b := sr.inj h
    have h2 : 2 * b = 0 := by linear_combination -h1
    rw [r_mul_r, one_def]
    congr 1
    rw [← two_mul]
    exact h2
  · exact sr_mul_self_eq_one b

omit [NeZero k] in
theorem cc_or_one_comm (x : DihedralGroup (2 * k)) (hx : x = 1 ∨ x = cc k)
    (y : DihedralGroup (2 * k)) : y * x = x * y := by
  rcases hx with rfl | rfl
  · rw [mul_one, one_mul]
  · exact cc_central y

theorem classify_z (hke : 2 ∣ k) (hk : 3 ≤ k) {T₁ : Subgroup ↥(Wsub k)} {z t : ↥(Wsub k)}
    (h : Cfg ↥(Wsub k) (2 * k) T₁ z t) :
    ∃ (a : ZMod (2 * k)) (ε : DihedralGroup (2 * k)), pz k a = 0 ∧ (ε = 1 ∨ ε = cc k) ∧
      (z.1 = (sr a, ε) ∨ z.1 = (ε, sr a)) := by
  have hzz : z * z = 1 := h.zz
  have hz₁ : z.1.1 * z.1.1 = 1 := congrArg (fun w : ↥(Wsub k) => w.1.1) hzz
  have hz₂ : z.1.2 * z.1.2 = 1 := congrArg (fun w : ↥(Wsub k) => w.1.2) hzz
  have hpar : par k z.1.1 = par k z.1.2 := mem_Wsub.mp z.2
  have hcent : (z.1.1 = 1 ∨ z.1.1 = cc k) → (z.1.2 = 1 ∨ z.1.2 = cc k) → False := by
    intro ha hb
    have htop : centralizer ({z} : Set ↥(Wsub k)) = ⊤ := by
      rw [eq_top_iff']
      intro g
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Prod.ext
      · exact cc_or_one_comm _ ha _
      · exact cc_or_one_comm _ hb _
    have hc := h.card_C
    rw [htop, Subgroup.card_top, card_Wsub] at hc
    have hk1 : 2 ≤ k := by omega
    nlinarith
  have hrefl : ∀ a a' : ZMod (2 * k), z.1.1 = sr a → z.1.2 = sr a' → False := by
    intro a a' ha ha'
    have hsq : ∀ g ∈ T₁, g.1.1 * g.1.1 = 1 ∧ g.1.2 * g.1.2 = 1 := by
      intro g hg
      have e := h.hzT₁ g hg
      have e1 : z.1.1 * g.1.1 = g.1.1 * z.1.1 := congrArg (fun w : ↥(Wsub k) => w.1.1) e
      have e2 : z.1.2 * g.1.2 = g.1.2 * z.1.2 := congrArg (fun w : ↥(Wsub k) => w.1.2) e
      rw [ha] at e1
      rw [ha'] at e2
      exact ⟨sq_one_of_comm_sr _ a e1.symm, sq_one_of_comm_sr _ a' e2.symm⟩
    have hcomm : ∀ g ∈ T₁, ∀ g' ∈ T₁, g * g' = g' * g := by
      intro g hg g' hg'
      apply Subtype.ext
      apply Prod.ext
      · exact comm_of_sq_one (hsq g hg).1 (hsq g' hg').1 (hsq (g * g') (T₁.mul_mem hg hg')).1
      · exact comm_of_sq_one (hsq g hg).2 (hsq g' hg').2 (hsq (g * g') (T₁.mul_mem hg hg')).2
    obtain ⟨k', hk', -, ⟨φ⟩⟩ := h.dih
    have hk'k : k' = k := by omega
    subst hk'k
    apply dihedral_noncomm hk
    have := hcomm (φ.symm (r 1)).1 (φ.symm (r 1)).2 (φ.symm (sr 0)).1 (φ.symm (sr 0)).2
    have h2 : φ.symm (r 1) * φ.symm (sr 0) = φ.symm (sr 0) * φ.symm (r 1) := Subtype.ext this
    rw [← map_mul, ← map_mul] at h2
    exact φ.symm.injective h2
  rcases (mul_self_eq_one_iff _).mp hz₁ with h1 | h1 | ⟨a, h1⟩ <;>
    rcases (mul_self_eq_one_iff _).mp hz₂ with h2 | h2 | ⟨a', h2⟩
  · exact (hcent (Or.inl h1) (Or.inl h2)).elim
  · exact (hcent (Or.inl h1) (Or.inr h2)).elim
  · refine ⟨a', 1, ?_, Or.inl rfl, Or.inr (Prod.ext h1 h2)⟩
    have := hpar; rw [h1, h2, par_one] at this
    exact this.symm
  · exact (hcent (Or.inr h1) (Or.inl h2)).elim
  · exact (hcent (Or.inr h1) (Or.inr h2)).elim
  · refine ⟨a', cc k, ?_, Or.inr rfl, Or.inr (Prod.ext h1 h2)⟩
    have := hpar; rw [h1, h2] at this
    have h3 : par k (cc k) = 0 := par_cc hke
    rw [h3] at this
    exact this.symm
  · refine ⟨a, 1, ?_, Or.inl rfl, Or.inl (Prod.ext h1 h2)⟩
    have := hpar; rw [h1, h2, par_one] at this
    exact this
  · refine ⟨a, cc k, ?_, Or.inr rfl, Or.inl (Prod.ext h1 h2)⟩
    have := hpar; rw [h1, h2] at this
    have h3 : par k (cc k) = 0 := par_cc hke
    rw [h3] at this
    exact this
  · exact (hrefl a a' h1 h2).elim

end Classify

section BDihedral

variable [NeZero k]

theorem zpow_r_exists {n : ℕ} (a : ZMod n) (i : ℤ) : ∃ c : ZMod n, (r a : DihedralGroup n) ^ i = r c := by
  induction i using Int.induction_on with
  | zero => exact ⟨0, by rw [zpow_zero, one_def]⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c + a, by rw [zpow_add_one, hc, r_mul_r]⟩
  | pred m ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c - a, by rw [zpow_sub_one, hc, inv_r, r_mul_r]; congr 1; ring⟩

theorem orderOf_r_two (hk : 2 ≤ k) : orderOf (r (2 : ZMod (2 * k)) : DihedralGroup (2 * k)) = k := by
  rw [DihedralGroup.orderOf_r]
  have h1 : (2 : ZMod (2 * k)).val = 2 := by
    have : ((2 : ℕ) : ZMod (2 * k)).val = 2 % (2 * k) := ZMod.val_natCast (2 * k) 2
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this
  rw [h1]
  have h2 : (2 * k).gcd 2 = 2 := Nat.gcd_eq_right (dvd_mul_right 2 k)
  rw [h2]
  omega

theorem closure_eq_Bsub : Subgroup.closure ({r (2 : ZMod (2 * k)), sr 0} : Set (DihedralGroup (2 * k))) =
    Bsub k := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · show par k (r (2 : ZMod (2 * k))) = 0
      show pz k 2 = 0
      have h2 : ((2 : ℕ) : ZMod (2 * k)) = 2 := by norm_num
      rw [← h2, pz_natCast]
      decide
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      show pz k 0 = 0
      exact map_zero _
  · intro x hx
    have h2 : r (2 : ZMod (2 * k)) ∈ Subgroup.closure ({r (2 : ZMod (2 * k)), sr 0} : Set (DihedralGroup (2 * k))) :=
      Subgroup.subset_closure (by simp)
    have h4 : sr (0 : ZMod (2 * k)) ∈ Subgroup.closure ({r (2 : ZMod (2 * k)), sr 0} : Set (DihedralGroup (2 * k))) :=
      Subgroup.subset_closure (by simp)
    rcases x with a | a
    · obtain ⟨b, rfl⟩ := (pz_eq_zero_iff a).mp hx
      exact r_two_mul_mem h2 b
    · obtain ⟨b, rfl⟩ := (pz_eq_zero_iff a).mp hx
      have : sr (2 * b) = sr 0 * r (2 * b) := by rw [sr_mul_r, zero_add]
      rw [this]
      exact Subgroup.mul_mem _ h4 (r_two_mul_mem h2 b)

theorem Bsub_equiv (hk : 2 ≤ k) : Nonempty (↥(Bsub k) ≃* DihedralGroup k) := by
  have h1 : (sr (0 : ZMod (2 * k)) : DihedralGroup (2 * k)) ^ 2 = 1 := by
    rw [pow_two]; exact sr_mul_self_eq_one 0
  have h2 : (sr (0 : ZMod (2 * k)) : DihedralGroup (2 * k)) * r 2 * (sr 0)⁻¹ = (r 2)⁻¹ := by
    rw [inv_sr, inv_r, sr_mul_r, sr_mul_sr, zero_add]
    congr 1
    ring
  have h3 : (sr (0 : ZMod (2 * k)) : DihedralGroup (2 * k)) ∉ Subgroup.zpowers (r 2) := by
    intro h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    obtain ⟨c, hc⟩ := zpow_r_exists (2 : ZMod (2 * k)) i
    rw [hc] at hi
    cases hi
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup h1 h2 h3
  rw [orderOf_r_two hk, closure_eq_Bsub] at e
  exact ⟨e⟩

theorem card_Bsub (hk : 2 ≤ k) : Nat.card ↥(Bsub k) = 2 * k := by
  obtain ⟨e⟩ := Bsub_equiv hk
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

end BDihedral

section Aux

variable [NeZero k]

theorem Dcent_B (hk : 3 ≤ k) (x : DihedralGroup (2 * k)) (h1 : sr 0 * x = x * sr 0)
    (h2 : r 2 * x = x * r 2) : x = 1 ∨ x = cc k := by
  rcases x with a | a
  · rw [sr_mul_r, r_mul_sr] at h1
    have h3 : (0 : ZMod (2 * k)) + a = 0 - a := sr.inj h1
    have h4 : 2 * a = 0 := by linear_combination h3
    rcases (zm_two_mul_eq_zero_iff a).mp h4 with h5 | h5
    · left; rw [h5, one_def]
    · right; rw [h5]; rfl
  · exfalso
    rw [r_mul_sr, sr_mul_r] at h2
    have h3 : a - 2 = a + 2 := sr.inj h2
    have h4 : (4 : ZMod (2 * k)) = 0 := by linear_combination -h3
    exact zm_four_ne_zero hk h4

theorem central_is_square {P : Type} [Group P] {k₁ k₂ : ℕ} [NeZero k₂] (hk₁ : k₁ = 2 * k₂)
    (hk2 : 2 ≤ k₂) (he : 2 ∣ k₂) (φ : P ≃* DihedralGroup k₁) {x : P} (hx1 : x ≠ 1)
    (hxc : ∀ g : P, g * x = x * g) : ∃ g : P, g * g = x := by
  subst hk₁
  have hc : ∀ h : DihedralGroup (2 * k₂), h * φ x = φ x * h := by
    intro h
    have := hxc (φ.symm h)
    have h2 := congrArg φ this
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  obtain ⟨a, ha, h2a⟩ := CFSG.GH74.GLS.IVK.Proofs2.dihedral_central_rot (by omega) hc
  rcases (zm_two_mul_eq_zero_iff a).mp h2a with h5 | h5
  · exfalso
    apply hx1
    apply φ.injective
    rw [ha, h5, map_one, one_def]
  · obtain ⟨j, hj⟩ := he
    refine ⟨φ.symm (r ((j : ℕ) : ZMod (2 * k₂))), ?_⟩
    apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, ha, h5, r_mul_r]
    congr 1
    rw [← Nat.cast_add, hj]
    congr 1
    omega

theorem dihedral_of_proj {G : Type} [Group G] (N : Subgroup G) (y₀ : G) (hy2 : y₀ * y₀ = 1)
    (hy : ∀ a ∈ N, y₀ * a * y₀⁻¹ ∈ N) (p : G →* DihedralGroup (2 * k)) (hpy : p y₀ = sr 1)
    (hinj : ∀ a ∈ N, p a = 1 → a = 1) (hpar : ∀ a ∈ N, par k (p a) = 0)
    (hsurj : ∀ b, par k b = 0 → ∃ a ∈ N, p a = b) :
    IsDihedralOrder ↥(N ⊔ zpowers y₀) (2 * (2 * k)) := by
  let f : ↥(N ⊔ zpowers y₀) →* DihedralGroup (2 * k) := p.comp (N ⊔ zpowers y₀).subtype
  have hsg : par k (sr (1 : ZMod (2 * k))) = 1 := by
    show pz k 1 = 1
    exact pz_one
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : p g.1 = 1 := hg
    rcases mem_sup_zpowers_iff hy2 hy g.2 with h1 | ⟨b, hb, hgb⟩
    · exact Subtype.ext (hinj _ h1 hg')
    · exfalso
      rw [hgb, map_mul, hpy] at hg'
      have hpb : p b = sr 1 := by
        have h3 : p b * sr 1 * sr 1 = 1 * sr 1 := by rw [hg']
        rw [mul_assoc, sr_mul_self_eq_one, mul_one, one_mul] at h3
        exact h3
      have := hpar b hb
      rw [hpb, hsg] at this
      exact one_ne_zero this
  have hf_surj : Function.Surjective f := by
    intro d
    rcases z2_cases (par k d) with h0 | h1
    · obtain ⟨a, ha, hpa⟩ := hsurj d h0
      exact ⟨⟨a, mem_sup_left ha⟩, hpa⟩
    · have hd' : par k (d * (sr (1 : ZMod (2 * k)))⁻¹) = 0 := by
        rw [par_mul, par_inv, h1, hsg]; decide
      obtain ⟨a, ha, hpa⟩ := hsurj _ hd'
      refine ⟨⟨a * y₀, Subgroup.mul_mem _ (mem_sup_left ha) (mem_sup_right (mem_zpowers y₀))⟩, ?_⟩
      show p (a * y₀) = d
      rw [map_mul, hpa, hpy, inv_sr, mul_assoc, sr_mul_self_eq_one, mul_one]
  have hk2 : 2 ≤ 2 * k := by have := NeZero.ne k; omega
  exact ⟨2 * k, rfl, hk2, ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩⟩

end Aux

section Std

variable [NeZero k]

@[expose] def Xs (k : ℕ) : Subgroup ↥(Wsub k) :=
  ((MonoidHom.snd (DihedralGroup (2 * k)) (DihedralGroup (2 * k))).comp (Wsub k).subtype).ker

omit [NeZero k] in
theorem mem_Xs {w : ↥(Wsub k)} : w ∈ Xs k ↔ w.1.2 = 1 := Iff.rfl

omit [NeZero k] in
theorem Xs_normal : (Xs k).Normal := MonoidHom.normal_ker _

@[expose] def y0 (k : ℕ) : ↥(Wsub k) := ⟨(sr 1, sr 1), rfl⟩

omit [NeZero k] in
theorem y0_mul_self : y0 k * y0 k = 1 :=
  Subtype.ext (Prod.ext (sr_mul_self_eq_one 1) (sr_mul_self_eq_one 1))

theorem Xs_le_normal {z : ↥(Wsub k)} {a : ZMod (2 * k)} (ha : pz k a = 0) (hz : z.1 = (sr a, 1))
    (N : Subgroup ↥(Wsub k)) (hN : N.Normal) (hzN : z ∈ N) : Xs k ≤ N := by
  have hrefl : ∀ c : ZMod (2 * k), pz k c = 0 → ∃ w : ↥(Wsub k), w.1 = (sr c, 1) ∧ w ∈ N := by
    intro c hc
    obtain ⟨a', ha'⟩ := (pz_eq_zero_iff a).mp ha
    obtain ⟨c', hc'⟩ := (pz_eq_zero_iff c).mp hc
    let g : ↥(Wsub k) := ⟨(r (a' - c'), r (a' - c')), rfl⟩
    refine ⟨g * z * g⁻¹, ?_, hN.conj_mem z hzN g⟩
    show (r (a' - c'), r (a' - c')) * z.1 * (r (a' - c'), r (a' - c'))⁻¹ = (sr c, 1)
    rw [hz]
    apply Prod.ext
    · show r (a' - c') * sr a * (r (a' - c'))⁻¹ = sr c
      rw [inv_r, r_mul_sr, sr_mul_r]
      congr 1
      rw [ha', hc']
      ring
    · show r (a' - c') * 1 * (r (a' - c'))⁻¹ = 1
      group
  intro w hw
  have hw2 : w.1.2 = 1 := hw
  have hpar : par k w.1.1 = 0 := by
    have := mem_Wsub.mp w.2
    rw [this, hw2, par_one]
  rcases hwe : w.1.1 with c | c
  ·
    rw [hwe] at hpar
    have hc : pz k c = 0 := hpar
    obtain ⟨w₁, hw₁, hw₁N⟩ := hrefl 0 (map_zero _)
    obtain ⟨w₂, hw₂, hw₂N⟩ := hrefl c hc
    have : w = w₁ * w₂ := by
      apply Subtype.ext
      apply Prod.ext
      · show w.1.1 = w₁.1.1 * w₂.1.1
        rw [hwe, hw₁, hw₂]
        show r c = sr 0 * sr c
        rw [sr_mul_sr, sub_zero]
      · show w.1.2 = w₁.1.2 * w₂.1.2
        rw [hw2, hw₁, hw₂]
        show (1 : DihedralGroup (2 * k)) = 1 * 1
        rw [mul_one]
    rw [this]
    exact N.mul_mem hw₁N hw₂N
  · rw [hwe] at hpar
    have hc : pz k c = 0 := hpar
    obtain ⟨w₁, hw₁, hw₁N⟩ := hrefl c hc
    have : w = w₁ := by
      apply Subtype.ext
      apply Prod.ext
      · show w.1.1 = w₁.1.1
        rw [hwe, hw₁]
      · show w.1.2 = w₁.1.2
        rw [hw2, hw₁]
    rw [this]
    exact hw₁N

theorem Xs_centralizes {z : ↥(Wsub k)} {a : ZMod (2 * k)} (ha : pz k a = 0) (hz : z.1 = (sr a, 1))
    {T₁ : Subgroup ↥(Wsub k)} (hn : T₁.Normal) (hzT : ∀ g ∈ T₁, z * g = g * z) :
    ∀ x ∈ Xs k, ∀ g ∈ T₁, x * g = g * x := by
  have := hn
  have hzc : z ∈ Subgroup.centralizer (T₁ : Set ↥(Wsub k)) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact (hzT g hg).symm
  have hle := Xs_le_normal ha hz (Subgroup.centralizer (T₁ : Set ↥(Wsub k))) inferInstance hzc
  intro x hx g hg
  exact (mem_centralizer_iff.mp (hle hx)) g hg |>.symm

end Std

section Std2

variable [NeZero k]

@[expose] def exW (b : DihedralGroup (2 * k)) (hb : par k b = 0) : ↥(Wsub k) :=
  ⟨(b, 1), by show par k b = par k 1; rw [par_one]; exact hb⟩

omit [NeZero k] in
theorem exW_mem (b : DihedralGroup (2 * k)) (hb : par k b = 0) : exW b hb ∈ Xs k := rfl

omit [NeZero k] in
theorem par_sr_zero : par k (sr (0 : ZMod (2 * k))) = 0 := map_zero _

omit [NeZero k] in
theorem par_r_two : par k (r (2 : ZMod (2 * k))) = 0 := by
  show pz k 2 = 0
  have h2 : ((2 : ℕ) : ZMod (2 * k)) = 2 := by norm_num
  rw [← h2, pz_natCast]
  decide

theorem T1_first {z t : ↥(Wsub k)} {a : ZMod (2 * k)} (hk : 3 ≤ k) (ha : pz k a = 0)
    (hz : z.1 = (sr a, 1)) {T₁ : Subgroup ↥(Wsub k)} (h : Cfg ↥(Wsub k) (2 * k) T₁ z t) :
    ∀ g ∈ T₁, g.1.1 = 1 ∨ g.1.1 = cc k := by
  intro g hg
  have hc := Xs_centralizes ha hz h.normal h.hzT₁
  have c1 := hc _ (exW_mem (sr 0) par_sr_zero) g hg
  have c2 := hc _ (exW_mem (r 2) par_r_two) g hg
  have e1 : sr 0 * g.1.1 = g.1.1 * sr 0 := congrArg (fun w : ↥(Wsub k) => w.1.1) c1
  have e2 : r 2 * g.1.1 = g.1.1 * r 2 := congrArg (fun w : ↥(Wsub k) => w.1.1) c2
  exact Dcent_B hk _ e1 e2

theorem cc1_not_mem {z t : ↥(Wsub k)} {a : ZMod (2 * k)} (hk4 : 4 ∣ k) (hk : 3 ≤ k)
    (ha : pz k a = 0) (hz : z.1 = (sr a, 1)) {T₁ : Subgroup ↥(Wsub k)}
    (h : Cfg ↥(Wsub k) (2 * k) T₁ z t) (hpc : par k (cc k) = 0) :
    exW (cc k) hpc ∉ T₁ := by
  intro hmem
  have hY := T1_first hk ha hz h
  obtain ⟨k', hk', -, ⟨φ⟩⟩ := h.dih
  have hk'k : k' = k := by omega
  obtain ⟨j, hj⟩ := hk4
  have hk2 : 2 ≤ 2 * j := by omega
  have hkj : k' = 2 * (2 * j) := by omega
  have : NeZero (2 * j) := ⟨by omega⟩
  let u : ↥T₁ := ⟨exW (cc k) hpc, hmem⟩
  have hu1 : u ≠ 1 := by
    intro hu
    have : (exW (cc k) hpc) = 1 := congrArg Subtype.val hu
    have h2 := congrArg (fun w : ↥(Wsub k) => w.1.1) this
    exact cc_ne_one h2
  have huc : ∀ g : ↥T₁, g * u = u * g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact cc_central _
    · show g.1.1.2 * 1 = 1 * g.1.1.2
      rw [mul_one, one_mul]
  obtain ⟨g, hg⟩ := central_is_square hkj (by omega) (dvd_mul_right 2 j) φ hu1 huc
  have h1 := congrArg (fun w : ↥T₁ => w.1.1.1) hg
  have h2 : g.1.1.1 * g.1.1.1 = cc k := h1
  rcases T1_first hk ha hz h g.1 g.2 with h3 | h3
  · rw [h3, mul_one] at h2
    exact cc_ne_one h2.symm
  · rw [h3, cc_mul_cc] at h2
    exact cc_ne_one h2.symm

end Std2

section Std3

variable [NeZero k]

structure StdCfg (k : ℕ) (T₁ : Subgroup ↥(Wsub k)) (z t : ↥(Wsub k)) (a : ZMod (2 * k)) : Prop where
  cfg : Cfg ↥(Wsub k) (2 * k) T₁ z t
  ha : pz k a = 0
  hz : z.1 = (sr a, 1)
  hk4 : 4 ∣ k
  hk : 3 ≤ k

variable {T₁ : Subgroup ↥(Wsub k)} {z t : ↥(Wsub k)} {a : ZMod (2 * k)}

omit [NeZero k] in
theorem StdCfg.hke (S : StdCfg k T₁ z t a) : 2 ∣ k := dvd_trans (by norm_num) S.hk4

omit [NeZero k] in
theorem StdCfg.hpc (S : StdCfg k T₁ z t a) : par k (cc k) = 0 := par_cc S.hke

theorem T1_inj (S : StdCfg k T₁ z t a) : ∀ g ∈ T₁, g.1.2 = 1 → g = 1 := by
  intro g hg h2
  rcases T1_first S.hk S.ha S.hz S.cfg g hg with h1 | h1
  · exact Subtype.ext (Prod.ext h1 h2)
  · exfalso
    apply cc1_not_mem S.hk4 S.hk S.ha S.hz S.cfg S.hpc
    have : g = exW (cc k) S.hpc := Subtype.ext (Prod.ext h1 h2)
    rw [← this]
    exact hg

theorem T1_par (S : StdCfg k T₁ z t a) : ∀ g ∈ T₁, par k g.1.2 = 0 := by
  intro g hg
  rw [← mem_Wsub.mp g.2]
  rcases T1_first S.hk S.ha S.hz S.cfg g hg with h1 | h1
  · rw [h1, par_one]
  · rw [h1]; exact S.hpc

theorem T1_surj (S : StdCfg k T₁ z t a) : ∀ b, par k b = 0 → ∃ g ∈ T₁, g.1.2 = b := by
  have hk2 : 2 ≤ k := by have := S.hk; omega
  let ψ : ↥T₁ → ↥(Bsub k) := fun g => ⟨g.1.1.2, T1_par S g.1 g.2⟩
  have hinj : Function.Injective ψ := by
    intro g g' hgg'
    have h2 : g.1.1.2 = g'.1.1.2 := congrArg Subtype.val hgg'
    have h3 : (g'⁻¹ * g : ↥T₁) = 1 := by
      apply Subtype.ext
      apply T1_inj S _ (g'⁻¹ * g).2
      show g'.1.1.2⁻¹ * g.1.1.2 = 1
      rw [h2]; group
    exact (inv_mul_eq_one.mp h3).symm
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le (by
    rw [card_Bsub hk2, card_of_isDihedralOrder S.cfg.dih])
  intro b hb
  obtain ⟨g, hg⟩ := hbij.2 ⟨b, hb⟩
  exact ⟨g.1, g.2, congrArg Subtype.val hg⟩

theorem Xs_dihedral (hk2 : 2 ≤ k) : IsDihedralOrder ↥(Xs k) (2 * k) := by
  obtain ⟨e⟩ := Bsub_equiv hk2
  let f : ↥(Xs k) →* ↥(Bsub k) :=
    MonoidHom.codRestrict ((MonoidHom.fst (DihedralGroup (2 * k)) (DihedralGroup (2 * k))).comp
      ((Wsub k).subtype.comp (Xs k).subtype)) (Bsub k) (fun g => by
        show par k g.1.1.1 = 0
        rw [mem_Wsub.mp g.1.2, mem_Xs.mp g.2, par_one])
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro g hg
      have h1 : g.1.1.1 = 1 := congrArg Subtype.val hg
      exact Subtype.ext (Subtype.ext (Prod.ext h1 (mem_Xs.mp g.2)))
    · intro b
      exact ⟨⟨exW b.1 b.2, exW_mem b.1 b.2⟩, Subtype.ext rfl⟩
  exact ⟨k, rfl, hk2, ⟨(MulEquiv.ofBijective f hbij).trans e⟩⟩

theorem one_cc_mem (S : StdCfg k T₁ z t a) :
    (⟨(1, cc k), by show par k 1 = par k (cc k); rw [par_one, S.hpc]⟩ : ↥(Wsub k)) ∈ T₁ := by
  obtain ⟨j, hj⟩ := S.hk4
  have hpj : par k (r ((2 * j : ℕ) : ZMod (2 * k))) = 0 := by
    show pz k ((2 * j : ℕ) : ZMod (2 * k)) = 0
    rw [pz_natCast]
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this]; simp
  obtain ⟨g, hg, hg2⟩ := T1_surj S _ hpj
  have hg1 := T1_first S.hk S.ha S.hz S.cfg g hg
  have hsq : g * g = (⟨(1, cc k), by show par k 1 = par k (cc k); rw [par_one, S.hpc]⟩ : ↥(Wsub k)) := by
    apply Subtype.ext
    apply Prod.ext
    · show g.1.1 * g.1.1 = 1
      rcases hg1 with h | h
      · rw [h, mul_one]
      · rw [h, cc_mul_cc]
    · show g.1.2 * g.1.2 = cc k
      rw [hg2, r_mul_r]
      show r _ = r _
      congr 1
      rw [← Nat.cast_add]
      have : (2 * j + 2 * j : ℕ) = k := by omega
      rw [this]
  rw [← hsq]
  exact T₁.mul_mem hg hg

end Std3

section Std4

variable [NeZero k] {T₁ : Subgroup ↥(Wsub k)} {z t : ↥(Wsub k)} {a : ZMod (2 * k)}

theorem std_concl (S : StdCfg k T₁ z t a) : Concl ↥(Wsub k) (2 * k) T₁ z := by
  have hk2 : 2 ≤ k := by have := S.hk; omega
  have hsg : par k (sr (1 : ZMod (2 * k))) = 1 := by
    show pz k 1 = 1
    exact pz_one
  have hy2 := y0_mul_self (k := k)
  have hyN : ∀ N : Subgroup ↥(Wsub k), N.Normal → ∀ g ∈ N, y0 k * g * (y0 k)⁻¹ ∈ N :=
    fun N hN g hg => hN.conj_mem g hg (y0 k)
  refine ⟨Xs k, y0 k, Xs_normal, ?_, ?_, Xs_dihedral hk2, ?_, ?_, ?_, hy2, ?_, ?_, ?_⟩
  · show z.1.2 = 1
    rw [S.hz]
  · exact fun N hN hzN => Xs_le_normal S.ha S.hz N hN hzN
  · exact Xs_centralizes S.ha S.hz S.cfg.normal S.cfg.hzT₁
  · rw [eq_bot_iff]
    rintro w ⟨hwX, hwT⟩
    exact Subgroup.mem_bot.mpr (T1_inj S w hwT (mem_Xs.mp hwX))
  ·
    intro c hc
    have hc2 : ∀ b, par k b = 0 → c.1.2 * b = b * c.1.2 := by
      intro b hb
      obtain ⟨g, hg, hg2⟩ := T1_surj S b hb
      have e : c.1.2 * g.1.2 = g.1.2 * c.1.2 :=
        congrArg (fun w : ↥(Wsub k) => w.1.2) (hc g hg)
      rw [hg2] at e
      exact e
    have hc2' : c.1.2 = 1 ∨ c.1.2 = cc k :=
      Dcent_B S.hk c.1.2 (hc2 (sr 0) par_sr_zero).symm (hc2 (r 2) par_r_two).symm
    have hpc1 : par k c.1.1 = 0 := by
      rw [mem_Wsub.mp c.2]
      rcases hc2' with h | h
      · rw [h, par_one]
      · rw [h]; exact S.hpc
    have hζ : (⟨(1, c.1.2), by
        show par k 1 = par k c.1.2
        rw [par_one, ← mem_Wsub.mp c.2]; exact hpc1.symm⟩ : ↥(Wsub k)) ∈ T₁ := by
      rcases hc2' with h | h
      · have : (⟨(1, c.1.2), by
            show par k 1 = par k c.1.2
            rw [par_one, ← mem_Wsub.mp c.2]; exact hpc1.symm⟩ : ↥(Wsub k)) = 1 := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact h
        rw [this]; exact T₁.one_mem
      · have : (⟨(1, c.1.2), by
            show par k 1 = par k c.1.2
            rw [par_one, ← mem_Wsub.mp c.2]; exact hpc1.symm⟩ : ↥(Wsub k)) =
            ⟨(1, cc k), by show par k 1 = par k (cc k); rw [par_one, S.hpc]⟩ := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · exact h
        rw [this]; exact one_cc_mem S
    refine ⟨exW c.1.1 hpc1, exW_mem _ _, ⟨(1, c.1.2), by
        show par k 1 = par k c.1.2
        rw [par_one, ← mem_Wsub.mp c.2]; exact hpc1.symm⟩, hζ, ?_, ?_⟩
    · intro g hg
      apply Subtype.ext
      apply Prod.ext
      · show 1 * g.1.1 = g.1.1 * 1
        rw [one_mul, mul_one]
      · show c.1.2 * g.1.2 = g.1.2 * c.1.2
        rcases hc2' with h | h
        · rw [h, one_mul, mul_one]
        · rw [h]; exact (cc_central g.1.2).symm
    · apply Subtype.ext
      apply Prod.ext
      · show c.1.1 = c.1.1 * 1
        rw [mul_one]
      · show c.1.2 = 1 * c.1.2
        rw [one_mul]
  ·
    rw [eq_top_iff]
    intro w _
    have key : ∀ w : ↥(Wsub k), par k w.1.1 = 0 → w ∈ Xs k ⊔ T₁ := by
      intro w hw
      have hw2 : par k w.1.2 = 0 := by rw [← mem_Wsub.mp w.2]; exact hw
      obtain ⟨g, hg, hg2⟩ := T1_surj S w.1.2 hw2
      have h1 : w * g⁻¹ ∈ Xs k := by
        show w.1.2 * g.1.2⁻¹ = 1
        rw [hg2]; group
      have hw' : w = (w * g⁻¹) * g := by group
      rw [hw']
      exact Subgroup.mul_mem_sup h1 hg
    rcases z2_cases (par k w.1.1) with h0 | h1
    · exact Subgroup.mem_sup_left (key w h0)
    · have h2 : par k (w * y0 k).1.1 = 0 := by
        show par k (w.1.1 * sr 1) = 0
        rw [par_mul, h1, hsg]; decide
      have h3 := key _ h2
      have hw : w = (w * y0 k) * y0 k := by rw [mul_assoc, hy2, mul_one]
      rw [hw]
      exact Subgroup.mul_mem_sup h3 (Subgroup.mem_zpowers _)
  ·
    refine dihedral_of_proj (Xs k) (y0 k) hy2 (hyN _ Xs_normal)
      ((MonoidHom.fst (DihedralGroup (2 * k)) (DihedralGroup (2 * k))).comp (Wsub k).subtype)
      rfl ?_ ?_ ?_
    · intro g hg h1
      have h1' : g.1.1 = 1 := h1
      exact Subtype.ext (Prod.ext h1' (mem_Xs.mp hg))
    · intro g hg
      show par k g.1.1 = 0
      rw [mem_Wsub.mp g.2, mem_Xs.mp hg, par_one]
    · intro b hb
      exact ⟨exW b hb, exW_mem b hb, rfl⟩
  ·
    refine dihedral_of_proj T₁ (y0 k) hy2 (hyN _ S.cfg.normal)
      ((MonoidHom.snd (DihedralGroup (2 * k)) (DihedralGroup (2 * k))).comp (Wsub k).subtype)
      rfl ?_ ?_ ?_
    · intro g hg h1
      exact T1_inj S g hg h1
    · intro g hg
      exact T1_par S g hg
    · intro b hb
      obtain ⟨g, hg, hg2⟩ := T1_surj S b hb
      exact ⟨g, hg, hg2⟩

end Std4

section Model4

variable [NeZero k]

theorem model_concl (hk4 : 4 ∣ k) {T₁ : Subgroup ↥(Wsub k)} {z t : ↥(Wsub k)}
    (h : Cfg ↥(Wsub k) (2 * k) T₁ z t) : Concl ↥(Wsub k) (2 * k) T₁ z := by
  have hke : 2 ∣ k := dvd_trans (by norm_num) hk4
  have hk3 : 3 ≤ k := by
    obtain ⟨j, hj⟩ := hk4
    have := NeZero.ne k
    omega
  obtain ⟨a, ε, ha, hε, hz⟩ := classify_z hke hk3 h
  rcases hz with hz | hz
  · rcases hε with rfl | rfl
    · exact std_concl ⟨h, ha, hz, hk4, hk3⟩
    · have h' := h.map (twistW hke)
      have hz' : ((twistW hke) z).1 = (sr a, 1) := by
        rw [twistW_val, hz]
        show (sr a, cc k * cc k) = (sr a, 1)
        rw [cc_mul_cc]
      exact Concl.of_map (twistW hke) (std_concl ⟨h', ha, hz', hk4, hk3⟩)
  · rcases hε with rfl | rfl
    · have h' := h.map (swapW k)
      have hz' : ((swapW k) z).1 = (sr a, 1) := by
        rw [swapW_val, hz]
      exact Concl.of_map (swapW k) (std_concl ⟨h', ha, hz', hk4, hk3⟩)
    · have h' := h.map ((swapW k).trans (twistW hke))
      have hz' : (((swapW k).trans (twistW hke)) z).1 = (sr a, 1) := by
        rw [MulEquiv.trans_apply, twistW_val, swapW_val, hz]
        show (sr a, cc k * cc k) = (sr a, 1)
        rw [cc_mul_cc]
      exact Concl.of_map ((swapW k).trans (twistW hke)) (std_concl ⟨h', ha, hz', hk4, hk3⟩)

end Model4

section N3

instance instDecMemWsub (k : ℕ) [NeZero k] : DecidablePred (· ∈ Wsub k) :=
  fun p => inferInstanceAs (Decidable (par k p.1 = par k p.2))

abbrev W2 : Type := ↥(Wsub 2)

@[expose] def nu2 (w : W2) : W2 := y0 2 * w * y0 2

@[expose] def Kl (a b : W2) : List W2 := [1, a, b, a * b]

@[expose] def Xl (z : W2) : List W2 := [1, z, nu2 z, z * nu2 z]

instance decMemKl (x a b : W2) : Decidable (x ∈ Kl a b) := by unfold Kl; infer_instance

instance decMemXl (x z : W2) : Decidable (x ∈ Xl z) := by unfold Xl; infer_instance

abbrev Tlist : List W2 :=
  [⟨(cc 2, 1), by decide⟩, ⟨(1, cc 2), by decide⟩, ⟨(cc 2, cc 2), by decide⟩]

@[expose] def Ssub2 : Subgroup W2 where
  carrier := {w | par 2 w.1.1 = 0}
  mul_mem' := by
    intro x y hx hy
    change par 2 (x * y).1.1 = 0
    change par 2 x.1.1 = 0 at hx
    change par 2 y.1.1 = 0 at hy
    show par 2 (x.1.1 * y.1.1) = 0
    rw [par_mul, hx, hy]; rfl
  one_mem' := par_one
  inv_mem' := by
    intro x hx
    change par 2 (x⁻¹).1.1 = 0
    change par 2 x.1.1 = 0 at hx
    show par 2 (x.1.1)⁻¹ = 0
    rw [par_inv, hx]

instance instDecMemSsub2 : DecidablePred (· ∈ Ssub2) :=
  fun w => inferInstanceAs (Decidable (par 2 w.1.1 = 0))

theorem dS_comm : ∀ w w' : W2, par 2 w.1.1 = 0 → par 2 w'.1.1 = 0 → w * w' = w' * w := by
  decide

theorem dS_sq : ∀ w : W2, par 2 w.1.1 = 0 → w * w = 1 := by
  decide

theorem dS_card : Nat.card ↥Ssub2 = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

@[expose] def HCard (z : W2) : Prop := (Finset.univ.filter (fun w : W2 => w * z = z * w)).card = 16
instance decHCard (z : W2) : Decidable (HCard z) := by unfold HCard; infer_instance

@[expose] def CZ1 (z : W2) : Prop := par 2 z.1.1 = 0 ∧ nu2 z ≠ z
instance decCZ1 (z : W2) : Decidable (CZ1 z) := by unfold CZ1; infer_instance

@[expose] def CZ2 (z : W2) : Prop :=
  (∀ x ∈ Xl z, ∀ x' ∈ Xl z, x * x' ∈ Xl z) ∧ (∀ x ∈ Xl z, x * x = 1)
instance decCZ2 (z : W2) : Decidable (CZ2 z) := by unfold CZ2; infer_instance

@[expose] def CZ3 (z : W2) : Prop := ∀ w : W2, ∀ x ∈ Xl z, w * x * w⁻¹ ∈ Xl z
instance decCZ3 (z : W2) : Decidable (CZ3 z) := by unfold CZ3; infer_instance

@[expose] def CZ4 (z : W2) : Prop := ∀ w : W2, w * z = z * w → par 2 w.1.1 = 0
instance decCZ4 (z : W2) : Decidable (CZ4 z) := by unfold CZ4; infer_instance

@[expose] def QZ (z : W2) : Prop := z * z = 1 → HCard z → CZ1 z ∧ CZ2 z ∧ CZ3 z ∧ CZ4 z
instance decQZ (z : W2) : Decidable (QZ z) := by unfold QZ; infer_instance

theorem dZ : ∀ z : W2, QZ z := by decide

@[expose] def CKey1 (z a b : W2) : Prop := ∀ x ∈ Xl z, x ∈ Kl a b → x = 1
instance decCKey1 (z a b : W2) : Decidable (CKey1 z a b) := by unfold CKey1; infer_instance

@[expose] def CKey2 (a b : W2) : Prop :=
  ∃ τ ∈ [a, b, a * b], nu2 τ ≠ τ ∧ ∀ g ∈ [a, b, a * b], g = τ ∨ g = nu2 τ ∨ g = τ * nu2 τ
instance decCKey2 (a b : W2) : Decidable (CKey2 a b) := by unfold CKey2; infer_instance

@[expose] def CKey (z a b : W2) : Prop := CKey1 z a b ∧ CKey2 a b
instance decCKey (z a b : W2) : Decidable (CKey z a b) := by unfold CKey; infer_instance

@[expose] def PB (z t a b : W2) : Prop :=
  par 2 b.1.1 = 0 ∧ b ≠ 1 ∧ a ≠ b ∧ nu2 a ∈ Kl a b ∧ nu2 b ∈ Kl a b ∧
    z ∉ Kl a b ∧ t ∉ Kl a b ∧ z * t ∉ Kl a b
instance decPB (z t a b : W2) : Decidable (PB z t a b) := by unfold PB; infer_instance

@[expose] def QKey (z : W2) : Prop := z * z = 1 → HCard z → ∀ t ∈ Tlist, z ≠ t →
    ∀ a : W2, par 2 a.1.1 = 0 → a ≠ 1 → ∀ b : W2, PB z t a b → CKey z a b
instance decQKey (z : W2) : Decidable (QKey z) := by unfold QKey; infer_instance

theorem dKey : ∀ z : W2, QKey z := by decide

theorem dS_nu : ∀ w : W2, par 2 w.1.1 = 0 → par 2 (nu2 w).1.1 = 0 := by decide

theorem y0_not_mem_S : y0 2 ∉ Ssub2 := by
  intro h
  have h1 : par 2 (y0 2).1.1 = 0 := h
  have h2 : par 2 (sr (1 : ZMod (2 * 2))) = 1 := by
    show pz 2 1 = 1
    exact pz_one
  have h3 : par 2 (y0 2).1.1 = 1 := h2
  rw [h3] at h1
  exact one_ne_zero h1

theorem y0_inv : (y0 2)⁻¹ = y0 2 := inv_eq_of_mul_eq_one_right y0_mul_self

theorem nu2_def (w : W2) : y0 2 * w * (y0 2)⁻¹ = nu2 w := by
  rw [y0_inv]; rfl

theorem dS_mul_y : ∀ w : W2, par 2 w.1.1 = 1 → par 2 (w * y0 2).1.1 = 0 := by decide

theorem nu2_nu2 (w : W2) : nu2 (nu2 w) = w := by
  show y0 2 * (y0 2 * w * y0 2) * y0 2 = w
  have h := y0_mul_self (k := 2)
  calc y0 2 * (y0 2 * w * y0 2) * y0 2 = (y0 2 * y0 2) * w * (y0 2 * y0 2) := by group
    _ = w := by rw [h]; group

theorem nu2_one : nu2 (1 : W2) = 1 := by
  show y0 2 * 1 * y0 2 = 1
  rw [mul_one]; exact y0_mul_self

theorem klein_four (N : Subgroup W2) (u v : W2) (hNS : N ≤ Ssub2) (hu : u ∈ N) (hv : v ∈ N)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hN : ∀ g ∈ N, g = 1 ∨ g = u ∨ g = v ∨ g = u * v) :
    IsDihedralOrder ↥N 4 := by
  have huS : par 2 u.1.1 = 0 := hNS hu
  have hvS : par 2 v.1.1 = 0 := hNS hv
  have huu : u * u = 1 := dS_sq u huS
  have hvv : v * v = 1 := dS_sq v hvS
  have hcomm : v * u = u * v := dS_comm v u hvS huS
  have h1 : v ^ 2 = 1 := by rw [pow_two]; exact hvv
  have h2 : v * u * v⁻¹ = u⁻¹ := by
    rw [hcomm, inv_eq_of_mul_eq_one_right hvv, inv_eq_of_mul_eq_one_right huu]
    calc u * v * v = u * (v * v) := by rw [mul_assoc]
      _ = u := by rw [hvv, mul_one]
  have h3 : v ∉ zpowers u := by
    intro h
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h
    rcases zpow_invol huu i with h4 | h4
    · rw [h4] at hi; exact hv1 hi.symm
    · rw [h4] at hi; exact huv hi
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup h1 h2 h3
  have hcl : Subgroup.closure ({u, v} : Set W2) = N := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact hu
      · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hv
    · intro g hg
      rcases hN g hg with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  rw [hord, hcl] at e
  exact ⟨2, rfl, le_refl 2, ⟨e⟩⟩

theorem klein_dihedral (N : Subgroup W2) (τ : W2) (hτN : τ ∈ N) (hNS : N ≤ Ssub2)
    (hτ : nu2 τ ≠ τ) (hνN : nu2 τ ∈ N)
    (hN : ∀ g ∈ N, g = 1 ∨ g = τ ∨ g = nu2 τ ∨ g = τ * nu2 τ) :
    IsDihedralOrder ↥(N ⊔ zpowers (y0 2)) (2 * (2 * 2)) := by
  have hyy : y0 2 * y0 2 = 1 := y0_mul_self
  have hyi : (y0 2)⁻¹ = y0 2 := y0_inv
  have hτS : τ ∈ Ssub2 := hNS hτN
  have hντS : nu2 τ ∈ Ssub2 := hNS hνN
  have hττ : τ * τ = 1 := dS_sq τ hτS
  have hcomm : τ * nu2 τ = nu2 τ * τ := dS_comm τ (nu2 τ) hτS hντS
  have hwS : τ * nu2 τ ∈ Ssub2 := mul_mem hτS hντS
  have hww : τ * nu2 τ * (τ * nu2 τ) = 1 := dS_sq _ hwS
  have hτ1 : τ ≠ 1 := fun h => hτ (by rw [h, nu2_one])
  have hρ2 : (τ * y0 2) * (τ * y0 2) = τ * nu2 τ := by
    show τ * y0 2 * (τ * y0 2) = τ * (y0 2 * τ * y0 2)
    group
  have hw1 : τ * nu2 τ ≠ 1 := by
    intro h
    apply hτ
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hττ]
  have hord : orderOf (τ * y0 2) = 4 := by
    have hnot : ¬ (τ * y0 2) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, hρ2]; exact hw1
    have hfin : (τ * y0 2) ^ 2 ^ (1 + 1) = 1 := by
      have h4 : (τ * y0 2) ^ 2 ^ (1 + 1) = (τ * y0 2) ^ 2 * (τ * y0 2) ^ 2 := by
        rw [← pow_add]
        norm_num
      rw [h4, pow_two, hρ2, hww]
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
    simpa using this
  have hrel : y0 2 * (τ * y0 2) * (y0 2)⁻¹ = (τ * y0 2)⁻¹ := by
    rw [mul_inv_rev, hyi, inv_eq_of_mul_eq_one_right hττ]
    calc y0 2 * (τ * y0 2) * y0 2 = y0 2 * τ * (y0 2 * y0 2) := by group
      _ = y0 2 * τ := by rw [hyy, mul_one]
  have hnotmem : y0 2 ∉ zpowers (τ * y0 2) := by
    intro h
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨j, hj, hjy⟩ := h
    interval_cases j
    · exact y0_not_mem_S (by rw [← hjy, pow_zero]; exact one_mem _)
    · rw [pow_one] at hjy
      apply hτ1
      calc τ = τ * y0 2 * (y0 2)⁻¹ := by group
        _ = y0 2 * (y0 2)⁻¹ := by rw [hjy]
        _ = 1 := by group
    · rw [pow_two, hρ2] at hjy
      exact y0_not_mem_S (hjy ▸ hwS)
    · have h3 : (τ * y0 2) ^ 3 = τ * nu2 τ * (τ * y0 2) := by
        rw [pow_succ, pow_two, hρ2]
      rw [h3] at hjy
      have h4 : nu2 τ * y0 2 = y0 2 := by
        calc nu2 τ * y0 2 = (τ * nu2 τ * τ) * y0 2 := by
              rw [show τ * nu2 τ * τ = nu2 τ from by
                calc τ * nu2 τ * τ = nu2 τ * τ * τ := by rw [hcomm]
                  _ = nu2 τ := by rw [mul_assoc, hττ, mul_one]]
          _ = τ * nu2 τ * (τ * y0 2) := mul_assoc _ _ _
          _ = y0 2 := hjy
      have h5 : nu2 τ = 1 := by
        calc nu2 τ = nu2 τ * y0 2 * (y0 2)⁻¹ := by group
          _ = y0 2 * (y0 2)⁻¹ := by rw [h4]
          _ = 1 := by group
      apply hτ1
      calc τ = nu2 (nu2 τ) := (nu2_nu2 τ).symm
        _ = 1 := by rw [h5, nu2_one]
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup
    (ρ := τ * y0 2) (σ := y0 2) (by rw [pow_two]; exact hyy) hrel hnotmem
  have hy : y0 2 ∈ Subgroup.closure ({τ * y0 2, y0 2} : Set W2) :=
    Subgroup.subset_closure (by simp)
  have hρ : τ * y0 2 ∈ Subgroup.closure ({τ * y0 2, y0 2} : Set W2) :=
    Subgroup.subset_closure (by simp)
  have hcl : Subgroup.closure ({τ * y0 2, y0 2} : Set W2) = N ⊔ zpowers (y0 2) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact mul_mem (mem_sup_left hτN) (mem_sup_right (mem_zpowers _))
      · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact mem_sup_right (mem_zpowers _)
    · apply sup_le
      · intro g hg
        have hτc : τ ∈ Subgroup.closure ({τ * y0 2, y0 2} : Set W2) := by
          have h1 : (τ * y0 2) * y0 2 ∈ Subgroup.closure ({τ * y0 2, y0 2} : Set W2) :=
            mul_mem hρ hy
          rwa [mul_assoc, hyy, mul_one] at h1
        have hντc : nu2 τ ∈ Subgroup.closure ({τ * y0 2, y0 2} : Set W2) := by
          have : nu2 τ = y0 2 * (τ * y0 2) := by
            show y0 2 * τ * y0 2 = y0 2 * (τ * y0 2)
            rw [mul_assoc]
          rw [this]; exact mul_mem hy hρ
        rcases hN g hg with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact hτc
        · exact hντc
        · exact mul_mem hτc hντc
      · rw [zpowers_le]; exact hy
  rw [hord, hcl] at e
  exact ⟨4, rfl, by norm_num, ⟨e⟩⟩

theorem klein_data {G : Type} [Group G] {T₁ : Subgroup G} (h : IsDihedralOrder ↥T₁ (2 * 2)) :
    ∃ a b : G, a ∈ T₁ ∧ b ∈ T₁ ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ ∀ g, g ∈ T₁ ↔ (g = 1 ∨ g = a ∨ g = b ∨ g = a * b) := by
  obtain ⟨k', hk', -, ⟨φ⟩⟩ := h
  have hk'2 : k' = 2 := by omega
  subst hk'2
  have hD : ∀ x : DihedralGroup 2, x = 1 ∨ x = r 1 ∨ x = sr 0 ∨ x = r 1 * sr 0 := by decide
  have h1 : r (1 : ZMod 2) * r 1 = 1 := by decide
  have h2 : sr (0 : ZMod 2) * sr 0 = 1 := by decide
  have h3 : r (1 : ZMod 2) * sr 0 = sr 0 * r 1 := by decide
  have h4 : r (1 : ZMod 2) ≠ 1 := by decide
  have h5 : sr (0 : ZMod 2) ≠ 1 := by decide
  have h6 : r (1 : ZMod 2) ≠ sr 0 := by decide
  let a₀ : ↥T₁ := φ.symm (r 1)
  let b₀ : ↥T₁ := φ.symm (sr 0)
  have hφa : φ a₀ = r 1 := MulEquiv.apply_symm_apply φ _
  have hφb : φ b₀ = sr 0 := MulEquiv.apply_symm_apply φ _
  refine ⟨a₀.1, b₀.1, a₀.2, b₀.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : a₀ * a₀ = 1 := φ.injective (by rw [map_mul, hφa, map_one]; exact h1)
    exact congrArg Subtype.val e
  · have e : b₀ * b₀ = 1 := φ.injective (by rw [map_mul, hφb, map_one]; exact h2)
    exact congrArg Subtype.val e
  · have e : a₀ * b₀ = b₀ * a₀ := φ.injective (by rw [map_mul, map_mul, hφa, hφb]; exact h3)
    exact congrArg Subtype.val e
  · intro e
    have e' : a₀ = 1 := Subtype.ext e
    apply h4
    rw [← hφa, e', map_one]
  · intro e
    have e' : b₀ = 1 := Subtype.ext e
    apply h5
    rw [← hφb, e', map_one]
  · intro e
    have e' : a₀ = b₀ := Subtype.ext e
    apply h6
    rw [← hφa, ← hφb, e']
  · intro g
    constructor
    · intro hg
      let g' : ↥T₁ := ⟨g, hg⟩
      rcases hD (φ g') with e | e | e | e
      · left
        have : g' = 1 := φ.injective (by rw [e, map_one])
        exact congrArg Subtype.val this
      · right; left
        have : g' = a₀ := φ.injective (by rw [e, hφa])
        exact congrArg Subtype.val this
      · right; right; left
        have : g' = b₀ := φ.injective (by rw [e, hφb])
        exact congrArg Subtype.val this
      · right; right; right
        have : g' = a₀ * b₀ := φ.injective (by rw [e, map_mul, hφa, hφb])
        exact congrArg Subtype.val this
    · rintro (rfl | rfl | rfl | rfl)
      · exact T₁.one_mem
      · exact a₀.2
      · exact b₀.2
      · exact T₁.mul_mem a₀.2 b₀.2

theorem card_filter_comm (z : W2) :
    (Finset.univ.filter (fun w : W2 => w * z = z * w)).card =
      Nat.card ↥(centralizer ({z} : Set W2)) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun w : W2 => w * z = z * w) (q := fun w : W2 => w ∈ centralizer ({z} : Set W2)) ?_)
  intro w
  exact (mem_centralizer_singleton_iff).symm

theorem dZl : ∀ t : W2, t ≠ 1 → (∀ w : W2, w * t = t * w) → t ∈ Tlist := by decide

@[expose] def Xs3 (z : W2) (hmul : ∀ x ∈ Xl z, ∀ x' ∈ Xl z, x * x' ∈ Xl z)
    (hsq : ∀ x ∈ Xl z, x * x = 1) : Subgroup W2 where
  carrier := {w | w ∈ Xl z}
  mul_mem' := fun {a b} ha hb => hmul a ha b hb
  one_mem' := by simp [Xl]
  inv_mem' := fun {x} hx => by
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    rw [this]; exact hx

theorem model_concl3 {T₁ : Subgroup W2} {z t : W2} (h : Cfg W2 (2 * 2) T₁ z t) :
    Concl W2 (2 * 2) T₁ z := by
  have := h.normal
  obtain ⟨a, b, haT, hbT, haa, hbb, hab, ha1, hb1, hab', hKl0⟩ := klein_data h.dih
  have hKl : ∀ g, g ∈ T₁ ↔ g ∈ Kl a b := fun g => by rw [hKl0]; simp [Kl]
  have hzz : z * z = 1 := h.zz
  have hHC : HCard z := by
    have h1 := h.card_C
    unfold HCard
    rw [card_filter_comm, h1]
  obtain ⟨⟨hz1, hz2⟩, ⟨hmul, hsq⟩, hnorm, hcent⟩ := dZ z hzz hHC
  have hTS : ∀ g ∈ T₁, par 2 g.1.1 = 0 := fun g hg => hcent g (h.hzT₁ g hg).symm
  have hT₁S : T₁ ≤ Ssub2 := fun g hg => hTS g hg
  have hy2 : y0 2 * y0 2 = 1 := y0_mul_self
  have htT : t ∈ Tlist := by
    apply dZl t
    · intro ht1
      have := h.ht
      rw [ht1, orderOf_one] at this
      omega
    · exact Subgroup.mem_center_iff.mp h.htc
  have hνT : ∀ g ∈ T₁, nu2 g ∈ T₁ := by
    intro g hg
    have := h.normal.conj_mem g hg (y0 2)
    rwa [nu2_def] at this
  have hzK : z ∉ Kl a b := by
    intro hz
    have h1 : z ∈ T₁ := (hKl z).mpr hz
    have h2 : z ∈ (zpowers z ⊔ zpowers t) ⊓ T₁ :=
      ⟨mem_sup_left (mem_zpowers z), h1⟩
    rw [h.hinfU] at h2
    exact h.z_ne_one (Subgroup.mem_bot.mp h2)
  have htK : t ∉ Kl a b := by
    intro ht
    have h1 : t ∈ T₁ := (hKl t).mpr ht
    have h2 : t ∈ (zpowers z ⊔ zpowers t) ⊓ T₁ :=
      ⟨mem_sup_right (mem_zpowers t), h1⟩
    rw [h.hinfU] at h2
    have h3 : t = 1 := Subgroup.mem_bot.mp h2
    have := h.ht
    rw [h3, orderOf_one] at this
    omega
  have hztK : z * t ∉ Kl a b := by
    intro hzt
    have h1 : z * t ∈ T₁ := (hKl _).mpr hzt
    have h2 : z * t ∈ (zpowers z ⊔ zpowers t) ⊓ T₁ :=
      ⟨mul_mem (mem_sup_left (mem_zpowers z)) (mem_sup_right (mem_zpowers t)), h1⟩
    rw [h.hinfU] at h2
    have h3 : z * t = 1 := Subgroup.mem_bot.mp h2
    apply h.hzt
    have h4 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [h4, inv_eq_of_mul_eq_one_right h.tt]
  obtain ⟨hKey1, hKey2⟩ := dKey z hzz hHC t htT h.hzt a (hTS a haT) ha1 b
    ⟨hTS b hbT, hb1, hab', (hKl _).mp (hνT a haT), (hKl _).mp (hνT b hbT), hzK, htK, hztK⟩
  let X : Subgroup W2 := Xs3 z hmul hsq
  have hmemX : ∀ g, g ∈ X ↔ g ∈ Xl z := fun g => Iff.rfl
  have hXn : X.Normal := ⟨fun n hn g => hnorm g n hn⟩
  have hzX : z ∈ X := by simp [hmemX, Xl]
  have hνzS : nu2 z ∈ Ssub2 := dS_nu z hz1
  have hXS : ∀ g ∈ X, g ∈ Ssub2 := by
    intro g hg
    rw [hmemX] at hg
    simp only [Xl, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz1
    · exact hνzS
    · exact mul_mem hz1 hνzS
  have hz'1 : nu2 z ≠ 1 := by
    intro e
    apply h.z_ne_one
    calc z = nu2 (nu2 z) := (nu2_nu2 z).symm
      _ = 1 := by rw [e, nu2_one]
  have hXdih : IsDihedralOrder ↥X (2 * 2) := by
    refine klein_four X z (nu2 z) hXS hzX (by simp [hmemX, Xl]) h.z_ne_one hz'1 (Ne.symm hz2) ?_
    intro g hg
    rw [hmemX] at hg
    simpa [Xl] using hg
  have hXT : ∀ x ∈ X, ∀ τ ∈ T₁, x * τ = τ * x := fun x hx τ hτ => dS_comm x τ (hXS x hx) (hTS τ hτ)
  have hXinf : X ⊓ T₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgX, hgT⟩
    exact Subgroup.mem_bot.mpr (hKey1 g ((hmemX g).mp hgX) ((hKl g).mp hgT))
  have hSeq : X ⊔ T₁ = Ssub2 := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (fun g hg => hXS g hg) hT₁S
    · rw [dS_card, CFSG.GH74.GLS.IVK.Proofs2.card_sup_eq_mul hXT hXinf,
        card_of_isDihedralOrder hXdih, card_of_isDihedralOrder h.dih]
  have hτT_of : ∀ τ ∈ [a, b, a * b], τ ∈ T₁ := by
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · exact haT
    · exact hbT
    · exact mul_mem haT hbT
  have hcentS : ∀ c : W2, (∀ g ∈ T₁, c * g = g * c) → c ∈ Ssub2 := by
    intro c hc
    by_contra hcS
    have hc1 : par 2 c.1.1 = 1 := by
      rcases z2_cases (par 2 c.1.1) with h0 | h1
      · exact absurd h0 hcS
      · exact h1
    have hs : par 2 (c * y0 2).1.1 = 0 := dS_mul_y c hc1
    obtain ⟨τ, hτmem, hτν, -⟩ := hKey2
    have hτT := hτT_of τ hτmem
    have hτS : par 2 τ.1.1 = 0 := hTS τ hτT
    have hss : (c * y0 2) * (c * y0 2) = 1 := dS_sq _ hs
    have hsτ : (c * y0 2) * τ = τ * (c * y0 2) := dS_comm _ τ hs hτS
    have hcτ := hc τ hτT
    have hcs : c = (c * y0 2) * y0 2 := by rw [mul_assoc, hy2, mul_one]
    have hyτ : y0 2 * τ = τ * y0 2 := by
      generalize c * y0 2 = s at hss hsτ hcs
      subst hcs
      calc y0 2 * τ = (s * s) * (y0 2 * τ) := by rw [hss, one_mul]
        _ = s * ((s * y0 2) * τ) := by group
        _ = s * (τ * (s * y0 2)) := by rw [hcτ]
        _ = (s * τ) * (s * y0 2) := by group
        _ = (τ * s) * (s * y0 2) := by rw [hsτ]
        _ = τ * ((s * s) * y0 2) := by group
        _ = τ * y0 2 := by rw [hss, one_mul]
    apply hτν
    show y0 2 * τ * y0 2 = τ
    rw [hyτ, mul_assoc, hy2, mul_one]
  have hcent' : ∀ c : W2, (∀ g ∈ T₁, c * g = g * c) →
      ∃ x ∈ X, ∃ ζ ∈ T₁, (∀ g ∈ T₁, ζ * g = g * ζ) ∧ c = x * ζ := by
    intro c hc
    have hcS := hcentS c hc
    rw [← hSeq] at hcS
    have := hXn
    obtain ⟨x, hx, ζ, hζ, hxζ⟩ := Subgroup.mem_sup_of_normal_left.mp hcS
    exact ⟨x, hx, ζ, hζ, fun g hg => dS_comm ζ g (hTS ζ hζ) (hTS g hg), hxζ.symm⟩
  have hgen : X ⊔ T₁ ⊔ zpowers (y0 2) = ⊤ := by
    rw [hSeq, eq_top_iff]
    intro w _
    rcases z2_cases (par 2 w.1.1) with h0 | h1
    · exact mem_sup_left h0
    · have h2 : w * y0 2 ∈ Ssub2 := dS_mul_y w h1
      have h3 : (w * y0 2) * y0 2 ∈ Ssub2 ⊔ zpowers (y0 2) :=
        mul_mem_sup h2 (mem_zpowers _)
      rwa [mul_assoc, hy2, mul_one] at h3
  have hdX : IsDihedralOrder ↥(X ⊔ zpowers (y0 2)) (2 * (2 * 2)) := by
    refine klein_dihedral X z hzX hXS hz2 (by simp [hmemX, Xl]) ?_
    intro g hg
    rw [hmemX] at hg
    simpa [Xl] using hg
  have hdT : IsDihedralOrder ↥(T₁ ⊔ zpowers (y0 2)) (2 * (2 * 2)) := by
    obtain ⟨τ, hτmem, hτν, hτall⟩ := hKey2
    have hτT := hτT_of τ hτmem
    refine klein_dihedral T₁ τ hτT hT₁S hτν (hνT τ hτT) ?_
    intro g hg
    rcases (hKl0 g).mp hg with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (hτall _ (by simp))
    · exact Or.inr (hτall _ (by simp))
    · exact Or.inr (hτall _ (by simp))
  have hmin : ∀ N : Subgroup W2, N.Normal → z ∈ N → X ≤ N := by
    intro N hN hzN g hg
    rw [hmemX] at hg
    have hνzN : nu2 z ∈ N := by
      have := hN.conj_mem z hzN (y0 2)
      rwa [nu2_def] at this
    simp only [Xl, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hzN
    · exact hνzN
    · exact mul_mem hzN hνzN
  exact ⟨X, y0 2, hXn, hzX, hmin, hXdih, hXT, hXinf, hcent', hy2, hgen, hdX, hdT⟩

end N3

section Core

variable [NeZero k]

theorem core_concl {T : Type} [Group T] (hk : k = 2 ∨ 4 ∣ k) (hke : 2 ∣ k)
    (B₁ B₂ : Subgroup T) (y : T)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hinf : B₁ ⊓ B₂ = ⊥)
    (hy2 : y * y = 1)
    (hy₁ : ∀ a ∈ B₁, y * a * y⁻¹ ∈ B₁) (hy₂ : ∀ a ∈ B₂, y * a * y⁻¹ ∈ B₂)
    (hT : B₁ ⊔ B₂ ⊔ zpowers y = ⊤)
    (hB₁ : IsDihedralOrder ↥B₁ (2 * k)) (hB₂ : IsDihedralOrder ↥B₂ (2 * k))
    (hB₁y : IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 * (2 * k)))
    (hB₂y : IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 * (2 * k)))
    {T₁ : Subgroup T} {z t : T} (h : Cfg T (2 * k) T₁ z t) : Concl T (2 * k) T₁ z := by
  obtain ⟨e⟩ := exists_equiv_Wsub hke B₁ B₂ y hcomm hinf hy2 hy₁ hy₂ hT hB₁ hB₂ hB₁y hB₂y
  have h' := h.map e
  refine Concl.of_map e ?_
  rcases hk with rfl | hk4
  · exact model_concl3 h'
  · exact model_concl hk4 h'

end Core

end Model

end CtW

open Subgroup CFSG.GH74.GLS.IVK in
theorem lemmaW {T : Type} [Group T] [Finite T] {n : ℕ} (hn : 3 ≤ n)
    (B₁ B₂ : Subgroup T) (y : T)
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hinf : B₁ ⊓ B₂ = ⊥)
    (hy2 : y * y = 1)
    (hy₁ : ∀ a ∈ B₁, y * a * y⁻¹ ∈ B₁) (hy₂ : ∀ a ∈ B₂, y * a * y⁻¹ ∈ B₂)
    (hT : B₁ ⊔ B₂ ⊔ zpowers y = ⊤)
    (hB₁ : IsDihedralOrder ↥B₁ (2 ^ (n - 1))) (hB₂ : IsDihedralOrder ↥B₂ (2 ^ (n - 1)))
    (hB₁y : IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ n))
    (hB₂y : IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ n))
    (T₁ : Subgroup T) (hT₁n : T₁.Normal) (hT₁ : IsDihedralOrder ↥T₁ (2 ^ (n - 1)))
    (z t : T) (hz : orderOf z = 2) (ht : orderOf t = 2) (htc : t ∈ center T) (hzt : z ≠ t)
    (hzT₁ : ∀ a ∈ T₁, z * a = a * z)
    (hinfU : (zpowers z ⊔ zpowers t) ⊓ T₁ = ⊥)
    (hC : centralizer ({z} : Set T) = (zpowers z ⊔ zpowers t) ⊔ T₁) :
    ∃ (X : Subgroup T) (y₀ : T), X.Normal ∧ z ∈ X ∧
      (∀ N : Subgroup T, N.Normal → z ∈ N → X ≤ N) ∧
      IsDihedralOrder ↥X (2 ^ (n - 1)) ∧
      (∀ a ∈ X, ∀ b ∈ T₁, a * b = b * a) ∧ X ⊓ T₁ = ⊥ ∧
      (∀ c : T, (∀ a ∈ T₁, c * a = a * c) →
        ∃ x ∈ X, ∃ ζ ∈ T₁, (∀ a ∈ T₁, ζ * a = a * ζ) ∧ c = x * ζ) ∧
      y₀ * y₀ = 1 ∧ X ⊔ T₁ ⊔ zpowers y₀ = ⊤ ∧
      IsDihedralOrder ↥(X ⊔ zpowers y₀) (2 ^ n) ∧ IsDihedralOrder ↥(T₁ ⊔ zpowers y₀) (2 ^ n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have e1 : 2 ^ (j + 3 - 1) = 2 * 2 ^ (j + 1) := by
    have : j + 3 - 1 = j + 2 := by omega
    rw [this]; ring
  have e2 : 2 ^ (j + 3) = 2 * (2 * 2 ^ (j + 1)) := by ring
  have : NeZero (2 ^ (j + 1)) := ⟨by positivity⟩
  have hke : 2 ∣ 2 ^ (j + 1) := dvd_pow_self 2 (by omega)
  have hcase : 2 ^ (j + 1) = 2 ∨ 4 ∣ 2 ^ (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · left; norm_num
    · right
      have := pow_dvd_pow 2 (show 2 ≤ j + 1 by omega)
      simpa using this
  rw [e1] at hB₁ hB₂ hT₁
  rw [e2] at hB₁y hB₂y
  have h : CtW.Cfg T (2 * 2 ^ (j + 1)) T₁ z t := ⟨hT₁n, hT₁, hz, ht, htc, hzt, hzT₁, hinfU, hC⟩
  obtain ⟨X, y₀, hXn, hzX, hmin, hXd, hcomm', hinf', hcent, hyy, hgen, hdX, hdT⟩ :=
    CtW.core_concl hcase hke B₁ B₂ y hcomm hinf hy2 hy₁ hy₂ hT hB₁ hB₂ hB₁y hB₂y h
  refine ⟨X, y₀, hXn, hzX, hmin, ?_, hcomm', hinf', hcent, hyy, hgen, ?_, ?_⟩
  · rw [e1]; exact hXd
  · rw [e2]; exact hdX
  · rw [e2]; exact hdT

end CFSG.GH74.GLS.SP.Local
