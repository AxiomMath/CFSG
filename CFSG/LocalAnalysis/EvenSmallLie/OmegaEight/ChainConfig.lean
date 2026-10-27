module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainStart

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Stage1

variable {G : Type*} [Group G]

theorem cm_eq_one_iff_commute {t x : G} : cm t x = 1 ↔ x * t = t * x := by
  simp only [cm]
  constructor
  · intro h
    have : x * t * x⁻¹ = t := by rw [← mul_inv_eq_one]; exact h
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [this]
  · intro h
    rw [h]
    group

theorem cm_mul_right_of_commute {t x h : G} (hh : h * t = t * h) : cm t (x * h) = cm t x := by
  simp only [cm]
  have : h * t * h⁻¹ = t := by rw [hh, mul_inv_cancel_right]
  calc x * h * t * (x * h)⁻¹ * t⁻¹ = x * (h * t * h⁻¹) * x⁻¹ * t⁻¹ := by group
    _ = x * t * x⁻¹ * t⁻¹ := by rw [this]

theorem cm_conj_conj (g t x : G) : cm (g * t * g⁻¹) (g * x * g⁻¹) = g * cm t x * g⁻¹ := by
  simp only [cm]
  group

theorem exists_mul_of_mem_sup_normalizer {N H : Subgroup G} (hLE : H ≤ normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, x = n * h := by
  have hx' : x ∈ ((N ⊔ H : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left N H hLE] at hx'
  obtain ⟨n, hn, h, hh, rfl⟩ := hx'
  exact ⟨n, hn, h, hh, rfl⟩

section CmGen

variable {t : G} {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
  (ht : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
include hA ht

omit hA in
theorem cm_mem_of {a : G} (ha : a ∈ A) : cm t a ∈ A := by
  have h := ht _ (inv_mem ha)
  have := mul_mem ha h
  simpa [cm, mul_assoc] using this

theorem cm_mul_of {x y : G} (hx : x ∈ A) (hy : y ∈ A) : cm t (x * y) = cm t x * cm t y := by
  have h1 := hA _ (cm_mem_of ht hy) _ (ht _ (inv_mem hx))
  simp only [cm] at *
  calc x * y * t * (x * y)⁻¹ * t⁻¹ = x * (y * t * y⁻¹ * t⁻¹) * (t * x⁻¹ * t⁻¹) := by group
    _ = x * (t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) := by rw [mul_assoc x, h1, ← mul_assoc]
    _ = x * t * x⁻¹ * t⁻¹ * (y * t * y⁻¹ * t⁻¹) := by group

theorem cm_mul_t {a b : G} (ha : a ∈ A) (hb : b ∈ A) : cm (b * t) a = cm t a := by
  have h1 := hA a ha b hb
  have h2 := hA b hb _ (cm_mem_of ht ha)
  simp only [cm] at *
  calc a * (b * t) * a⁻¹ * (b * t)⁻¹ = (a * b) * t * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = b * (a * t * a⁻¹ * t⁻¹) * b⁻¹ := by rw [h1]; group
    _ = a * t * a⁻¹ * t⁻¹ := by rw [h2, mul_inv_cancel_right]

@[expose] def cmHomOf : A →* G where
  toFun a := cm t a
  map_one' := by simp [cm]
  map_mul' x y := cm_mul_of hA ht x.2 y.2

end CmGen

@[expose] def TAct (t : G) (k : ℕ) (A : Subgroup G) : Prop :=
  (∀ a ∈ A, t * a * t⁻¹ = a⁻¹) ∨ (3 ≤ k ∧ ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ * a ^ 2 ^ (k - 1))

structure Config (t : G) (Q P : Subgroup G) (k : ℕ) (A : Subgroup G) : Prop where
  two_le : 2 ≤ k
  level : Level Q k A
  act : TAct t k A
  P_norm : ∀ x ∈ P, ∀ a ∈ A, x * a * x⁻¹ ∈ A
  normalizer_le : normalizer ((pw A 2 ⊔ zpowers t : Subgroup G) : Set G) ≤ A ⊔ (P ⊔ zpowers t)

@[expose] def Terminal (t : G) (P : Subgroup G) (k : ℕ) (A : Subgroup G) : Prop :=
  ((∀ a ∈ A, t * a * t⁻¹ = a⁻¹) ∧
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ A ⊔ (P ⊔ zpowers t)) ∨
  (3 ≤ k ∧ ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ * a ^ 2 ^ (k - 1))

namespace Config

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {k : ℕ} {A : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hC : Config t Q P k A)
include hS hC

omit hS in
theorem t_conj_mem {x : G} (hx : x ∈ A) : t * x * t⁻¹ ∈ A := by
  rcases hC.act with h | ⟨-, h⟩
  · rw [h x hx]; exact inv_mem hx
  · rw [h x hx]; exact mul_mem (inv_mem hx) (pow_mem hx _)

omit hS in
theorem k_pos : 1 ≤ k := le_trans (by norm_num) hC.two_le

theorem commute_iff {x : G} (hx : x ∈ A) : x * t = t * x ↔ x ∈ Q := by
  refine ⟨fun h => hC.level.mem_Q x hx ?_, fun h => hS.shape.commute_of_mem (hS.rad.Q_le_L h)⟩
  have h' : t * x * t⁻¹ = x := by rw [← h, mul_inv_cancel_right]
  rcases hC.act with h1 | ⟨hk, h1⟩
  · rw [h1 x hx] at h'
    nth_rewrite 1 [← h']
    exact inv_mul_cancel x
  · rw [h1 x hx] at h'
    have h2 : (x * x) ^ (2 ^ (k - 2)) = x * x := by
      have e : (x * x) ^ (2 ^ (k - 2)) = x ^ 2 ^ (k - 1) := by
        rw [← sq, ← pow_mul, ← pow_succ']
        congr 2
        omega
      rw [e]
      have := congrArg (x * ·) h'
      simpa [mul_assoc] using this
    have h3 : (x * x) ^ (2 ^ (k - 2) - 1) = 1 := by
      have hpos : 1 ≤ 2 ^ (k - 2) := Nat.one_le_two_pow
      have := h2
      rw [show 2 ^ (k - 2) = (2 ^ (k - 2) - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.1 this
    have h4 : (x * x) ^ 2 ^ k = 1 := by
      rw [← sq, ← pow_mul, ← pow_succ']
      rw [pow_succ, pow_mul, hC.level.pow_eq_one x hx, one_pow]
    have hco : Nat.Coprime (2 ^ (k - 2) - 1) (2 ^ k) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      have : 2 ≤ 2 ^ (k - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have he : Even (2 ^ (k - 2)) := Nat.even_pow.2 ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (by omega) he odd_one
    have h5 := (hco.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3)).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one h4)
    rwa [orderOf_eq_one_iff] at h5

theorem cm_eq_one_iff {x : G} (hx : x ∈ A) : cm t x = 1 ↔ x ∈ Q := by
  rw [cm_eq_one_iff_commute, hC.commute_iff hS hx]

omit hS in
theorem cm_mem_pw {x : G} (hx : x ∈ A) : cm t x ∈ pw A 2 := by
  rcases hC.act with h | ⟨hk, h⟩
  · rw [cm_eq_sq h hx, ← sq]
    exact pow_mem_pw hx 2
  · have e : cm t x = x * x * (x ^ 2 ^ (k - 1))⁻¹ := by
      have h' := h x⁻¹ (inv_mem hx)
      have hc : x ^ 2 ^ (k - 1) * x = x * x ^ 2 ^ (k - 1) := (pow_mul_comm' x _)
      simp only [cm]
      calc x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
        _ = x * (x⁻¹⁻¹ * x⁻¹ ^ 2 ^ (k - 1)) := by rw [h']
        _ = x * x * (x ^ 2 ^ (k - 1))⁻¹ := by rw [inv_inv, inv_pow, mul_assoc]
    rw [e]
    refine mul_mem (by rw [← sq]; exact pow_mem_pw hx 2) (inv_mem ?_)
    have : x ^ 2 ^ (k - 1) = (x ^ 2 ^ (k - 2)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]; congr 2; omega
    rw [this]
    exact pow_mem_pw (pow_mem hx _) 2

theorem exists_cm_eq [Finite G] {y : G} (hy : y ∈ pw A 2) : ∃ x ∈ A, cm t x = y := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  set f := cmHomOf hC.level.comm (fun x hx => hC.t_conj_mem hx)
  have hle : f.range ≤ pw A 2 := by
    rintro _ ⟨x, rfl⟩
    exact hC.cm_mem_pw x.2
  have hker : f.ker = Q.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hC.cm_eq_one_iff hS x.2
  have h := card_mul_index f.ker
  rw [index_ker, hker, hC.level.card_eq,
    Nat.card_congr (subgroupOfEquivOfLe hC.level.Q_le).toEquiv, hQ] at h
  have hc : Nat.card f.range = Nat.card (pw A 2) := by
    rw [hC.level.card_pw_two hQ hQ2 hC.k_pos]
    have e : 2 ^ (6 * k) = 64 * 2 ^ (6 * (k - 1)) := by
      rw [show 6 * k = 6 + 6 * (k - 1) by have := hC.k_pos; omega, pow_add]; norm_num
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 64) h
  have heq := eq_of_le_of_card_ge hle hc.ge
  rw [← heq] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, x.2, rfl⟩

omit hS in
theorem pw_conj_mem {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) {y : G} (hy : y ∈ pw A 2) :
    g * y * g⁻¹ ∈ pw A 2 := by
  obtain ⟨x, hx, rfl⟩ := (mem_pw hC.level.comm).1 hy
  rw [← conj_pow]
  exact pow_mem_pw (hg x hx) 2

omit hS in
theorem t_inv_pw {y : G} (hy : y ∈ pw A 2) : t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := (mem_pw hC.level.comm).1 hy
  rw [← conj_pow]
  rcases hC.act with h | ⟨hk, h⟩
  · rw [h x hx, inv_pow]
  · rw [h x hx, (Commute.inv_left ((Commute.refl x).pow_right _)).mul_pow, inv_pow, ← pow_mul,
      ← pow_succ, show k - 1 + 1 = k by have := hC.k_pos; omega, hC.level.pow_eq_one x hx,
      mul_one]

omit hC in
theorem mem_Q_of_mem_L {u : G} (hu : u ∈ L) (hc : ∀ q ∈ Q, u * q = q * u) : u ∈ Q := by
  have h : u ∈ centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) :=
    ⟨hS.shape.le_centralizer hu, mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩
  rw [hS.shape.centralizer_eq] at h
  obtain ⟨q, hq, rfl | rfl⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h
  · exact hq
  · exact absurd (by simpa using L.mul_mem (L.inv_mem (hS.rad.Q_le_L hq)) hu) hS.shape.not_mem

omit hC in
theorem commute_of_mem_TH {h : G} (hh : h ∈ U ⊔ zpowers t) : h * t = t * h := by
  obtain ⟨u, hu, rfl | rfl⟩ := (hS.shape.mem_sup_iff hS.rad.U_le_L).1 hh
  · exact hS.shape.commute_of_mem (hS.rad.U_le_L hu)
  · have hc := hS.shape.commute_of_mem (hS.rad.U_le_L hu)
    calc u * t * t = t * u * t := by rw [hc]
      _ = t * (u * t) := mul_assoc _ _ _

omit hS in
theorem t_mem_normalizer [Finite G] : t ∈ normalizer (A : Set G) :=
  mem_normalizer_of_conj_mem fun _ hx => hC.t_conj_mem hx

theorem TH_le_normalizer [Finite G] : U ⊔ zpowers t ≤ normalizer (A : Set G) :=
  sup_le (fun u hu => mem_normalizer_of_conj_mem (hC.P_norm u (hS.rad.U_le_P hu)))
    (zpowers_le.2 (hC.t_mem_normalizer))

omit hS in
theorem PT_le_normalizer [Finite G] : P ⊔ zpowers t ≤ normalizer (A : Set G) :=
  sup_le (fun u hu => mem_normalizer_of_conj_mem (hC.P_norm u hu))
    (zpowers_le.2 (hC.t_mem_normalizer))

omit hS in
theorem isPGroup_A : IsPGroup 2 A := fun x => ⟨k, Subtype.ext (hC.level.pow_eq_one x x.2)⟩

theorem isPGroup_T [Finite G] : IsPGroup 2 (A ⊔ (U ⊔ zpowers t) : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' hC.isPGroup_A
    (hS.shape.isPGroup_sup hS.rad.U_le_L hS.rad.U_pgroup) (hC.TH_le_normalizer hS)

theorem T_le_normalizer [Finite G] : A ⊔ (U ⊔ zpowers t) ≤ normalizer (A : Set G) :=
  sup_le le_normalizer (hC.TH_le_normalizer hS)

theorem mem_T [Finite G] {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t)) :
    ∃ b ∈ A, ∃ u ∈ U, x = b * u ∨ x = b * u * t := by
  obtain ⟨b, hb, h, hh, rfl⟩ := exists_mul_of_mem_sup_normalizer (hC.TH_le_normalizer hS) hx
  obtain ⟨u, hu, h1 | h1⟩ := (hS.shape.mem_sup_iff hS.rad.U_le_L).1 hh
  · exact ⟨b, hb, u, hu, Or.inl (by rw [h1])⟩
  · exact ⟨b, hb, u, hu, Or.inr (by rw [h1, mul_assoc])⟩

theorem cm_mem_pw_T [Finite G] {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t)) : cm t x ∈ pw A 2 := by
  obtain ⟨b, hb, h, hh, rfl⟩ := exists_mul_of_mem_sup_normalizer (hC.TH_le_normalizer hS) hx
  rw [cm_mul_right_of_commute (commute_of_mem_TH hS hh)]
  exact hC.cm_mem_pw hb

theorem mem_Q_of_trivial [Finite G] {u : G} (hu : u ∈ U)
    (h : ∀ y ∈ A, u * y * u⁻¹ * y⁻¹ ∈ pw A 2) : u ∈ Q := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  refine mem_Q_of_mem_L hS (hS.rad.U_le_L hu) fun q hq => ?_
  obtain ⟨y, hy, rfl⟩ := hC.level.exists_pow_eq hQ hQ2 hC.k_pos hq
  have he := h y hy
  have he' : (u * y * u⁻¹ * y⁻¹) ^ 2 ^ (k - 1) = 1 :=
    (hC.level.pow_eq_one_iff hQ hQ2 hC.k_pos
      (pw_le A 2 he)).2 he
  have hyA : u * y * u⁻¹ ∈ A := hC.P_norm u (hS.rad.U_le_P hu) y hy
  have hc : Commute (u * y * u⁻¹ * y⁻¹) y :=
    hC.level.comm _ (pw_le A 2 he) _ hy
  have e : u * y * u⁻¹ = (u * y * u⁻¹ * y⁻¹) * y := by group
  have e2 : u * y ^ 2 ^ (k - 1) * u⁻¹ = y ^ 2 ^ (k - 1) := by
    rw [← conj_pow, e, hc.mul_pow, he', one_mul]
  calc u * y ^ 2 ^ (k - 1) = u * y ^ 2 ^ (k - 1) * u⁻¹ * u := by group
    _ = y ^ 2 ^ (k - 1) * u := by rw [e2]

theorem mem_At_of_trivial [Finite G] {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t))
    (h : ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ pw A 2) : x ∈ A ⊔ zpowers t := by
  obtain ⟨b, hb, u, hu, rfl | rfl⟩ := hC.mem_T hS hx
  · have hu' : u ∈ Q := by
      refine hC.mem_Q_of_trivial hS hu fun y hy => ?_
      have h1 := h y hy
      have hc : b * (u * y * u⁻¹) = (u * y * u⁻¹) * b :=
        hC.level.comm _ hb _ (hC.P_norm u (hS.rad.U_le_P hu) y hy)
      have e : b * u * y * (b * u)⁻¹ * y⁻¹ = u * y * u⁻¹ * y⁻¹ := by
        calc b * u * y * (b * u)⁻¹ * y⁻¹ = b * (u * y * u⁻¹) * b⁻¹ * y⁻¹ := by group
          _ = u * y * u⁻¹ * y⁻¹ := by rw [hc, mul_inv_cancel_right]
      rwa [e] at h1
    exact mem_sup_left (mul_mem hb (hC.level.Q_le hu'))
  · have hu' : u ∈ Q := by
      refine hC.mem_Q_of_trivial hS hu fun y hy => ?_
      have hty := hC.t_conj_mem hy
      have hd : (t * y * t⁻¹) * y⁻¹ ∈ pw A 2 := by
        have := inv_mem (hC.cm_mem_pw hy)
        simp only [cm] at this
        simpa [mul_assoc] using this
      set d := (t * y * t⁻¹) * y⁻¹ with hddef
      have hdA : d ∈ A := pw_le A 2 hd
      have h1 := h y hy
      have hc : b * (u * (t * y * t⁻¹) * u⁻¹) = (u * (t * y * t⁻¹) * u⁻¹) * b :=
        hC.level.comm _ hb _ (hC.P_norm u (hS.rad.U_le_P hu) _ hty)
      have e1 : b * u * t * y * (b * u * t)⁻¹ * y⁻¹ = u * (t * y * t⁻¹) * u⁻¹ * y⁻¹ := by
        calc b * u * t * y * (b * u * t)⁻¹ * y⁻¹ = b * (u * (t * y * t⁻¹) * u⁻¹) * b⁻¹ * y⁻¹ :=
              by group
          _ = u * (t * y * t⁻¹) * u⁻¹ * y⁻¹ := by rw [hc, mul_inv_cancel_right]
      rw [e1] at h1
      have hud : u * d * u⁻¹ ∈ pw A 2 :=
        hC.pw_conj_mem (fun a ha => hC.P_norm u (hS.rad.U_le_P hu) a ha) hd
      have hc2 : (u * y * u⁻¹) * (u * d * u⁻¹) = (u * d * u⁻¹) * (u * y * u⁻¹) :=
        hC.level.comm _ (hC.P_norm u (hS.rad.U_le_P hu) y hy) _ (pw_le A 2 hud)
      have e2 : u * (t * y * t⁻¹) * u⁻¹ * y⁻¹ = (u * y * u⁻¹ * y⁻¹) * (u * d * u⁻¹) := by
        have hty' : t * y * t⁻¹ = d * y := by rw [hddef]; group
        rw [hty']
        calc u * (d * y) * u⁻¹ * y⁻¹ = (u * d * u⁻¹) * (u * y * u⁻¹) * y⁻¹ := by group
          _ = (u * y * u⁻¹) * (u * d * u⁻¹) * y⁻¹ := by rw [hc2]
          _ = (u * y * u⁻¹ * y⁻¹) * (y * (u * d * u⁻¹) * y⁻¹) := by group
          _ = (u * y * u⁻¹ * y⁻¹) * (u * d * u⁻¹) := by
            rw [hC.level.comm y hy _ (pw_le A 2 hud), mul_inv_cancel_right]
      rw [e2] at h1
      have := mul_mem h1 (inv_mem hud)
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left (mul_mem hb (hC.level.Q_le hu'))) (mem_sup_right (mem_zpowers t))

theorem mem_At_of_centralizer_Q [Finite G] {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t))
    (h : ∀ q ∈ Q, x * q = q * x) : x ∈ A ⊔ zpowers t := by
  have key : ∀ b ∈ A, ∀ u ∈ U, ∀ z : G, (∀ q ∈ Q, z * q * z⁻¹ = q) →
      (∀ q ∈ Q, b * u * z * q = q * (b * u * z)) → u ∈ Q := by
    intro b hb u hu z hz hc
    refine mem_Q_of_mem_L hS (hS.rad.U_le_L hu) fun q hq => ?_
    have huq : u * q * u⁻¹ ∈ Q := (mem_normalizer_iff.1
      (hS.rad.P_le_normalizer (hS.rad.U_le_P hu)) q).1 hq
    have h1 := hc q hq
    have h2 : b * (u * q * u⁻¹) = (u * q * u⁻¹) * b := hC.level.comm _ hb _ (hC.level.Q_le huq)
    have h3 : b * u * z * q * (b * u * z)⁻¹ = q := by rw [h1, mul_inv_cancel_right]
    have h4 : b * u * z * q * (b * u * z)⁻¹ = b * (u * (z * q * z⁻¹) * u⁻¹) * b⁻¹ := by group
    rw [h4, hz q hq, h2, mul_inv_cancel_right] at h3
    calc u * q = u * q * u⁻¹ * u := by group
      _ = q * u := by rw [h3]
  obtain ⟨b, hb, u, hu, rfl | rfl⟩ := hC.mem_T hS hx
  · have hu' := key b hb u hu 1 (fun q _ => by group) (fun q hq => by rw [mul_one]; exact h q hq)
    exact mem_sup_left (mul_mem hb (hC.level.Q_le hu'))
  · have hu' := key b hb u hu t (fun q hq => by
      rw [← hS.shape.commute_of_mem (hS.rad.Q_le_L hq), mul_inv_cancel_right]) h
    exact mul_mem (mem_sup_left (mul_mem hb (hC.level.Q_le hu'))) (mem_sup_right (mem_zpowers t))

theorem mem_A_of_centralizer_pw [Finite G] (hk : 3 ≤ k) {x : G} (hx : x ∈ A ⊔ (U ⊔ zpowers t))
    (h : ∀ c ∈ pw A 2, x * c = c * x) : x ∈ A := by
  have hQ := hS.rad.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hS.rad.Q_mul_self hq
  have hL1 := hC.level.pw_two hQ hQ2 hC.two_le
  have hk1 : 1 ≤ k - 1 := by omega
  have hQc : ∀ z : G, (∀ c ∈ pw A 2, z * c = c * z) → ∀ q ∈ Q, z * q = q * z := by
    intro z hz q hq
    obtain ⟨c, hc, rfl⟩ := hL1.exists_pow_eq hQ hQ2 hk1 hq
    exact ((Commute.pow_right (hz c hc) _))
  have hbc : ∀ b ∈ A, ∀ z : G, (∀ c ∈ pw A 2, b * z * c = c * (b * z)) →
      ∀ c ∈ pw A 2, z * c = c * z := by
    intro b hb z hz c hc
    have h1 := hz c hc
    have h2 : b * c = c * b := hC.level.comm b hb c (pw_le A 2 hc)
    have : b * (z * c) = b * (c * z) := by
      calc b * (z * c) = b * z * c := (mul_assoc _ _ _).symm
        _ = c * (b * z) := h1
        _ = c * b * z := (mul_assoc _ _ _).symm
        _ = b * c * z := by rw [h2]
        _ = b * (c * z) := mul_assoc _ _ _
    exact mul_left_cancel this
  obtain ⟨b, hb, u, hu, rfl | rfl⟩ := hC.mem_T hS hx
  · have hu' : u ∈ Q := mem_Q_of_mem_L hS (hS.rad.U_le_L hu) (hQc u (hbc b hb u h))
    exact mul_mem hb (hC.level.Q_le hu')
  · exfalso
    have hz := hbc b hb (u * t) (fun c hc => by rw [← mul_assoc]; exact h c hc)
    have hu' : u ∈ Q := by
      refine mem_Q_of_mem_L hS (hS.rad.U_le_L hu) fun q hq => ?_
      have h1 := hQc (u * t) hz q hq
      have h2 := hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
      calc u * q = u * t * q * t⁻¹ := by rw [mul_assoc u t q, ← h2]; group
        _ = q * (u * t) * t⁻¹ := by rw [h1]
        _ = q * u := by group
    have ht : ∀ c ∈ pw A 2, t * c = c * t := by
      intro c hc
      have h1 := hz c hc
      have h2 : u * c = c * u := hC.level.comm u (hC.level.Q_le hu') c (pw_le A 2 hc)
      have : u * (t * c) = u * (c * t) := by
        calc u * (t * c) = u * t * c := (mul_assoc _ _ _).symm
          _ = c * (u * t) := h1
          _ = c * u * t := (mul_assoc _ _ _).symm
          _ = u * c * t := by rw [h2]
          _ = u * (c * t) := mul_assoc _ _ _
      exact mul_left_cancel this
    have hle : pw A 2 ≤ Q := by
      intro c hc
      refine hC.level.mem_Q c (pw_le A 2 hc) ?_
      have h1 := hC.t_inv_pw hc
      rw [ht c hc, mul_inv_cancel_right] at h1
      calc c * c = c⁻¹ * c := by rw [← h1]
        _ = 1 := inv_mul_cancel c
    have := card_le_of_le hle
    rw [hC.level.card_pw_two hQ hQ2 hC.k_pos, hQ] at this
    have h12 : 2 ^ 12 ≤ 2 ^ (6 * (k - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem eq_T_of_le_NA [Finite G] {V : Subgroup G} (hV : IsPGroup 2 V)
    (hTV : A ⊔ (U ⊔ zpowers t) ≤ V) (hVN : V ≤ A ⊔ (P ⊔ zpowers t)) :
    V = A ⊔ (U ⊔ zpowers t) := by
  refine le_antisymm (fun v hv => ?_) hTV
  have hAV : A ≤ V := le_sup_left.trans hTV
  have hUV : U ⊔ zpowers t ≤ V := le_sup_right.trans hTV
  have hW : V ⊓ (P ⊔ zpowers t) = U ⊔ zpowers t := by
    refine hS.shape.sylow _ (fun y hy => ?_) (hV.to_le inf_le_left)
      (le_inf hUV (sup_le_sup_right hS.rad.U_le_P _))
    exact (sup_le (hS.rad.P_le_L.trans hS.shape.le_centralizer)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))) hy.2
  obtain ⟨b, hb, h, hh, rfl⟩ := exists_mul_of_mem_sup_normalizer hC.PT_le_normalizer (hVN hv)
  have hhV : h ∈ V := by simpa using V.mul_mem (V.inv_mem (hAV hb)) hv
  have : h ∈ U ⊔ zpowers t := hW ▸ ⟨hhV, hh⟩
  exact mul_mem (mem_sup_left hb) (mem_sup_right this)

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
