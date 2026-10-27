module

public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneBasic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv
open scoped commutatorElement

structure ASide {G : Type*} [Group G] (A V W : Subgroup G) : Prop where
  le : V ≤ A
  trans : ∀ w ∈ W, ∀ w' ∈ W, w ≠ 1 → w' ≠ 1 →
    ∃ a ∈ A ⊓ normalizer (W : Set G), a * w * a⁻¹ = w'
  torus : ∀ g : G, (∀ v ∈ V, g * v * g⁻¹ ∈ A) →
    ∃ y : G, g * y * g⁻¹ ∈ A ∧ y ∈ normalizer (W : Set G) ∧
      y ∈ normalizer ((V ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ∧
      ∀ w ∈ V ⊓ centralizer (V : Set G), y * w * y⁻¹ = w → w = 1
  spread : ∀ a ∈ A ⊓ normalizer (W : Set G),
    (∃ u ∈ V ⊓ centralizer (V : Set G), u ≠ 1 ∧ a * u * a⁻¹ ∈ V ⊓ centralizer (V : Set G)) →
    ∀ u ∈ V ⊓ centralizer (V : Set G), a * u * a⁻¹ ∈ V ⊓ centralizer (V : Set G)

namespace Datum

section U

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G} {W : Subgroup G}

abbrev U (d : Datum A) : Subgroup G := d.V ⊓ centralizer (d.V : Set G)

@[expose] def line₀ (d : Datum A) (W : Subgroup G) : Set G := {x | x ∈ d.pts W ∧ x * d.t ∈ d.U}

omit [Finite G] in
theorem U_le (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) : d.U ≤ W := by
  have h : d.U ≤ V₁ ⊓ V₂ := hR.inf_eq.symm.le
  rcases hW with rfl | rfl
  · exact h.trans inf_le_left
  · exact h.trans inf_le_right

omit [Finite G] in
theorem U_mul_self (d : Datum A) (hR : Radicals d.V V₁ V₂) {u : G} (hu : u ∈ d.U) :
    u * u = 1 :=
  hR.mul_self_of_mem_center hu

omit [Finite G] in
theorem U_comm_t (d : Datum A) {u : G} (hu : u ∈ d.U) : u * d.t = d.t * u :=
  d.V_comm_t hu.1

omit [Finite G] in
theorem U_inv (d : Datum A) (hR : Radicals d.V V₁ V₂) {u : G} (hu : u ∈ d.U) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (d.U_mul_self hR hu)

theorem mem_normalizer_E (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) {y : G}
    (hyW : y ∈ normalizer (W : Set G)) (hyt : y * d.t * y⁻¹ ∈ d.E W) :
    y ∈ normalizer ((d.E W : Subgroup G) : Set G) := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rcases (d.mem_adj_iff hWV).mp hx with hxW | hxW
  · exact mem_sup_left ((mem_normalizer_iff.mp hyW x).mp hxW)
  · have e : y * x * y⁻¹ = (y * (x * d.t) * y⁻¹) * (y * d.t * y⁻¹) := by
      calc y * x * y⁻¹ = y * (x * d.t * d.t) * y⁻¹ := by
            rw [mul_assoc x d.t d.t, d.t_mul_self, mul_one]
        _ = (y * (x * d.t) * y⁻¹) * (y * d.t * y⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hyW _).mp hxW)) hyt

omit [Finite G] in
theorem conj_t_of_mem_A (d : Datum A) {a : G} (ha : a ∈ A) : a * d.t * a⁻¹ = d.t := by
  rw [mul_inv_eq_iff_eq_mul]
  exact d.comm_t_of_mem ha

theorem mem_normalizer_E_of_mem_A (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) {a : G} (ha : a ∈ A ⊓ normalizer (W : Set G)) :
    a ∈ normalizer ((d.E W : Subgroup G) : Set G) :=
  d.mem_normalizer_E hR hW ha.2 (by
    rw [d.conj_t_of_mem_A ha.1]
    exact mem_sup_right (mem_zpowers _))

theorem mem_line₀_iff (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) {x : G} : x ∈ d.line₀ W ↔ ∃ u ∈ d.U, x = u * d.t := by
  constructor
  · rintro ⟨-, hx⟩
    exact ⟨x * d.t, hx, by rw [mul_assoc, d.t_mul_self, mul_one]⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(F.mem_pts_iff d hR hα hW).mpr ⟨u, d.U_le hR hW hu, ?_⟩, ?_⟩
    · exact d.U_comm_t hu
    · rwa [mul_assoc, d.t_mul_self, mul_one]

omit [Finite G] in
theorem mem_line₀_conj (d : Datum A) {m : G} (hmE : m ∈ normalizer ((d.E W : Subgroup G) : Set G))
    (hmU : m ∈ normalizer (d.U : Set G)) (hmt : (m * d.t * m⁻¹) * d.t ∈ d.U) {z : G}
    (hz : z ∈ d.pts W) : m * z * m⁻¹ ∈ d.line₀ W ↔ z ∈ d.line₀ W := by
  have hz' : m * z * m⁻¹ ∈ d.pts W := Datum.pts_conj hmE hz
  have hs2 : (m * d.t * m⁻¹) * (m * d.t * m⁻¹) = 1 := by
    calc (m * d.t * m⁻¹) * (m * d.t * m⁻¹) = m * (d.t * d.t) * m⁻¹ := by group
      _ = 1 := by rw [d.t_mul_self]; group
  have e : (m * z * m⁻¹) * d.t = (m * (z * d.t) * m⁻¹) * ((m * d.t * m⁻¹) * d.t) := by
    calc (m * z * m⁻¹) * d.t = (m * z * m⁻¹) * (((m * d.t * m⁻¹) * (m * d.t * m⁻¹)) * d.t) := by
          rw [hs2, one_mul]
      _ = (m * (z * d.t) * m⁻¹) * ((m * d.t * m⁻¹) * d.t) := by group
  constructor
  · rintro ⟨-, h⟩
    rw [e, Subgroup.mul_mem_cancel_right _ hmt] at h
    exact ⟨hz, (mem_normalizer_iff.mp hmU _).mpr h⟩
  · rintro ⟨-, h⟩
    refine ⟨hz', ?_⟩
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp hmU _).mp h) hmt

end U

end Datum

namespace Facts

section Geometry

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem exists_moving (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) :
    ∃ y ∈ normalizer ((d.E W : Subgroup G) : Set G), y ∈ normalizer (d.U : Set G) ∧
      ∃ u ∈ d.U, u ≠ 1 ∧ y * d.t * y⁻¹ = u * d.t := by
  obtain ⟨u₀, hu₀U, hu₀P, hu₀1, hu₀2, hconj⟩ := F.exists_u₀ d hR hα
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hgt : c⁻¹⁻¹ * d.t * c⁻¹ = u₀ * d.t := by rw [inv_inv]; exact hc
  have hg : c⁻¹⁻¹ * d.t * c⁻¹ ∈ d.P ⊓ centralizer (d.P : Set G) := by
    rw [hgt]
    exact ⟨mul_mem hu₀U.1.1 d.t_mem_P, mul_mem hu₀P d.t_mem_centralizer_P⟩
  obtain ⟨y, hyA, hyW, hyU, hfix⟩ := AS.torus c⁻¹ (fun v hv => F.conj_V_le_A d hR hα hg hv)
  have hyt' : y * (u₀ * d.t) * y⁻¹ = u₀ * d.t := by
    have h1 : (c⁻¹ * y * c) * d.t * (c⁻¹ * y * c)⁻¹ = d.t := by
      have := d.conj_t_of_mem_A hyA
      simpa [inv_inv] using this
    calc y * (u₀ * d.t) * y⁻¹ = y * (c * d.t * c⁻¹) * y⁻¹ := by rw [hc]
      _ = c * ((c⁻¹ * y * c) * d.t * (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
      _ = c * d.t * c⁻¹ := by rw [h1]
      _ = u₀ * d.t := hc
  have hyu₀ : y * u₀ * y⁻¹ ∈ d.U := (mem_normalizer_iff.mp hyU u₀).mp hu₀U
  have hu₂ : (y * u₀ * y⁻¹) * u₀ ∈ d.U := mul_mem hyu₀ hu₀U
  have hyt : y * d.t * y⁻¹ = ((y * u₀ * y⁻¹) * u₀) * d.t := by
    calc y * d.t * y⁻¹ = (y * u₀ * y⁻¹) * (y * (u₀ * d.t) * y⁻¹) := by
          calc y * d.t * y⁻¹ = y * ((u₀ * u₀) * d.t) * y⁻¹ := by rw [hu₀2, one_mul]
            _ = (y * u₀ * y⁻¹) * (y * (u₀ * d.t) * y⁻¹) := by group
      _ = ((y * u₀ * y⁻¹) * u₀) * d.t := by rw [hyt']; group
  refine ⟨y, d.mem_normalizer_E hR hW hyW ?_, hyU, _, hu₂, ?_, hyt⟩
  · rw [hyt]
    exact mul_mem (mem_sup_left (d.U_le hR hW hu₂)) (mem_sup_right (mem_zpowers _))
  · intro h1
    apply hu₀1
    apply hfix u₀ hu₀U
    have h2 : y * u₀ * y⁻¹ = u₀⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, d.U_inv hR hu₀U]

omit [Finite G] in
theorem exists_torusA (d : Datum A) (AS : ASide A d.V W) :
    ∃ y ∈ A ⊓ normalizer (W : Set G), y ∈ normalizer (d.U : Set G) ∧
      ∀ w ∈ d.U, y * w * y⁻¹ = w → w = 1 := by
  obtain ⟨y, hyA, hyW, hyU, hfix⟩ := AS.torus 1 (fun v hv => by simpa using AS.le hv)
  exact ⟨y, ⟨by simpa using hyA, hyW⟩, hyU, hfix⟩

theorem exists_conj_U_le (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) {c : G} (hcE : c ∈ normalizer ((d.E W : Subgroup G) : Set G))
    (hct : c * d.t * c⁻¹ = d.t) :
    ∃ a ∈ A ⊓ normalizer (W : Set G), ∀ u ∈ d.U, ∃ u' ∈ d.U, c * u * c⁻¹ = a * u' * a⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcW : c ∈ normalizer (W : Set G) := F.normalizer_adj_le d hR hα hW hcE
  have hcA : c ∈ normalizer (A : Set G) := (centralizer_t_facts d.sector).1
    (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hct))
  have hVA : IsSylowOf 2 d.V A := d.V_isSylow
  have hVN : d.V ≤ normalizer (W : Set G) := by
    rcases hW with rfl | rfl
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR.le₁).mp hR.normal₁
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR.le₂).mp hR.normal₂
  have hVM : d.V ≤ A ⊓ normalizer (W : Set G) := le_inf hVA.le hVN
  have hV_M : IsSylowOf 2 d.V (A ⊓ normalizer (W : Set G)) := hVA.of_le hVM inf_le_left
  set V' : Subgroup G := d.V.map (MulAut.conj c).toMonoidHom with hV'
  have hV'A : V' ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.mp hcA v).mp (hVA.le hv)
  have hcW' : ∀ w ∈ W, c⁻¹ * w * c ∈ W := fun w hw =>
    (mem_normalizer_iff.mp hcW (c⁻¹ * w * c)).mpr (by
      have e : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
      rw [e]
      exact hw)
  have hV'N : V' ≤ normalizer (W : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    have h1 : v * (c⁻¹ * w * c) * v⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (hVN hv) _).mp (hcW' w hw)
    have h2 := (mem_normalizer_iff.mp hcW _).mp h1
    have e : (MulAut.conj c).toMonoidHom v * w * ((MulAut.conj c).toMonoidHom v)⁻¹ =
        c * (v * (c⁻¹ * w * c) * v⁻¹) * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact h2
  have hV'card : Nat.card V' = Nat.card d.V :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hV'syl : IsSylowOf 2 V' A :=
    isSylowOf_of_card hV'A (by rw [hV'card]; exact hVA.card_eq)
  have hV'_M : IsSylowOf 2 V' (A ⊓ normalizer (W : Set G)) :=
    hV'syl.of_le (le_inf hV'A hV'N) inf_le_left
  obtain ⟨k, hkM, hk⟩ := hV_M.exists_mem_conj hV'_M
  refine ⟨k, hkM, fun u hu => ?_⟩
  have hxV' : c * u * c⁻¹ ∈ V' := ⟨u, hu.1, rfl⟩
  have hyV : k⁻¹ * (c * u * c⁻¹) * k ∈ d.V := (hk _).mp hxV'
  have hyc : k⁻¹ * (c * u * c⁻¹) * k ∈ centralizer (d.V : Set G) := by
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : k * v * k⁻¹ ∈ V' := (hk _).mpr (by
      have e : k⁻¹ * (k * v * k⁻¹) * k = v := by group
      rw [e]
      exact hv)
    obtain ⟨v₀, hv₀, hv₀e⟩ := hv'
    have hv₀e' : c * v₀ * c⁻¹ = k * v * k⁻¹ := hv₀e
    have hcomm : (c * u * c⁻¹) * (k * v * k⁻¹) = (k * v * k⁻¹) * (c * u * c⁻¹) := by
      rw [← hv₀e']
      have := mem_centralizer_iff.mp hu.2 v₀ hv₀
      calc c * u * c⁻¹ * (c * v₀ * c⁻¹) = c * (u * v₀) * c⁻¹ := by group
        _ = c * (v₀ * u) * c⁻¹ := by rw [this]
        _ = c * v₀ * c⁻¹ * (c * u * c⁻¹) := by group
    calc v * (k⁻¹ * (c * u * c⁻¹) * k) = k⁻¹ * ((k * v * k⁻¹) * (c * u * c⁻¹)) * k := by group
      _ = k⁻¹ * ((c * u * c⁻¹) * (k * v * k⁻¹)) * k := by rw [hcomm]
      _ = k⁻¹ * (c * u * c⁻¹) * k * v := by group
  exact ⟨k⁻¹ * (c * u * c⁻¹) * k, ⟨hyV, hyc⟩, by group⟩

theorem exists_conj_t (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) {x : G} (hx : x ∈ d.pts W) :
    ∃ n ∈ normalizer ((d.E W : Subgroup G) : Set G), n * d.t * n⁻¹ = x := by
  obtain ⟨w, hw, rfl⟩ := (F.mem_pts_iff d hR hα hW).mp hx
  obtain ⟨hWV, -, -⟩ := hR.property hW
  by_cases hw1 : w = 1
  · exact ⟨1, one_mem _, by simp [hw1]⟩
  obtain ⟨y, hyE, hyU, u, hu, hu1, hyt⟩ := F.exists_moving d hR hα hW AS
  obtain ⟨a, haM, hau⟩ := AS.trans u (d.U_le hR hW hu) w hw hu1 hw1
  refine ⟨a * y, mul_mem (d.mem_normalizer_E_of_mem_A hR hW haM) hyE, ?_⟩
  have hat := d.conj_t_of_mem_A haM.1
  calc a * y * d.t * (a * y)⁻¹ = a * (y * d.t * y⁻¹) * a⁻¹ := by group
    _ = a * (u * d.t) * a⁻¹ := by rw [hyt]
    _ = (a * u * a⁻¹) * (a * d.t * a⁻¹) := by group
    _ = w * d.t := by rw [hau, hat]
    _ = d.t * w := d.V_comm_t (hWV hw)

theorem exists_conj_fix (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) {x y : G} (hx : x ∈ d.pts W)
    (hy : y ∈ d.pts W) (hxt : x ≠ d.t) (hyt : y ≠ d.t) :
    ∃ n ∈ normalizer ((d.E W : Subgroup G) : Set G), n * d.t * n⁻¹ = d.t ∧ n * x * n⁻¹ = y := by
  obtain ⟨w, hw, rfl⟩ := (F.mem_pts_iff d hR hα hW).mp hx
  obtain ⟨w', hw', rfl⟩ := (F.mem_pts_iff d hR hα hW).mp hy
  have hw1 : w ≠ 1 := fun h => hxt (by rw [h, mul_one])
  have hw1' : w' ≠ 1 := fun h => hyt (by rw [h, mul_one])
  obtain ⟨a, haM, hau⟩ := AS.trans w hw w' hw' hw1 hw1'
  have hat := d.conj_t_of_mem_A haM.1
  refine ⟨a, d.mem_normalizer_E_of_mem_A hR hW haM, hat, ?_⟩
  calc a * (d.t * w) * a⁻¹ = (a * d.t * a⁻¹) * (a * w * a⁻¹) := by group
    _ = d.t * w' := by rw [hat, hau]

theorem exists_stab (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) {x : G} (hx : x ∈ d.line₀ W) :
    ∃ n ∈ normalizer ((d.E W : Subgroup G) : Set G),
      (∀ z ∈ d.pts W, n * z * n⁻¹ ∈ d.line₀ W ↔ z ∈ d.line₀ W) ∧ n * d.t * n⁻¹ = x := by
  obtain ⟨u, hu, rfl⟩ := (d.mem_line₀_iff F hR hα hW).mp hx
  by_cases hu1 : u = 1
  · exact ⟨1, one_mem _, fun z _ => by simp, by simp [hu1]⟩
  obtain ⟨y, hyE, hyU, u₂, hu₂, hu₂1, hyt⟩ := F.exists_moving d hR hα hW AS
  obtain ⟨yA, hyAM, hyAU, hyAfix⟩ := exists_torusA d AS
  obtain ⟨k, hk⟩ := exists_conj_pow_eq_of_card_four hR.card_center hyAU hyAfix hu₂ hu hu₂1 hu1
  have hykM : yA ^ k ∈ A ⊓ normalizer (W : Set G) := pow_mem hyAM k
  have hykE := d.mem_normalizer_E_of_mem_A hR hW hykM
  have hat := d.conj_t_of_mem_A hykM.1
  have hykU : yA ^ k ∈ normalizer (d.U : Set G) := pow_mem hyAU k
  refine ⟨yA ^ k * y, mul_mem hykE hyE, fun z hz => ?_, ?_⟩
  · have hmt : (y * d.t * y⁻¹) * d.t ∈ d.U := by
      rw [hyt, mul_assoc, d.t_mul_self, mul_one]
      exact hu₂
    have hmt' : (yA ^ k * d.t * (yA ^ k)⁻¹) * d.t ∈ d.U := by
      rw [hat, d.t_mul_self]
      exact one_mem _
    have h1 := d.mem_line₀_conj hyE hyU hmt hz
    have h2 := d.mem_line₀_conj hykE hykU hmt' (Datum.pts_conj hyE hz)
    have e : (yA ^ k * y) * z * (yA ^ k * y)⁻¹ = yA ^ k * (y * z * y⁻¹) * (yA ^ k)⁻¹ := by group
    rw [e]
    exact h2.trans h1
  · calc yA ^ k * y * d.t * (yA ^ k * y)⁻¹ = yA ^ k * (y * d.t * y⁻¹) * (yA ^ k)⁻¹ := by group
      _ = yA ^ k * (u₂ * d.t) * (yA ^ k)⁻¹ := by rw [hyt]
      _ = (yA ^ k * u₂ * (yA ^ k)⁻¹) * (yA ^ k * d.t * (yA ^ k)⁻¹) := by group
      _ = u * d.t := by rw [hk, hat]

theorem line₀_spread (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) {n : G}
    (hn : n ∈ normalizer ((d.E W : Subgroup G) : Set G)) (hnt : n * d.t * n⁻¹ = d.t) {b : G}
    (hb : b ∈ d.line₀ W) (hbt : b ≠ d.t) (hnb : n * b * n⁻¹ ∈ d.line₀ W) {z : G}
    (hz : z ∈ d.pts W) : n * z * n⁻¹ ∈ d.line₀ W ↔ z ∈ d.line₀ W := by
  obtain ⟨u, hu, rfl⟩ := (d.mem_line₀_iff F hR hα hW).mp hb
  have hu1 : u ≠ 1 := fun h => hbt (by rw [h, one_mul])
  obtain ⟨u'', hu'', he⟩ := (d.mem_line₀_iff F hR hα hW).mp hnb
  have hnu : n * u * n⁻¹ = u'' := by
    have e : n * (u * d.t) * n⁻¹ = (n * u * n⁻¹) * d.t := by
      calc n * (u * d.t) * n⁻¹ = (n * u * n⁻¹) * (n * d.t * n⁻¹) := by group
        _ = (n * u * n⁻¹) * d.t := by rw [hnt]
    rw [e] at he
    exact mul_right_cancel he
  obtain ⟨a, haM, ha⟩ := F.exists_conj_U_le d hR hα hW hn hnt
  obtain ⟨u', hu', hau'⟩ := ha u hu
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    have h2 : n * u * n⁻¹ = 1 := by rw [hau', h]; group
    simpa [mul_inv_eq_one] using h2
  have hall := AS.spread a haM ⟨u', hu', hu'1, by rw [← hau', hnu]; exact hu''⟩
  have hnU : n ∈ normalizer (d.U : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨w', hw', hw'e⟩ := ha w hw
    rw [hw'e]
    exact hall w' hw'
  exact d.mem_line₀_conj hn hnU (by rw [hnt, d.t_mul_self]; exact one_mem _) hz

theorem ncard_line₀ (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) : (d.line₀ W).ncard = 4 := by
  have e : d.line₀ W = (fun u : G => u * d.t) '' (d.U : Set G) := by
    ext x
    rw [d.mem_line₀_iff F hR hα hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  rw [e, Set.ncard_image_of_injective _ (mul_left_injective d.t),
    ← Nat.card_coe_set_eq]
  exact hR.card_center

end Geometry

end Facts

end CFSG.OddStandard.Seitz77
