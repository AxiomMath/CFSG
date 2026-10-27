module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup

variable {G : Type} [Group G]

@[expose] def tauFn (t x : G) : G := x * t * x⁻¹ * t⁻¹

structure Cl2 (K B : Subgroup G) : Prop where
  B_le : B ≤ K
  central : ∀ k ∈ K, ∀ b ∈ B, k * b = b * k
  comm_mem : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ B
  sq_mem : ∀ x ∈ K, x * x ∈ B
  B_sq : ∀ b ∈ B, b * b = 1

variable {K B : Subgroup G}

theorem tauFn_eq_one_iff {t x : G} : tauFn t x = 1 ↔ x * t = t * x := by
  unfold tauFn
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem Cl2.comm_B (h : Cl2 K B) {a b : G} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a :=
  h.central a (h.B_le ha) b hb

theorem Cl2.sq_mul (h : Cl2 K B) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    (x * y) * (x * y) = (x * x) * (y * y) * (y * x * y⁻¹ * x⁻¹) := by
  have hc : x * y * x⁻¹ * y⁻¹ ∈ B := h.comm_mem x hx y hy
  have hd : y * x * y⁻¹ * x⁻¹ ∈ B := by
    have := B.inv_mem hc
    simpa [mul_assoc] using this
  obtain ⟨d, hdd⟩ : ∃ d, d = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hdx : Commute x d := h.central x hx d hd
  have hdy : Commute y d := h.central y hy d hd
  have e1 : y * x = d * (x * y) := by rw [hdd]; group
  have hcom : d * (x * x * (y * y)) = (x * x * (y * y)) * d :=
    ((hdx.symm.mul_right hdx.symm).mul_right (hdy.symm.mul_right hdy.symm)).eq
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (d * (x * y)) * y := by rw [e1]
    _ = (x * d) * (x * y * y) := by group
    _ = (d * x) * (x * y * y) := by rw [hdx.eq]
    _ = d * (x * x * (y * y)) := by group
    _ = (x * x * (y * y)) * d := hcom
    _ = (x * x) * (y * y) * d := by group

theorem Cl2.sq_mul_B (h : Cl2 K B) {x b : G} (hx : x ∈ K) (hb : b ∈ B) :
    (x * b) * (x * b) = x * x := by
  have hc : x * b = b * x := h.central x hx b hb
  calc (x * b) * (x * b) = x * (b * x) * b := by group
    _ = x * (x * b) * b := by rw [← hc]
    _ = (x * x) * (b * b) := by group
    _ = x * x := by rw [h.B_sq b hb, mul_one]

theorem Cl2.comm_mul (h : Cl2 K B) {x y z : G} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    z * (x * y) * z⁻¹ * (x * y)⁻¹ = (z * x * z⁻¹ * x⁻¹) * (z * y * z⁻¹ * y⁻¹) := by
  have hq : x * (z * y * z⁻¹ * y⁻¹) = (z * y * z⁻¹ * y⁻¹) * x :=
    h.central x hx _ (h.comm_mem z hz y hy)
  calc z * (x * y) * z⁻¹ * (x * y)⁻¹
      = (z * x * z⁻¹ * x⁻¹) * (x * (z * y * z⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (z * x * z⁻¹ * x⁻¹) * ((z * y * z⁻¹ * y⁻¹) * x * x⁻¹) := by rw [hq]
    _ = (z * x * z⁻¹ * x⁻¹) * (z * y * z⁻¹ * y⁻¹) := by group

theorem Cl2.sq_cube (h : Cl2 K B) {x y z : G} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    (x * y * z) * (x * y * z) * ((x * x) * (y * y) * (z * z)) =
      ((x * y) * (x * y)) * ((x * z) * (x * z)) * ((y * z) * (y * z)) := by
  haveI : IsMulCommutative ↥B := ⟨⟨fun a b => Subtype.ext (h.comm_B a.2 b.2)⟩⟩
  have h1 := h.sq_mul (K.mul_mem hx hy) hz
  have h2 := h.sq_mul hx hy
  have h3 := h.sq_mul hx hz
  have h4 := h.sq_mul hy hz
  have hC := h.comm_mul hx hy hz
  rw [h1, hC, h2, h3, h4]
  let a : ↥B := ⟨x * x, h.sq_mem x hx⟩
  let b : ↥B := ⟨y * y, h.sq_mem y hy⟩
  let c : ↥B := ⟨z * z, h.sq_mem z hz⟩
  let p : ↥B := ⟨y * x * y⁻¹ * x⁻¹, by
    simpa [mul_assoc] using B.inv_mem (h.comm_mem x hx y hy)⟩
  let q : ↥B := ⟨z * x * z⁻¹ * x⁻¹, h.comm_mem z hz x hx⟩
  let r : ↥B := ⟨z * y * z⁻¹ * y⁻¹, h.comm_mem z hz y hy⟩
  have key : (a * b * p * c * (q * r)) * (a * b * c) = (a * b * p) * (a * c * q) * (b * c * r) := by
    ac_rfl
  have := congrArg Subtype.val key
  simpa [a, b, c, p, q, r, mul_assoc] using this

theorem Cl2.tau_mul (h : Cl2 K B) {t x y : G} (ht : t ∈ K) (hx : x ∈ K) (hy : y ∈ K) :
    tauFn t (x * y) = tauFn t x * tauFn t y := by
  have hy' : tauFn t y ∈ B := h.comm_mem y hy t ht
  have hx' : tauFn t x ∈ B := h.comm_mem x hx t ht
  have e : tauFn t (x * y) = x * tauFn t y * x⁻¹ * tauFn t x := by unfold tauFn; group
  have hc : x * tauFn t y = tauFn t y * x := h.central x hx _ hy'
  calc tauFn t (x * y) = x * tauFn t y * x⁻¹ * tauFn t x := e
    _ = tauFn t y * x * x⁻¹ * tauFn t x := by rw [hc]
    _ = tauFn t y * tauFn t x := by group
    _ = tauFn t x * tauFn t y := h.comm_B hy' hx'

theorem Cl2.tau_mem (h : Cl2 K B) {t x : G} (ht : t ∈ K) (hx : x ∈ K) : tauFn t x ∈ B :=
  h.comm_mem x hx t ht

end A3

end CFSG.OddStandard.SmallF3.Omega
