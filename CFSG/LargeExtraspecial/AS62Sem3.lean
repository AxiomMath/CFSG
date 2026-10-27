module

public import CFSG.LargeExtraspecial.AS62Sem

public section

namespace CFSG.LargeExtraspecial.AS62

open Sem

namespace Frame

variable {G : Type*} [Group G] (F : Frame G)

def RelsOKG (x z u v : G) : Prop :=
  u * u = 1 ∧ u * (x * u * x⁻¹) = x * u * x⁻¹ * u ∧
    x * (x * u * x⁻¹) * x⁻¹ = z * u * (x * u * x⁻¹) ∧
  v * v = 1 ∧ v * (x * v * x⁻¹) = x * v * x⁻¹ * v ∧ x * (x * v * x⁻¹) * x⁻¹ = v * (x * v * x⁻¹) ∧
  u * v * u⁻¹ * v⁻¹ = 1 ∧ u * (x * v * x⁻¹) * u⁻¹ * (x * v * x⁻¹)⁻¹ = z ∧
  x * u * x⁻¹ * v * (x * u * x⁻¹)⁻¹ * v⁻¹ = z ∧
  x * u * x⁻¹ * (x * v * x⁻¹) * (x * u * x⁻¹)⁻¹ * (x * v * x⁻¹)⁻¹ = 1

theorem RelsOKG.map {G' : Type*} [Group G'] {x z u v : G} (h : RelsOKG x z u v) (φ : G →* G') :
    RelsOKG (φ x) (φ z) (φ u) (φ v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h1
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h2
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h3
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h4
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h5
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h6
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h7
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h8
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h9
  · simpa only [map_mul, map_inv, map_one] using congrArg φ h10

theorem RelsOKG.conj {x z u v m : G} (h : RelsOKG x z u v) (hmx : m * x = x * m)
    (hmz : m * z = z * m) : RelsOKG x z (m * u * m⁻¹) (m * v * m⁻¹) := by
  have h' := h.map (MulAut.conj m).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
  rwa [hmx, hmz, mul_inv_cancel_right, mul_inv_cancel_right] at h'

theorem deq_iff {g h : G} {dg dh : ℕ × ℕ} (hg : F.Rep g dg) (hh : F.Rep h dh) :
    deq dg dh = true ↔ g = h :=
  ⟨fun e => F.eq_of_rep hg (eq_of_deq e ▸ hh), fun e => by
    rw [F.rep_unique hg (e ▸ hh)]
    exact deq_self _⟩

theorem relsOK_iff {x z u v : G} {du dv : ℕ × ℕ} (hx : F.Rep x xD) (hz : F.Rep z zD)
    (hu : F.Rep u du) (hv : F.Rep v dv) : relsOK du dv = true ↔ RelsOKG x z u v := by
  have hu2 : F.Rep (x * u * x⁻¹) (dconj xD du) := F.rep_mul (F.rep_mul hx hu) (F.rep_inv hx)
  have hv2 : F.Rep (x * v * x⁻¹) (dconj xD dv) := F.rep_mul (F.rep_mul hx hv) (F.rep_inv hx)
  have hu3 : F.Rep (x * (x * u * x⁻¹) * x⁻¹) (dconj xD (dconj xD du)) :=
    F.rep_mul (F.rep_mul hx hu2) (F.rep_inv hx)
  have hv3 : F.Rep (x * (x * v * x⁻¹) * x⁻¹) (dconj xD (dconj xD dv)) :=
    F.rep_mul (F.rep_mul hx hv2) (F.rep_inv hx)
  have hc : ∀ {a b : G} {da db : ℕ × ℕ}, F.Rep a da → F.Rep b db →
      F.Rep (a * b * a⁻¹ * b⁻¹) (dcomm da db) :=
    fun ha hb => F.rep_mul (F.rep_mul (F.rep_mul ha hb) (F.rep_inv ha)) (F.rep_inv hb)
  have e1 := F.deq_iff (F.rep_mul hu hu) F.rep_one
  have e2 := F.deq_iff (F.rep_mul hu hu2) (F.rep_mul hu2 hu)
  have e3 := F.deq_iff hu3 (F.rep_mul (F.rep_mul hz hu) hu2)
  have e4 := F.deq_iff (F.rep_mul hv hv) F.rep_one
  have e5 := F.deq_iff (F.rep_mul hv hv2) (F.rep_mul hv2 hv)
  have e6 := F.deq_iff hv3 (F.rep_mul hv hv2)
  have e7 := F.deq_iff (hc hu hv) F.rep_one
  have e8 := F.deq_iff (hc hu hv2) hz
  have e9 := F.deq_iff (hc hu2 hv) hz
  have e10 := F.deq_iff (hc hu2 hv2) F.rep_one
  simp only [relsOK, uOK, vOK, mixedOK, Bool.and_eq_true, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, RelsOKG, and_assoc]

theorem mem_sol18_of_relsOKG {x z u v : G} {du dv : ℕ × ℕ} (hx : F.Rep x xD) (hz : F.Rep z zD)
    (hu : F.Rep u du) (hv : F.Rep v dv) (hu2 : du.2 ∈ k1Codes) (hv2 : dv.2 ∈ k1Codes)
    (h : RelsOKG x z u v) : (du, dv) ∈ sol18 :=
  mem_sol18_of_relsOK (F.rep_lt hu) hu2 (F.rep_lt hv) hv2 ((F.relsOK_iff hx hz hu hv).2 h)

theorem relsOKG_of_mem_sol18 {x z u v : G} {du dv : ℕ × ℕ} (hx : F.Rep x xD)
    (hz : F.Rep z zD) (hu : F.Rep u du) (hv : F.Rep v dv) (h : (du, dv) ∈ sol18) :
    RelsOKG x z u v :=
  (F.relsOK_iff hx hz hu hv).1 (relsOK_of_mem_sol18 (du, dv) h)

theorem permCode_mem_k1Codes {p : Equiv.Perm (Fin 5)}
    (h : p = 1 ∨ p = Equiv.swap 1 2 * Equiv.swap 3 4 ∨ p = Equiv.swap 1 3 * Equiv.swap 2 4 ∨
      p = Equiv.swap 1 4 * Equiv.swap 2 3) : permCode p ∈ k1Codes := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

variable {z t e x : G}

theorem rep_ze (hz : F.Rep z zD) (he : F.Rep e eD) : F.Rep (z * e) zeD := F.rep_mul hz he

theorem rep_tet (ht : F.Rep t tD) (he : F.Rep e eD) : F.Rep (t * e * t) tetD :=
  F.rep_mul (F.rep_mul ht he) ht

theorem rep_b1 (ht : F.Rep t tD) (he : F.Rep e eD) : F.Rep (t * e * t * e) b1D :=
  F.rep_mul (F.rep_tet ht he) he

theorem rep_b2 (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    F.Rep (x * (t * e * t * e) * x⁻¹) b2D :=
  F.rep_mul (F.rep_mul hx (F.rep_b1 ht he)) (F.rep_inv hx)

theorem rep_e2 (he : F.Rep e eD) (hx : F.Rep x xD) : F.Rep (x * e * x⁻¹) e2D :=
  F.rep_mul (F.rep_mul hx he) (F.rep_inv hx)

theorem relsOKG_b1_e (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD) :
    RelsOKG x z (t * e * t * e) e :=
  F.relsOKG_of_mem_sol18 hx hz (F.rep_b1 ht he) he (by decide +kernel)

theorem I1 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) :
    z * (z * e) * (t * e * t) = t * e * t * e :=
  F.eq_of_rep (F.rep_congr (F.rep_mul (F.rep_mul hz (F.rep_ze hz he)) (F.rep_tet ht he))
    dmul_I1) (F.rep_b1 ht he)

theorem I2 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) :
    z * (t * e * t) * (z * e) * (t * e * t) = e :=
  F.eq_of_rep (F.rep_congr (F.rep_mul (F.rep_mul (F.rep_mul hz (F.rep_tet ht he))
    (F.rep_ze hz he)) (F.rep_tet ht he)) dmul_I2) he

theorem I3 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) :
    t * (z * e) * t = z * (t * e * t) :=
  F.eq_of_rep (F.rep_congr (F.rep_mul (F.rep_mul ht (F.rep_ze hz he)) ht) dmul_I3)
    (F.rep_mul hz (F.rep_tet ht he))

theorem I4 (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) :
    t * (z * e * (t * e * t)) * t = z * e * (t * e * t) :=
  F.eq_of_rep (F.rep_congr (F.rep_mul (F.rep_mul ht (F.rep_mul (F.rep_ze hz he)
    (F.rep_tet ht he))) ht) dmul_I4) (F.rep_mul (F.rep_ze hz he) (F.rep_tet ht he))

@[expose] def qProd (z t e x : G) (c : ℕ) : G :=
  bitPow (t * e * t * e) (c.testBit 0) * bitPow (x * (t * e * t * e) * x⁻¹) (c.testBit 1) *
    bitPow e (c.testBit 2) * bitPow (x * e * x⁻¹) (c.testBit 3) * bitPow z (c.testBit 4)

theorem rep_bitPow {g : G} {d : ℕ × ℕ} (hg : F.Rep g d) (b : Bool) :
    F.Rep (bitPow g b) (cond b d one) := by
  cases b
  · exact F.rep_one
  · exact hg

theorem rep_qProd (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    (c : ℕ) : F.Rep (qProd z t e x c) (qProdD c) :=
  F.rep_mul (F.rep_mul (F.rep_mul (F.rep_mul (F.rep_bitPow (F.rep_b1 ht he) _)
    (F.rep_bitPow (F.rep_b2 ht he hx) _)) (F.rep_bitPow he _))
    (F.rep_bitPow (F.rep_e2 he hx) _)) (F.rep_bitPow hz _)

theorem qProd_injective (hz : F.Rep z zD) (ht : F.Rep t tD) (he : F.Rep e eD) (hx : F.Rep x xD)
    {c d : ℕ} (hc : c < 32) (hd : d < 32) (h : qProd z t e x c = qProd z t e x d) : c = d :=
  qProdD_injective hc hd
    (F.rep_unique (F.rep_qProd hz ht he hx c) (h ▸ F.rep_qProd hz ht he hx d))

end Frame

end CFSG.LargeExtraspecial.AS62
