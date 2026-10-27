module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneCoordsDefs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneECoordsMat

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "𝔽" => Fin 3 → ZMod 2

variable {G : Type} [Group G]

structure ECBase (τ : Multiplicative 𝕊 →* G) (lev : GL (Fin 3) (ZMod 2) →* G) (z : G)
    (ν : G → 𝕊) (C E Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) : Prop where
  vc : EpsOneVCoords Jh E C z lev (fun c => symThreeDiag (ν c : M₃)) cV
  τ_inj : Function.Injective τ
  lev_τ : ∀ g B, lev g * τ B * (lev g)⁻¹ =
    τ (Multiplicative.ofAdd (symThreeCongr g (Multiplicative.toAdd B)))
  C_Jh : C ≤ Jh
  E_Jh : E ≤ Jh
  E_sq : ∀ x ∈ E, x * x = 1
  E_cent : ∀ x ∈ Jh, ∀ e ∈ E, x * e = e * x
  card_E : Nat.card E = 512
  z_Jh : ∀ x ∈ Jh, z * x * z⁻¹ ∈ Jh
  z_E : ∀ e ∈ E, ∃ B : 𝕊, symThreeDiag (B : M₃) = 0 ∧
    z * e * z⁻¹ * e⁻¹ = τ (Multiplicative.ofAdd B)
  C_sq : ∀ c ∈ C, c * c = τ (Multiplicative.ofAdd (sqS (symThreeDiag (ν c : M₃))))
  C_comm : ∀ c ∈ C, ∀ d ∈ C, c⁻¹ * d⁻¹ * c * d = τ (Multiplicative.ofAdd
    (symThreePolarSym (symThreeDiag (ν c : M₃)) (symThreeDiag (ν d : M₃))))
  δ_surj : ∀ w, ∃ c ∈ C, symThreeDiag (ν c : M₃) = w

open Classical in
@[expose] def lift (Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) (p : 𝔽 × 𝔽) : G :=
  if h : ∃ x ∈ Jh, cV x = p then h.choose else 1

@[expose] def cm (a b : G) : G := a⁻¹ * b⁻¹ * a * b

@[expose] def bf (Jh : Subgroup G) (cV : G → 𝔽 × 𝔽) (p q : 𝔽 × 𝔽) : G :=
  cm (lift Jh cV p) (lift Jh cV q)

theorem pvec_add_self (p : 𝔽 × 𝔽) : p + p = 0 :=
  Prod.ext (vec_add_self p.1) (vec_add_self p.2)

theorem conj_cm (g a b : G) : g * cm a b * g⁻¹ = cm (g * a * g⁻¹) (g * b * g⁻¹) := by
  simp only [cm]
  group

theorem cm_inv (a b : G) : (cm a b)⁻¹ = cm b a := by
  simp only [cm]
  group

namespace ECBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {C E Jh : Subgroup G} {cV : G → 𝔽 × 𝔽}

theorem lift_mem (h : ECBase τ lev z ν C E Jh cV) (p : 𝔽 × 𝔽) : lift Jh cV p ∈ Jh := by
  have hex := h.vc.surj p
  rw [lift, dite_eq_left hex]
  exact hex.choose_spec.1

theorem cV_lift (h : ECBase τ lev z ν C E Jh cV) (p : 𝔽 × 𝔽) : cV (lift Jh cV p) = p := by
  have hex := h.vc.surj p
  rw [lift, dite_eq_left hex]
  exact hex.choose_spec.2

theorem cV_one (h : ECBase τ lev z ν C E Jh cV) : cV 1 = 0 :=
  (h.vc.eq_zero 1 (one_mem _)).2 (one_mem _)

theorem cV_inv (h : ECBase τ lev z ν C E Jh cV) {x : G} (hx : x ∈ Jh) : cV x⁻¹ = cV x := by
  have h1 := h.vc.mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.cV_one] at h1
  have h2 : cV x⁻¹ = cV x + (cV x + cV x⁻¹) := by rw [← add_assoc, pvec_add_self, zero_add]
  rw [h2, ← h1, add_zero]

theorem mem_E_of_cV_eq (h : ECBase τ lev z ν C E Jh cV) {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh)
    (hxy : cV x = cV y) : x⁻¹ * y ∈ E := by
  refine (h.vc.eq_zero _ (mul_mem (inv_mem hx) hy)).1 ?_
  rw [h.vc.mul _ (inv_mem hx) _ hy, h.cV_inv hx, hxy, pvec_add_self]

theorem E_comm (h : ECBase τ lev z ν C E Jh cV) {e e' : G} (he : e ∈ E) (he' : e' ∈ E) :
    e * e' = e' * e :=
  h.E_cent e (h.E_Jh he) e' he'

theorem E_inv (h : ECBase τ lev z ν C E Jh cV) {e : G} (he : e ∈ E) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (h.E_sq e he)

theorem sq_mem_E (h : ECBase τ lev z ν C E Jh cV) {x : G} (hx : x ∈ Jh) : x * x ∈ E := by
  refine (h.vc.eq_zero _ (mul_mem hx hx)).1 ?_
  rw [h.vc.mul _ hx _ hx, pvec_add_self]

theorem cV_C (h : ECBase τ lev z ν C E Jh cV) {c : G} (hc : c ∈ C) :
    cV c = (symThreeDiag (ν c : M₃), 0) :=
  h.vc.on_C₂ c hc

theorem cm_mem_E (h : ECBase τ lev z ν C E Jh cV) {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) :
    cm x y ∈ E := by
  have h1 : x⁻¹ * y⁻¹ ∈ Jh := mul_mem (inv_mem hx) (inv_mem hy)
  have h2 : x⁻¹ * y⁻¹ * x ∈ Jh := mul_mem h1 hx
  refine (h.vc.eq_zero _ (mul_mem h2 hy)).1 ?_
  rw [h.vc.mul _ h2 _ hy, h.vc.mul _ h1 _ hx, h.vc.mul _ (inv_mem hx) _ (inv_mem hy),
    h.cV_inv hx, h.cV_inv hy]
  calc cV x + cV y + cV x + cV y = (cV x + cV x) + (cV y + cV y) := by abel
    _ = 0 := by rw [pvec_add_self, pvec_add_self, add_zero]

theorem cm_mul_E_left (h : ECBase τ lev z ν C E Jh cV) {x y e : G} (hx : x ∈ Jh) (hy : y ∈ Jh)
    (he : e ∈ E) : cm (x * e) y = cm x y := by
  have hey : e * y = y * e := (h.E_cent y hy e he).symm
  have hce : cm x y * e = e * cm x y := h.E_comm (h.cm_mem_E hx hy) he
  calc cm (x * e) y = e⁻¹ * (x⁻¹ * y⁻¹ * x * (e * y)) := by simp only [cm]; group
    _ = e⁻¹ * (cm x y * e) := by rw [hey]; simp only [cm]; group
    _ = cm x y := by rw [hce]; group

theorem cm_mul_E_right (h : ECBase τ lev z ν C E Jh cV) {x y e : G} (hx : x ∈ Jh) (hy : y ∈ Jh)
    (he : e ∈ E) : cm x (y * e) = cm x y := by
  have hxe : x⁻¹ * e⁻¹ = e⁻¹ * x⁻¹ := h.E_cent _ (inv_mem hx) _ (inv_mem he)
  have hce : cm x y * e = e * cm x y := h.E_comm (h.cm_mem_E hx hy) he
  calc cm x (y * e) = x⁻¹ * e⁻¹ * (y⁻¹ * x * y * e) := by simp only [cm]; group
    _ = e⁻¹ * (cm x y * e) := by rw [hxe]; simp only [cm]; group
    _ = cm x y := by rw [hce]; group

theorem cm_eq_of_cV (h : ECBase τ lev z ν C E Jh cV) {x x' y y' : G} (hx : x ∈ Jh)
    (hx' : x' ∈ Jh) (hy : y ∈ Jh) (hy' : y' ∈ Jh) (h1 : cV x = cV x') (h2 : cV y = cV y') :
    cm x y = cm x' y' := by
  have e1 := h.mem_E_of_cV_eq hx hx' h1
  have e2 := h.mem_E_of_cV_eq hy hy' h2
  calc cm x y = cm (x * (x⁻¹ * x')) (y * (y⁻¹ * y')) := by
        rw [h.cm_mul_E_right (mul_mem hx (mul_mem (inv_mem hx) hx')) hy e2,
          h.cm_mul_E_left hx hy e1]
    _ = cm x' y' := by rw [mul_inv_cancel_left, mul_inv_cancel_left]

theorem cm_eq_bf (h : ECBase τ lev z ν C E Jh cV) {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) :
    cm x y = bf Jh cV (cV x) (cV y) :=
  h.cm_eq_of_cV hx (h.lift_mem _) hy (h.lift_mem _) (h.cV_lift _).symm (h.cV_lift _).symm

theorem bf_mem (h : ECBase τ lev z ν C E Jh cV) (p q : 𝔽 × 𝔽) : bf Jh cV p q ∈ E :=
  h.cm_mem_E (h.lift_mem p) (h.lift_mem q)

theorem cm_mul_left (h : ECBase τ lev z ν C E Jh cV) {x x' y : G} (hx : x ∈ Jh) (hx' : x' ∈ Jh)
    (hy : y ∈ Jh) : cm (x * x') y = cm x y * cm x' y := by
  have hc : x'⁻¹ * cm x y = cm x y * x'⁻¹ := h.E_cent _ (inv_mem hx') _ (h.cm_mem_E hx hy)
  calc cm (x * x') y = x'⁻¹ * cm x y * (y⁻¹ * x' * y) := by simp only [cm]; group
    _ = cm x y * cm x' y := by rw [hc]; simp only [cm]; group

theorem cm_mul_right (h : ECBase τ lev z ν C E Jh cV) {x y y' : G} (hx : x ∈ Jh) (hy : y ∈ Jh)
    (hy' : y' ∈ Jh) : cm x (y * y') = cm x y * cm x y' := by
  have hc : cm x y * y' = y' * cm x y := (h.E_cent _ hy' _ (h.cm_mem_E hx hy)).symm
  calc cm x (y * y') = cm x y' * (y'⁻¹ * (cm x y * y')) := by simp only [cm]; group
    _ = cm x y' * cm x y := by rw [hc]; group
    _ = cm x y * cm x y' := h.E_comm (h.cm_mem_E hx hy') (h.cm_mem_E hx hy)

theorem bf_add_left (h : ECBase τ lev z ν C E Jh cV) (p p' q : 𝔽 × 𝔽) :
    bf Jh cV (p + p') q = bf Jh cV p q * bf Jh cV p' q := by
  have hm := mul_mem (h.lift_mem p) (h.lift_mem p')
  have hc : cV (lift Jh cV p * lift Jh cV p') = p + p' := by
    rw [h.vc.mul _ (h.lift_mem p) _ (h.lift_mem p'), h.cV_lift, h.cV_lift]
  rw [bf, ← h.cm_eq_of_cV hm (h.lift_mem _) (h.lift_mem q) (h.lift_mem q)
    (by rw [hc, h.cV_lift]) rfl, h.cm_mul_left (h.lift_mem p) (h.lift_mem p') (h.lift_mem q)]
  rfl

theorem bf_add_right (h : ECBase τ lev z ν C E Jh cV) (p q q' : 𝔽 × 𝔽) :
    bf Jh cV p (q + q') = bf Jh cV p q * bf Jh cV p q' := by
  have hm := mul_mem (h.lift_mem q) (h.lift_mem q')
  have hc : cV (lift Jh cV q * lift Jh cV q') = q + q' := by
    rw [h.vc.mul _ (h.lift_mem q) _ (h.lift_mem q'), h.cV_lift, h.cV_lift]
  rw [bf, ← h.cm_eq_of_cV (h.lift_mem p) (h.lift_mem p) hm (h.lift_mem _) rfl
    (by rw [hc, h.cV_lift]), h.cm_mul_right (h.lift_mem p) (h.lift_mem q) (h.lift_mem q')]
  rfl

theorem bf_zero_left (h : ECBase τ lev z ν C E Jh cV) (q : 𝔽 × 𝔽) : bf Jh cV 0 q = 1 := by
  have h1 := h.bf_add_left 0 0 q
  rw [add_zero] at h1
  calc bf Jh cV 0 q = (bf Jh cV 0 q)⁻¹ * (bf Jh cV 0 q * bf Jh cV 0 q) := by group
    _ = 1 := by rw [← h1, inv_mul_cancel]

theorem bf_zero_right (h : ECBase τ lev z ν C E Jh cV) (p : 𝔽 × 𝔽) : bf Jh cV p 0 = 1 := by
  have h1 := h.bf_add_right p 0 0
  rw [add_zero] at h1
  calc bf Jh cV p 0 = (bf Jh cV p 0)⁻¹ * (bf Jh cV p 0 * bf Jh cV p 0) := by group
    _ = 1 := by rw [← h1, inv_mul_cancel]

theorem bf_comm (h : ECBase τ lev z ν C E Jh cV) (p q : 𝔽 × 𝔽) :
    bf Jh cV q p = bf Jh cV p q := by
  rw [bf, ← cm_inv]
  exact h.E_inv (h.bf_mem p q)

theorem sq_mul (h : ECBase τ lev z ν C E Jh cV) {x y : G} (hx : x ∈ Jh) (hy : y ∈ Jh) :
    x * y * (x * y) = x * x * (y * y) * cm y x := by
  have hc : cm y x * y = y * cm y x := (h.E_cent _ hy _ (h.cm_mem_E hy hx)).symm
  calc x * y * (x * y) = x * x * y * (cm y x * y) := by simp only [cm]; group
    _ = x * x * (y * y) * cm y x := by rw [hc]; group

end ECBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.ECoords
