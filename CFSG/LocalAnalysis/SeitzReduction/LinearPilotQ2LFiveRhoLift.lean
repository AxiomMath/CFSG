module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer CFSG.LieType.Steinberg.CentralExt.SLClosed

structure RhoExt (E : Type*) [Group E] where
  π : E →* SpecialLinearGroup (Fin 4) F4
  surj : Function.Surjective π
  β : π.ker → Fin 4 → F4
  bij : Function.Bijective β
  β_mul : ∀ v w : π.ker, β (v * w) = β v + β w
  conj : ∀ (e : E) (w v : π.ker), (v : E) = e * w * e⁻¹ →
    β v = (π e : Matrix (Fin 4) (Fin 4) F4) *ᵥ β w
  τ : E →* E
  τ_τ : ∀ e, τ (τ e) = e
  π_τ : ∀ e, π (τ e) = veeFrob (π e)

namespace RhoExt

variable {E : Type*} [Group E] (X : RhoExt E)

@[expose] noncomputable def βE (x : E) : Fin 4 → F4 :=
  if h : x ∈ X.π.ker then X.β ⟨x, h⟩ else 0

theorem βE_of_mem {x : E} (hx : X.π x = 1) : X.βE x = X.β ⟨x, hx⟩ := dite_eq_left hx

theorem β_one : X.β 1 = 0 := by
  have h := X.β_mul 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem βE_one : X.βE 1 = 0 := by
  rw [X.βE_of_mem (map_one _)]
  exact X.β_one

theorem βE_mul {x y : E} (hx : X.π x = 1) (hy : X.π y = 1) :
    X.βE (x * y) = X.βE x + X.βE y := by
  rw [X.βE_of_mem hx, X.βE_of_mem hy, X.βE_of_mem (by rw [map_mul, hx, hy, one_mul])]
  exact X.β_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem βE_inv {x : E} (hx : X.π x = 1) : X.βE x⁻¹ = -X.βE x := by
  have hx' : X.π x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  have h := X.βE_mul hx' hx
  rw [inv_mul_cancel, X.βE_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem βE_conj (e : E) {x : E} (hx : X.π x = 1) :
    X.βE (e * x * e⁻¹) = (X.π e : Matrix (Fin 4) (Fin 4) F4) *ᵥ X.βE x := by
  have h' : X.π (e * x * e⁻¹) = 1 := by rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  rw [X.βE_of_mem hx, X.βE_of_mem h']
  exact X.conj e ⟨x, hx⟩ ⟨_, h'⟩ rfl

theorem eq_one_of_βE {x : E} (hx : X.π x = 1) (h0 : X.βE x = 0) : x = 1 := by
  rw [X.βE_of_mem hx, ← X.β_one] at h0
  exact congrArg Subtype.val (X.bij.1 h0)

theorem exists_βE (v : Fin 4 → F4) : ∃ x : E, X.π x = 1 ∧ X.βE x = v := by
  obtain ⟨w, hw⟩ := X.bij.2 v
  exact ⟨w, w.2, by rw [X.βE_of_mem w.2]; exact hw⟩

theorem βE_eq_zero_of_commute {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) {w : E} (hw1 : X.π w = 1)
    (hw : k * w = w * k) {r : Fin 4} (hr : d r ≠ 1) : X.βE w r = 0 := by
  have h := X.βE_conj k hw1
  rw [hw, mul_inv_cancel_right, hk] at h
  have h' := congrFun h r
  rw [mulVec_diagonal] at h'
  have h'' : (d r - 1) * X.βE w r = 0 := by rw [sub_mul, one_mul, ← h', sub_self]
  rcases mul_eq_zero.mp h'' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hr
  · exact h0

theorem eq_one_of_commute {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : ∀ r, d r ≠ 1) {w : E}
    (hw1 : X.π w = 1) (hw : k * w = w * k) : w = 1 :=
  X.eq_one_of_βE hw1 (funext fun r => X.βE_eq_zero_of_commute hk hw1 hw (hd r))

theorem eq_of_commute {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : ∀ r, d r ≠ 1) {y y' : E}
    (hyy : X.π y = X.π y') (hy : k * y = y * k) (hy' : k * y' = y' * k) : y = y' := by
  have h1 : X.π (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, hyy, inv_mul_cancel]
  have h2 : k * (y⁻¹ * y') = (y⁻¹ * y') * k :=
    (((show Commute k y from hy).inv_right).mul_right (show Commute k y' from hy')).eq
  have h3 := X.eq_one_of_commute hk hd h1 h2
  rw [inv_mul_eq_one] at h3
  exact h3

theorem eq_of_βE_eq {x y : E} (hx : X.π x = 1) (hy : X.π y = 1) (h : X.βE x = X.βE y) :
    x = y := by
  rw [X.βE_of_mem hx, X.βE_of_mem hy] at h
  exact congrArg Subtype.val (X.bij.1 h)

theorem exists_commute {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : ∀ r, d r ≠ 1) {x : E}
    (hx : X.π k * X.π x = X.π x * X.π k) : ∃ y : E, X.π y = X.π x ∧ k * y = y * k := by
  set w₁ := x⁻¹ * (k * x * k⁻¹) with hw₁
  have hw₁1 : X.π w₁ = 1 := by
    rw [hw₁, map_mul, map_inv, map_mul, map_mul, map_inv, hx, mul_inv_cancel_right,
      inv_mul_cancel]
  obtain ⟨w, hw1, hwv⟩ := X.exists_βE (fun r => X.βE w₁ r / (1 - d r))
  refine ⟨x * w, by rw [map_mul, hw1, mul_one], ?_⟩
  have hkw1 : X.π (k * w * k⁻¹) = 1 := by
    rw [map_mul, map_mul, hw1, mul_one, map_inv, mul_inv_cancel]
  have heq : w₁ * (k * w * k⁻¹) = w := by
    refine X.eq_of_βE_eq (by rw [map_mul, hw₁1, hkw1, one_mul]) hw1 ?_
    rw [X.βE_mul hw₁1 hkw1, X.βE_conj k hw1, hk, hwv]
    funext r
    simp only [Pi.add_apply, mulVec_diagonal]
    have hr : (1 : F4) - d r ≠ 0 := sub_ne_zero.mpr (Ne.symm (hd r))
    field_simp
    ring
  calc k * (x * w) = x * (w₁ * (k * w * k⁻¹)) * k := by rw [hw₁]; group
    _ = x * w * k := by rw [heq]

open scoped Classical in
@[expose] noncomputable def fixLift (k : E) (g : SpecialLinearGroup (Fin 4) F4) : E :=
  if h : ∃ y : E, X.π y = g ∧ k * y = y * k then h.choose else 1

theorem fixLift_spec {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : ∀ r, d r ≠ 1)
    {g : SpecialLinearGroup (Fin 4) F4} (hg : X.π k * g = g * X.π k) :
    X.π (X.fixLift k g) = g ∧ k * X.fixLift k g = X.fixLift k g * k := by
  obtain ⟨x, rfl⟩ := X.surj g
  have h : ∃ y : E, X.π y = X.π x ∧ k * y = y * k := X.exists_commute hk hd hg
  rw [fixLift, dite_eq_left h]
  exact h.choose_spec

theorem fixLift_eq {k : E} {d : Fin 4 → F4}
    (hk : (X.π k : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : ∀ r, d r ≠ 1)
    {g : SpecialLinearGroup (Fin 4) F4} {y : E} (hy : X.π y = g) (hyk : k * y = y * k) :
    X.fixLift k g = y := by
  have hg : X.π k * g = g * X.π k := by rw [← hy, ← map_mul, hyk, map_mul]
  obtain ⟨h1, h2⟩ := X.fixLift_spec hk hd hg
  exact X.eq_of_commute hk hd (by rw [h1, hy]) h2 hyk

end RhoExt

end CFSG.SeitzReduction.LinearPilot
