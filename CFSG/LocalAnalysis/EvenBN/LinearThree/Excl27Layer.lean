module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Graph
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Singer

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace Layer

variable {H : Type*} [Group H] {E : Subgroup H} [E.Normal] {K : Type} [Field K]
  {Y : Type*} [Group Y]

@[expose] noncomputable def layerAut (η : E ≃* Y) : H →* MulAut Y :=
  (MulAut.congr η).toMonoidHom.comp MulAut.conjNormal

theorem coe_symm_layerAut_apply (η : E ≃* Y) (h : H) (p : Y) :
    ((η.symm (layerAut η h p) : E) : H) = h * (η.symm p : H) * h⁻¹ := by
  simp [layerAut, MulAut.congr_apply, MulAut.conjNormal_apply]

theorem layerAut_eq_conj (η : E ≃* Y) (e : E) :
    layerAut η (e : H) = MulAut.conj (η e) := by
  ext p
  apply η.symm.injective
  apply Subtype.ext
  rw [coe_symm_layerAut_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

theorem layerAut_apply (η : E ≃* Y) (h : H) (e : E) :
    layerAut η h (η e) = η ⟨h * e * h⁻¹, (inferInstance : E.Normal).conj_mem _ e.2 h⟩ := by
  apply η.symm.injective
  apply Subtype.ext
  rw [coe_symm_layerAut_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem layerAut_injective (η : E ≃* Y)
    (hfaith : ∀ h : H, (∀ e ∈ E, h⁻¹ * e * h = e) → h = 1) :
    Function.Injective (layerAut η : H → MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro h h1
  apply hfaith
  intro e he
  have hc : ∀ e' ∈ E, h * e' * h⁻¹ = e' := by
    intro e' he'
    have h2 := layerAut_apply η h ⟨e', he'⟩
    rw [h1, MulAut.one_apply] at h2
    exact (congrArg Subtype.val (η.injective h2)).symm
  have h3 := hc (h⁻¹ * e * h) (by simpa using (inferInstance : E.Normal).conj_mem e he h⁻¹)
  calc h⁻¹ * e * h = h * (h⁻¹ * e * h) * h⁻¹ := h3.symm
    _ = e := by group

variable {f : ℕ}

@[expose] noncomputable def imageJ (η : E ≃* Y) (J : Subgroup H) : Subgroup Y :=
  (J.subgroupOf E).map η.toMonoidHom

omit [E.Normal] in
theorem nonempty_imageJ_equiv (η : E ≃* Y) {J : Subgroup H} (hJE : J ≤ E)
    {S : Type*} [Group S] (hJ : Nonempty (J ≃* S)) : Nonempty (imageJ η J ≃* S) := by
  obtain ⟨e⟩ := hJ
  exact ⟨((J.subgroupOf E).equivMapOfInjective η.toMonoidHom η.injective).symm.trans
    ((subgroupOfEquivOfLe hJE).trans e)⟩

theorem layerAut_fix_imageJ (η : E ≃* Y) {J : Subgroup H} {x : H}
    (hx : ∀ j ∈ J, x * j = j * x) : ∀ p ∈ imageJ η J, layerAut η x p = p := by
  rintro _ ⟨e, he, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, layerAut_apply]
  congr 1
  apply Subtype.ext
  change x * (e : H) * x⁻¹ = e
  rw [hx e (mem_subgroupOf.mp he), mul_inv_cancel_right]

structure Data (H : Type*) [Group H] (E : Subgroup H) [E.Normal] (K : Type) [Field K]
    [Finite K] (f : ℕ) where
  η : E ≃* projectiveSL 3 K
  three_le : 3 ≤ f
  card : Nat.card K = 2 ^ f
  faith : ∀ h : H, (∀ e ∈ E, h⁻¹ * e * h = e) → h = 1
  t : H
  orderOf_t : orderOf t = 2
  J : Subgroup H
  J_le : J ≤ E
  J_equiv : Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) K)
  t_comm : ∀ j ∈ J, t * j = j * t

namespace Data

variable [Finite K] (D : Data H E K f)

theorem injective : Function.Injective (layerAut D.η : H → MulAut (projectiveSL 3 K)) :=
  layerAut_injective D.η D.faith

theorem orderOf_y : orderOf (layerAut D.η D.t) = 2 := by
  rw [orderOf_injective _ D.injective, D.orderOf_t]

theorem y_sq : layerAut D.η D.t ^ 2 = 1 := by
  rw [← D.orderOf_y]
  exact pow_orderOf_eq_one _

theorem type :
    layerAut D.η D.t ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      ∃ γ : MulAut (projectiveSL 3 K), layerAut D.η D.t = γ * dualAut 3 K * γ⁻¹ :=
  exists_eq_conj_dualAut D.three_le D.card D.orderOf_y
    (nonempty_imageJ_equiv D.η D.J_le D.J_equiv) (layerAut_fix_imageJ D.η D.t_comm)

theorem t_inv : D.t⁻¹ = D.t := by
  have h := pow_orderOf_eq_one D.t
  rw [D.orderOf_t, sq] at h
  exact inv_eq_of_mul_eq_one_right h

theorem exists_conj_eq_mul {z : H} (hz : z ∈ E) (htz : (D.t * z) ^ 2 = 1) :
    ∃ m ∈ E, m * D.t * m⁻¹ = D.t * z := by
  set y := layerAut D.η D.t with hy
  have hΦz : layerAut D.η z = MulAut.conj (D.η ⟨z, hz⟩) := layerAut_eq_conj D.η ⟨z, hz⟩
  have hp : (y * MulAut.conj (D.η ⟨z, hz⟩)) ^ 2 = 1 := by
    rw [hy, ← hΦz, ← map_mul, ← map_pow, htz, map_one]
  obtain ⟨b, hb⟩ := exists_conj_eq_mul_conj_of_not_mem_range (by have := D.three_le; omega)
    D.card D.y_sq D.type.1 hp
  refine ⟨(D.η.symm b : H), (D.η.symm b).2, D.injective ?_⟩
  have hΦm : layerAut D.η (D.η.symm b : H) = MulAut.conj b := by
    rw [layerAut_eq_conj, MulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, map_inv, hΦm, map_mul, hΦz, ← hy, hb]

theorem eq_one_of_commute {x : H} (hxt : x * D.t = D.t * x) (hxJ : ∀ j ∈ D.J, x * j = j * x)
    (hx : Odd (orderOf x)) : x = 1 := by
  obtain ⟨-, γ, hγ⟩ := D.type
  apply D.injective
  rw [map_one]
  refine eq_one_of_commute_conj_dualAut (by have := D.three_le; omega) D.card γ
    (nonempty_imageJ_equiv D.η D.J_le D.J_equiv) ?_ ?_ (layerAut_fix_imageJ D.η hxJ) ?_
  · rw [← hγ]
    exact layerAut_fix_imageJ D.η D.t_comm
  · rw [← hγ, ← map_mul, ← map_mul, hxt]
  · rwa [orderOf_injective _ D.injective]

theorem exists_orderOf_conj_mul_eq {r : ℕ} (hr : r.Prime) (h1 : ¬ r ∣ Nat.card K - 1)
    (h2 : ¬ r ∣ Nat.card K ^ 2 - 1) (h3 : r ∣ Nat.card K ^ 3 - 1) :
    ∃ m ∈ E, orderOf (m * D.t * m⁻¹ * D.t) = r := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two
    (by have := D.three_le; omega) D.card
  obtain ⟨-, γ, hγ⟩ := D.type
  obtain ⟨q', hq'r, hq'δ⟩ := exists_orderOf_eq_dualAut_eq_inv (by have := D.three_le; omega)
    D.card hr h1 h2 h3
  set y := layerAut D.η D.t with hy
  set q := γ q' with hq
  have hyq : y q = q⁻¹ := by
    rw [hγ, MulAut.mul_apply, MulAut.mul_apply, hq, MulAut.inv_apply_self, hq'δ, map_inv]
  set s : H := (D.η.symm q : H) with hs
  have hsE : s ∈ E := (D.η.symm q).2
  have hts : D.t * s * D.t⁻¹ = s⁻¹ := by
    have h := layerAut_apply D.η D.t (D.η.symm q)
    rw [MulEquiv.apply_symm_apply, ← hy, hyq] at h
    have h' := congrArg (fun p => ((D.η.symm p : E) : H)) h
    simp only [MulEquiv.symm_apply_apply] at h'
    rw [map_inv] at h'
    exact h'.symm.trans (by simp [hs])
  have htinv := D.t_inv
  have h4 : D.t * s⁻¹ * D.t⁻¹ = s := by
    calc D.t * s⁻¹ * D.t⁻¹ = (D.t * s * D.t⁻¹)⁻¹ := by group
      _ = s := by rw [hts, inv_inv]
  have hinv : (D.t * s⁻¹) ^ 2 = 1 := by
    calc (D.t * s⁻¹) ^ 2 = D.t * s⁻¹ * D.t⁻¹ * s⁻¹ := by rw [sq, htinv]; group
      _ = s * s⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel s
  obtain ⟨m, hmE, hm⟩ := D.exists_conj_eq_mul (inv_mem hsE) hinv
  refine ⟨m, hmE, ?_⟩
  have hms : m * D.t * m⁻¹ * D.t = s := by
    rw [hm]
    calc D.t * s⁻¹ * D.t = D.t * s⁻¹ * D.t⁻¹ := by rw [htinv]
      _ = s := h4
  rw [hms, hs, show ((D.η.symm q : E) : H) = E.subtype (D.η.symm q) from rfl,
    orderOf_injective E.subtype E.subtype_injective, MulEquiv.orderOf_eq, hq,
    MulEquiv.orderOf_eq, hq'r]

end Data

end Layer

end CFSG.LocalAnalysis.EvenBN.LinearThree
