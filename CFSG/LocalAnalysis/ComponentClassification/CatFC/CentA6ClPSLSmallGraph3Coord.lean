module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSplit

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmallGraph3

open Subgroup Matrix
open CFSG.RankThree.PartOne.KCOrthogonalDescent

section HypCoord

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}
  (H : HypSplit Q 1 1)

abbrev Idx : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

theorem Q_eq_coord (v : W) :
    Q v = H.b.equivFun v (.inl 0) * H.b.equivFun v (.inr (.inl 0)) +
      Q (H.b (.inr (.inr 0))) * H.b.equivFun v (.inr (.inr 0)) ^ 2 := by
  have h := H.Q_vec (fun i => H.b.repr v (.inl i)) (fun i => H.b.repr v (.inr (.inl i)))
    (fun j => H.b.repr v (.inr (.inr j)))
  rw [H.vec_repr] at h
  rw [h]
  simp only [HypSplit.vec]
  simp [QuadraticMap.map_smul]
  ring

@[expose] noncomputable def coordAut (L : (Idx → K) ≃ₗ[K] (Idx → K)) : W ≃ₗ[K] W :=
  H.b.equivFun.trans (L.trans H.b.equivFun.symm)

theorem equivFun_coordAut (L : (Idx → K) ≃ₗ[K] (Idx → K)) (v : W) :
    H.b.equivFun (coordAut H L v) = L (H.b.equivFun v) := by
  change H.b.equivFun (H.b.equivFun.symm (L (H.b.equivFun v))) = _
  exact LinearEquiv.apply_symm_apply _ _

@[expose] noncomputable def coordAutHom : ((Idx → K) ≃ₗ[K] (Idx → K)) →* (W ≃ₗ[K] W) where
  toFun := coordAut H
  map_one' := by
    ext v
    change H.b.equivFun.symm (H.b.equivFun v) = v
    exact LinearEquiv.symm_apply_apply _ _
  map_mul' L₁ L₂ := by
    ext v
    change H.b.equivFun.symm (L₁ (L₂ (H.b.equivFun v))) =
      H.b.equivFun.symm (L₁ (H.b.equivFun (H.b.equivFun.symm (L₂ (H.b.equivFun v)))))
    rw [LinearEquiv.apply_symm_apply]

theorem Q_coordAut (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (hL : ∀ c : Idx → K, L c (.inl 0) * L c (.inr (.inl 0)) +
        Q (H.b (.inr (.inr 0))) * L c (.inr (.inr 0)) ^ 2 =
      c (.inl 0) * c (.inr (.inl 0)) + Q (H.b (.inr (.inr 0))) * c (.inr (.inr 0)) ^ 2)
    (v : W) : Q (coordAut H L v) = Q v := by
  rw [Q_eq_coord H (coordAut H L v), Q_eq_coord H v, equivFun_coordAut]
  exact hL _

end HypCoord

section Diag

variable {K : Type} [Field K]

@[expose] noncomputable def diagAut : (Idx → Kˣ) →* ((Idx → K) ≃ₗ[K] (Idx → K)) where
  toFun w :=
    { toFun := fun c i => (w i : K) * c i
      map_add' := fun c d => by ext i; simp [mul_add]
      map_smul' := fun a c => by ext i; simp [mul_left_comm]
      invFun := fun c i => ((w i)⁻¹ : Kˣ) * c i
      left_inv := fun c => by
        ext i
        simp [← mul_assoc]
      right_inv := fun c => by
        ext i
        simp [← mul_assoc] }
  map_one' := by ext c i; simp
  map_mul' w₁ w₂ := by ext c i; simp [mul_assoc]

theorem diagAut_apply (w : Idx → Kˣ) (c : Idx → K) (i : Idx) : diagAut w c i = (w i : K) * c i :=
  rfl

@[expose] def diagW (a : Kˣ) : Idx → Kˣ :=
  Sum.elim (fun _ => a) (Sum.elim (fun _ => a⁻¹) (fun _ => 1))

@[expose] noncomputable def swapAut : (Idx → K) ≃ₗ[K] (Idx → K) :=
  (LinearEquiv.funCongrLeft K K (Equiv.swap (Sum.inl (0 : Fin 1) : Idx)
    (Sum.inr (Sum.inl 0)))).trans (LinearEquiv.neg K)

theorem swapAut_apply (c : Idx → K) (i : Idx) :
    swapAut c i = -c (Equiv.swap (Sum.inl (0 : Fin 1) : Idx) (Sum.inr (Sum.inl 0)) i) := by
  simp [swapAut]

theorem idx_cases (P : Idx → Prop) (h1 : P (.inl 0)) (h2 : P (.inr (.inl 0)))
    (h3 : P (.inr (.inr 0))) : ∀ i, P i := by
  intro i
  rcases i with i | i | i
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h1
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h2
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h3

theorem swapIdx_inl :
    Equiv.swap (Sum.inl (0 : Fin 1) : Idx) (Sum.inr (Sum.inl 0)) (Sum.inl 0) =
      Sum.inr (Sum.inl 0) :=
  Equiv.swap_apply_left _ _

theorem swapIdx_inr_inl :
    Equiv.swap (Sum.inl (0 : Fin 1) : Idx) (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)) =
      Sum.inl 0 :=
  Equiv.swap_apply_right _ _

theorem swapIdx_inr_inr :
    Equiv.swap (Sum.inl (0 : Fin 1) : Idx) (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inr 0)) =
      Sum.inr (Sum.inr 0) :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

theorem swapAut_mul_self : (swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) * swapAut = 1 := by
  ext c i
  refine idx_cases (fun i => ((swapAut * swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) c) i =
    (1 : (Idx → K) ≃ₗ[K] (Idx → K)) c i) ?_ ?_ ?_ i
  all_goals simp [swapAut_apply, swapIdx_inl, swapIdx_inr_inl, swapIdx_inr_inr]

theorem diagW_pow (a : Kˣ) (k : ℕ) : (diagW a) ^ k = diagW (a ^ k) := by
  funext i
  refine idx_cases (fun i => ((diagW a) ^ k) i = diagW (a ^ k) i) ?_ ?_ ?_ i
  all_goals simp [diagW]

theorem swap_diag_swap (a : Kˣ) :
    (swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) * diagAut (diagW a) * swapAut =
      (diagAut (diagW a))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  ext c i
  refine idx_cases (fun i => (((swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) * diagAut (diagW a) *
    swapAut * diagAut (diagW a) : (Idx → K) ≃ₗ[K] (Idx → K)) c) i =
    (1 : (Idx → K) ≃ₗ[K] (Idx → K)) c i) ?_ ?_ ?_ i
  all_goals simp [swapAut_apply, swapIdx_inl, swapIdx_inr_inl, swapIdx_inr_inr, diagAut_apply,
    diagW]

end Diag

section Elements

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}
  (H : HypSplit Q 1 1)

theorem coordAut_diag_mem (a : Kˣ) :
    coordAut H (diagAut (diagW a)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  refine Q_coordAut H _ (fun c => ?_)
  simp only [diagAut_apply, diagW, Sum.elim_inl, Sum.elim_inr, Units.val_one]
  have : (a : K) * (a⁻¹ : Kˣ) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination (c (.inl 0) * c (.inr (.inl 0))) * this

theorem coordAut_swap_mem :
    coordAut H (swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  refine Q_coordAut H _ (fun c => ?_)
  simp only [swapAut_apply, swapIdx_inl, swapIdx_inr_inl, swapIdx_inr_inr]
  ring

@[expose] noncomputable def zElt (a : Kˣ) : TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨coordAut H (diagAut (diagW a)), coordAut_diag_mem H a⟩

@[expose] noncomputable def tElt : TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨coordAut H (swapAut : (Idx → K) ≃ₗ[K] (Idx → K)), coordAut_swap_mem H⟩

theorem zElt_pow (a : Kˣ) (k : ℕ) :
    ((zElt H a ^ k : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) =
      coordAutHom H (diagAut (diagW (a ^ k))) := by
  rw [Subgroup.coe_pow, ← diagW_pow, map_pow, map_pow]
  rfl

theorem zElt_pow_eq_one {a : Kˣ} {k : ℕ} (hk : a ^ k = 1) : zElt H a ^ k = 1 := by
  apply Subtype.ext
  rw [zElt_pow, hk]
  have : diagW (1 : Kˣ) = 1 := by
    funext i
    refine idx_cases (fun i => diagW (1 : Kˣ) i = (1 : Idx → Kˣ) i) ?_ ?_ ?_ i
    all_goals simp [diagW]
  rw [this, map_one, map_one]
  rfl

theorem tElt_mul_self : tElt H * tElt H = (1 : TauCeti.QuadraticMap.orthogonalGroup Q) := by
  apply Subtype.ext
  change coordAutHom H swapAut * coordAutHom H swapAut = 1
  rw [← map_mul, swapAut_mul_self, map_one]

theorem tElt_conj (a : Kˣ) : tElt H * zElt H a * (tElt H)⁻¹ = (zElt H a)⁻¹ := by
  have ht : (tElt H)⁻¹ = tElt H := (inv_eq_of_mul_eq_one_right (tElt_mul_self H)).symm.symm
  rw [ht]
  apply Subtype.ext
  change coordAutHom H swapAut * coordAutHom H (diagAut (diagW a)) * coordAutHom H swapAut =
    (coordAutHom H (diagAut (diagW a)))⁻¹
  rw [← map_mul, ← map_mul, swap_diag_swap, map_inv]

end Elements

section NonScalar

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}
  (H : HypSplit Q 1 1)

theorem zElt_pow_eq (a : Kˣ) (k : ℕ) : zElt H a ^ k = zElt H (a ^ k) :=
  Subtype.ext (zElt_pow H a k)

theorem zElt_apply_inl (a : Kˣ) :
    (zElt H a : W ≃ₗ[K] W) (H.b (.inl 0)) = (a : K) • H.b (.inl 0) := by
  apply H.b.equivFun.injective
  change H.b.equivFun (coordAut H (diagAut (diagW a)) (H.b (.inl 0))) = _
  rw [equivFun_coordAut, map_smul]
  funext i
  refine idx_cases (fun i => diagAut (diagW a) (H.b.equivFun (H.b (.inl 0))) i =
    ((a : K) • H.b.equivFun (H.b (.inl 0))) i) ?_ ?_ ?_ i
  all_goals simp [diagAut_apply, diagW, Module.Basis.equivFun_self]

theorem zElt_apply_tail (a : Kˣ) :
    (zElt H a : W ≃ₗ[K] W) (H.b (.inr (.inr 0))) = H.b (.inr (.inr 0)) := by
  apply H.b.equivFun.injective
  change H.b.equivFun (coordAut H (diagAut (diagW a)) (H.b (.inr (.inr 0)))) = _
  rw [equivFun_coordAut]
  funext i
  refine idx_cases (fun i => diagAut (diagW a) (H.b.equivFun (H.b (.inr (.inr 0)))) i =
    H.b.equivFun (H.b (.inr (.inr 0))) i) ?_ ?_ ?_ i
  all_goals simp [diagAut_apply, diagW, Module.Basis.equivFun_self]

theorem zElt_not_scalar [Nontrivial K] {a : Kˣ} (ha : a ≠ 1) (c : K)
    (hc : ∀ v, (zElt H a : W ≃ₗ[K] W) v = c • v) : False := by
  have h1 := hc (H.b (.inl 0))
  have h2 := hc (H.b (.inr (.inr 0)))
  rw [zElt_apply_inl] at h1
  rw [zElt_apply_tail] at h2
  have hc1 : c = 1 := by
    have h3 : (1 - c) • H.b (.inr (.inr 0)) = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    have := (smul_eq_zero.mp h3).resolve_right (H.b.ne_zero _)
    linear_combination -this
  have h4 : ((a : K) - c) • H.b (.inl 0) = 0 := by rw [sub_smul, h1, sub_self]
  have h5 := (smul_eq_zero.mp h4).resolve_right (H.b.ne_zero _)
  apply ha
  apply Units.ext
  rw [Units.val_one]
  linear_combination h5 + hc1

theorem tElt_apply_inl :
    H.b.equivFun ((tElt H : W ≃ₗ[K] W) (H.b (.inl 0))) (.inr (.inl 0)) = -1 := by
  change H.b.equivFun (coordAut H (swapAut : (Idx → K) ≃ₗ[K] (Idx → K)) (H.b (.inl 0)))
    (.inr (.inl 0)) = _
  rw [equivFun_coordAut, swapAut_apply, swapIdx_inr_inl, Module.Basis.equivFun_self]
  simp

theorem tElt_not_scalar (c : K) (hc : ∀ v, (tElt H : W ≃ₗ[K] W) v = c • v) : False := by
  have h1 := hc (H.b (.inl 0))
  have h2 := tElt_apply_inl H
  rw [h1, map_smul] at h2
  simp [Module.Basis.equivFun_self] at h2

end NonScalar

end CFSG.ComponentClassification.CatFC.PSLSmallGraph3
