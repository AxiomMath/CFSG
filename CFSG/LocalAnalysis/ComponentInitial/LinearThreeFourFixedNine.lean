module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearThreeFourFixedNine

open Matrix LinearFlag

variable {k : Type*} [Field k]

@[expose] def dSL (p : kˣ × kˣ) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨diagonal ![(p.1 : k), p.2, ((p.1 * p.2)⁻¹ : kˣ)], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp
    field_simp⟩

theorem coe_dSL (p : kˣ × kˣ) : (dSL p : Matrix (Fin 3) (Fin 3) k) =
    diagonal ![(p.1 : k), p.2, ((p.1 * p.2)⁻¹ : kˣ)] :=
  rfl

@[expose] def dHom : kˣ × kˣ →* Matrix.SpecialLinearGroup (Fin 3) k where
  toFun := dSL
  map_one' := by
    apply Subtype.ext
    rw [coe_dSL, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  map_mul' p q := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_dSL, coe_dSL, coe_dSL, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
    ring

theorem coe_dHom (p : kˣ × kˣ) : (dHom p : Matrix (Fin 3) (Fin 3) k) =
    diagonal ![(p.1 : k), p.2, ((p.1 * p.2)⁻¹ : kˣ)] :=
  rfl

@[expose] def rSL : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [det_fin_three]⟩

theorem coe_rSL : ((rSL : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
    !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

@[expose] def rot (p : kˣ × kˣ) : kˣ × kˣ :=
  ((p.1 * p.2)⁻¹, p.1)

theorem rSL_mul_dHom (p : kˣ × kˣ) :
    (rSL : Matrix.SpecialLinearGroup (Fin 3) k) * dHom p = dHom (rot p) * rSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dHom, coe_dHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_rSL, rot, Matrix.mul_apply, diagonal]

theorem rSL_mul_dHom_mul (p : kˣ × kˣ) (x : Matrix.SpecialLinearGroup (Fin 3) k) :
    rSL * (dHom p * x) = dHom (rot p) * (rSL * x) := by
  rw [← mul_assoc, rSL_mul_dHom, mul_assoc]

theorem rSL_pow_three : (rSL : Matrix.SpecialLinearGroup (Fin 3) k) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem rSL_mul_rSL_mul_rSL : (rSL : Matrix.SpecialLinearGroup (Fin 3) k) * (rSL * rSL) = 1 := by
  rw [← pow_three, rSL_pow_three]

theorem rSL_mul_rSL_mul_rSL_mul (x : Matrix.SpecialLinearGroup (Fin 3) k) :
    rSL * (rSL * (rSL * x)) = x := by
  rw [← mul_assoc, ← mul_assoc, ← pow_three', rSL_pow_three, one_mul]

theorem rSL_inv : (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁻¹ = rSL * rSL := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three, rSL_pow_three]

theorem mul_rot_mul_rot_rot (p : kˣ × kˣ) : p * rot p * rot (rot p) = 1 := by
  ext
  · simp [rot]
  · simp [rot]
    field_simp

@[expose] def dSet : Set (Matrix.SpecialLinearGroup (Fin 3) k) :=
  {g | ∃ a b : kˣ, (g : Matrix (Fin 3) (Fin 3) k) = diagonal ![(a : k), b, ((a * b)⁻¹ : kˣ)]}

@[expose] def qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) :=
  Subgroup.closure (dSet ∪ {rSL})

theorem mem_dSet_iff {g : Matrix.SpecialLinearGroup (Fin 3) k} :
    g ∈ dSet ↔ ∃ p, dHom p = g := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨(a, b), Subtype.ext h.symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩

@[expose] def qElt (x : (kˣ × kˣ) × Fin 3) : Matrix.SpecialLinearGroup (Fin 3) k :=
  dHom x.1 * rSL ^ (x.2 : ℕ)

theorem rSL_mul_qElt (x : (kˣ × kˣ) × Fin 3) :
    (rSL : Matrix.SpecialLinearGroup (Fin 3) k) * qElt x = qElt (rot x.1, x.2 + 1) := by
  obtain ⟨p, i⟩ := x
  simp only [qElt]
  rw [← mul_assoc, rSL_mul_dHom, mul_assoc, ← pow_succ']
  fin_cases i
  · rfl
  · rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, Fin.val_zero, pow_zero]
    rw [rSL_pow_three]

theorem coe_qSub :
    (qSub (k := k) : Set (Matrix.SpecialLinearGroup (Fin 3) k)) = Set.range qElt := by
  apply le_antisymm
  · intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨((1 : kˣ × kˣ), (0 : Fin 3)), by simp [qElt]⟩
    | mul_left x hx y _ ih =>
      obtain ⟨⟨p, i⟩, rfl⟩ := ih
      rcases hx with hx | hx
      · obtain ⟨q, rfl⟩ := mem_dSet_iff.mp hx
        exact ⟨(q * p, i), by simp only [qElt, map_mul, mul_assoc]⟩
      · rw [Set.mem_singleton_iff.mp hx]
        exact ⟨_, (rSL_mul_qElt (p, i)).symm⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨⟨p, i⟩, rfl⟩ := ih
      rcases hx with hx | hx
      · obtain ⟨q, rfl⟩ := mem_dSet_iff.mp hx
        exact ⟨(q⁻¹ * p, i), by simp only [qElt, map_mul, map_inv, mul_assoc]⟩
      · rw [Set.mem_singleton_iff.mp hx, rSL_inv, mul_assoc, rSL_mul_qElt, rSL_mul_qElt]
        exact ⟨_, rfl⟩
  · rintro _ ⟨⟨p, i⟩, rfl⟩
    have hd : dHom p ∈ qSub (k := k) :=
      Subgroup.subset_closure (Or.inl (mem_dSet_iff.mpr ⟨p, rfl⟩))
    have hr : (rSL : Matrix.SpecialLinearGroup (Fin 3) k) ∈ qSub :=
      Subgroup.subset_closure (Or.inr rfl)
    exact mul_mem hd (pow_mem hr _)

theorem qElt_injective : Function.Injective (qElt (k := k)) := by
  rintro ⟨⟨a, b⟩, i⟩ ⟨⟨a', b'⟩, j⟩ h
  have hm := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
    (g : Matrix (Fin 3) (Fin 3) k)) h
  have e : ∀ r c, (qElt ((a, b), i) : Matrix (Fin 3) (Fin 3) k) r c =
      (qElt ((a', b'), j) : Matrix (Fin 3) (Fin 3) k) r c := fun r c =>
    congrFun (congrFun hm r) c
  have e0 := e 0 0
  have e1 := e 0 1
  have e2 := e 0 2
  have e3 := e 1 0
  have e4 := e 1 1
  have e5 := e 1 2
  fin_cases i <;> fin_cases j <;>
    simp [qElt, coe_dHom, coe_rSL, pow_succ, Matrix.mul_apply, diagonal] at e0 e1 e2 e3 e4 e5 ⊢ <;>
    exact ⟨Units.ext ‹_›, Units.ext ‹_›⟩

theorem card_qSub (hk : Nat.card k = 4) : Nat.card (qSub (k := k)) = 27 := by
  rw [← SetLike.coe_sort_coe, coe_qSub, Nat.card_range_of_injective qElt_injective,
    Nat.card_prod, Nat.card_prod, LinearThreeFourOuter.card_units_eq_three hk, Nat.card_fin]

theorem qElt_pow_three (hk : Nat.card k = 4) (x : (kˣ × kˣ) × Fin 3) : qElt x ^ 3 = 1 := by
  obtain ⟨p, i⟩ := x
  have hp3 : p ^ 3 = 1 := Prod.ext (LinearThreeFourOuter.units_pow_three hk _)
    (LinearThreeFourOuter.units_pow_three hk _)
  fin_cases i
  · simp [qElt, ← map_pow, hp3]
  · simp only [qElt, pow_one, pow_three, mul_assoc, rSL_mul_dHom_mul, rSL_mul_rSL_mul_rSL,
      mul_one]
    rw [← map_mul, ← map_mul, ← mul_assoc, mul_rot_mul_rot_rot, map_one]
  · simp only [qElt, pow_two, pow_three, mul_assoc, rSL_mul_dHom_mul, rSL_mul_rSL_mul_rSL_mul,
      rSL_mul_rSL_mul_rSL, mul_one]
    rw [← map_mul, ← map_mul, mul_comm (rot (rot p)), ← mul_assoc, mul_rot_mul_rot_rot, map_one]

theorem dHom_eq_of_mem_scalars {g : Matrix.SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ scalars 3 k) : ∃ c : kˣ, dHom (c, c) = g := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  refine ⟨c, Subtype.ext ?_⟩
  rw [coe_dHom, hgc, scalar_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hc)]

theorem scalars_le_qSub : scalars 3 k ≤ qSub := by
  intro g hg
  obtain ⟨c, rfl⟩ := dHom_eq_of_mem_scalars hg
  exact Subgroup.subset_closure (Or.inl (mem_dSet_iff.mpr ⟨_, rfl⟩))

theorem card_scalars (hk : Nat.card k = 4) : Nat.card (scalars 3 k) = 3 := by
  have hset : (scalars 3 k : Set (Matrix.SpecialLinearGroup (Fin 3) k)) =
      Set.range (fun c : kˣ => dHom (c, c)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := dHom_eq_of_mem_scalars hg
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      have hc := LinearThreeFourOuter.units_pow_three hk c
      refine mem_scalars.mpr ⟨c, hc, ?_⟩
      rw [coe_dHom, scalar_apply]
      congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        rw [inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hc)]
  have hinj : Function.Injective
      (fun c : kˣ => (dHom (c, c) : Matrix.SpecialLinearGroup (Fin 3) k)) := by
    intro c d h
    have := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k)) h) 0) 0
    simp [coe_dHom, diagonal] at this
    exact Units.ext this
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective hinj,
    LinearThreeFourOuter.card_units_eq_three hk]

theorem card_map_proj_qSub (hk : Nat.card k = 4) :
    Nat.card ((qSub (k := k)).map (proj 3 k)) = 9 := by
  have h := Subgroup.card_ker_mul_card_range ((proj 3 k).comp (qSub (k := k)).subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype, card_qSub hk] at h
  have hker : ((proj 3 k).comp (qSub (k := k)).subtype).ker = (scalars 3 k).subgroupOf qSub := by
    rw [← MonoidHom.comap_ker, ker_proj]
    rfl
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe scalars_le_qSub).toEquiv,
    card_scalars hk] at h
  omega

theorem pow_three_of_mem_map_proj (hk : Nat.card k = 4) {x : projectiveSL 3 k}
    (hx : x ∈ (qSub (k := k)).map (proj 3 k)) : x ^ 3 = 1 := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [coe_qSub] at hg
  obtain ⟨y, rfl⟩ := hg
  rw [← map_pow, qElt_pow_three hk, map_one]

theorem isElementaryAbelian_three_of_card {G : Type*} [Group G] {H : Subgroup G}
    (hcard : Nat.card H = 9) (hexp : ∀ x ∈ H, x ^ 3 = 1) : CFSG.IsElementaryAbelian 3 H :=
  { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hexp x x.2) }

variable {σ : k ≃+* k}

theorem sigma_units (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (x : kˣ) :
    σ (x : k) = ((x⁻¹ : kˣ) : k) := by
  have h := congrArg Units.val (LinearThreeFourOuter.units_map_sigma hσ hk x)
  simpa using h

theorem beta_proj_dHom (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (p : kˣ × kˣ) :
    (fieldAut 3 k σ * dualAut 3 k) (proj 3 k (dHom p)) = proj 3 k (dHom p) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_transpose,
    ← map_inv, coe_dHom, coe_dHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, sigma_units hσ hk]

theorem beta_proj_rSL :
    (fieldAut 3 k σ * dualAut 3 k) (proj 3 k rSL) = proj 3 k rSL := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_transpose, rSL_inv,
    Matrix.SpecialLinearGroup.coe_mul, coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem beta_fixed (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) {x : projectiveSL 3 k}
    (hx : x ∈ (qSub (k := k)).map (proj 3 k)) : (fieldAut 3 k σ * dualAut 3 k) x = x := by
  obtain ⟨g, hg, rfl⟩ := hx
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · obtain ⟨p, rfl⟩ := mem_dSet_iff.mp hg
      exact beta_proj_dHom hσ hk p
    · rw [Set.mem_singleton_iff.mp hg]
      exact beta_proj_rSL
  | one => simp
  | mul g h _ _ ihg ihh => rw [map_mul, map_mul, ihg, ihh]
  | inv g _ ih => rw [map_inv, map_inv, ih]

theorem beta_mul_beta (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) :
    (fieldAut 3 k σ * dualAut 3 k) * (fieldAut 3 k σ * dualAut 3 k) = 1 := by
  rw [mul_assoc, ← mul_assoc (dualAut 3 k), dualAut_mul_fieldAut, mul_assoc,
    LinearThreeFourOuter.dualAut_mul_self, mul_one,
    LinearThreeFourOuter.fieldAut_sigma_mul_self hσ hk]

@[expose] def jM : Matrix (Fin 3) (Fin 3) k :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem jM_mul_jM : (jM : Matrix (Fin 3) (Fin 3) k) * jM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jM, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def jGL : GL (Fin 3) k :=
  ⟨jM, jM, jM_mul_jM, jM_mul_jM⟩

@[expose] def bM (ω : k) : Matrix (Fin 3) (Fin 3) k :=
  !![1, 1, 0; 0, 0, 1; ω, ω ^ 2, 0]

variable {ω : k}

theorem det_bM (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) : (bM ω).det = 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have h := LinearFieldFour.omega_mul_omega hk hω0 hω1
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  simp [bM, det_fin_three]
  linear_combination (-1 : k) * h - h2

theorem bM_mul_map_transpose (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) : bM ω * ((bM ω)ᵀ).map σ = jM := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have h := LinearFieldFour.omega_mul_omega hk hω0 hω1
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have h4 := LinearFieldFour.pow_four_eq_self hk ω
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bM, jM, Matrix.mul_apply, Fin.sum_univ_three, hσ]
  · linear_combination h2
  · linear_combination h + h4 + ω * h2
  · linear_combination h + ω * h2
  · linear_combination ((ω + 1) * (ω ^ 3 + 2)) * h + (ω * (ω ^ 3 + 2) + 1) * h2

theorem conjAut_mul_beta_mul_inv (H : GL (Fin 3) k) :
    conjAut 3 k H * (fieldAut 3 k σ * dualAut 3 k) * (conjAut 3 k H)⁻¹ =
      conjAut 3 k (H * GeneralLinearGroup.map (σ : k →+* k)
        (GeneralLinearGroup.inverseTranspose H⁻¹)) * (fieldAut 3 k σ * dualAut 3 k) := by
  rw [← map_inv, mul_assoc, mul_assoc, dualAut_mul_conjAut, ← mul_assoc (fieldAut 3 k σ),
    fieldAut_mul_conjAut, map_mul]
  simp only [mul_assoc]

theorem gamma_eq (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (B : Matrix.SpecialLinearGroup (Fin 3) k) (hB : (B : Matrix (Fin 3) (Fin 3) k) = bM ω) :
    conjAut 3 k jGL * (fieldAut 3 k σ * dualAut 3 k) =
      conjAut 3 k (Matrix.SpecialLinearGroup.toGL B) * (fieldAut 3 k σ * dualAut 3 k) *
        (conjAut 3 k (Matrix.SpecialLinearGroup.toGL B))⁻¹ := by
  rw [conjAut_mul_beta_mul_inv]
  congr 2
  apply Units.ext
  rw [Units.val_mul]
  change jM = _
  rw [show ((GeneralLinearGroup.map (σ : k →+* k) (GeneralLinearGroup.inverseTranspose
    (Matrix.SpecialLinearGroup.toGL B)⁻¹) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      ((B : Matrix (Fin 3) (Fin 3) k)ᵀ).map σ by
    change ((GeneralLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.toGL B)⁻¹ :
      GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map σ = _
    rw [GeneralLinearGroup.coe_inverseTranspose, inv_inv]
    rfl, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hB, bM_mul_map_transpose hσ hk hω0 hω1]

theorem gamma_sq (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (B : Matrix.SpecialLinearGroup (Fin 3) k) (hB : (B : Matrix (Fin 3) (Fin 3) k) = bM ω) :
    (conjAut 3 k jGL * (fieldAut 3 k σ * dualAut 3 k)) ^ 2 = 1 := by
  rw [gamma_eq hσ hk hω0 hω1 B hB, conj_pow, pow_two, beta_mul_beta hσ hk, mul_one,
    mul_inv_cancel]

theorem proj_conj (B g : Matrix.SpecialLinearGroup (Fin 3) k) :
    proj 3 k (MulAut.conj B g) =
      conjAut 3 k (Matrix.SpecialLinearGroup.toGL B) (proj 3 k g) := by
  rw [conjAut_proj, MulAut.conj_apply]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem map_conj_map_proj (B : Matrix.SpecialLinearGroup (Fin 3) k) :
    ((qSub (k := k)).map (MulAut.conj B).toMonoidHom).map (proj 3 k) =
      ((qSub (k := k)).map (proj 3 k)).map
        (conjAut 3 k (Matrix.SpecialLinearGroup.toGL B)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => proj_conj B g

end LinearThreeFourFixedNine

open LinearFlag LinearThreeFourFixedNine

theorem linear_three_four_graph_field_fixed_nine {k : Type*} [Field k] (hk : Nat.card k = 4)
    {ω : k} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 3) k, (B : Matrix (Fin 3) (Fin 3) k) = bM ω ∧
      conjAut 3 k jGL * (fieldAut 3 k σ * dualAut 3 k) =
        conjAut 3 k (Matrix.SpecialLinearGroup.toGL B) * (fieldAut 3 k σ * dualAut 3 k) *
          (conjAut 3 k (Matrix.SpecialLinearGroup.toGL B))⁻¹ ∧
      (conjAut 3 k jGL * (fieldAut 3 k σ * dualAut 3 k)) ^ 2 = 1 ∧
      Nat.card (qSub (k := k)) = 27 ∧
      CFSG.IsElementaryAbelian 3 ((qSub (k := k)).map (proj 3 k)) ∧
      Nat.card ((qSub (k := k)).map (proj 3 k)) = 9 ∧
      (∀ x ∈ (qSub (k := k)).map (proj 3 k), (fieldAut 3 k σ * dualAut 3 k) x = x) ∧
      CFSG.IsElementaryAbelian 3
        (((qSub (k := k)).map (MulAut.conj B).toMonoidHom).map (proj 3 k)) ∧
      Nat.card (((qSub (k := k)).map (MulAut.conj B).toMonoidHom).map (proj 3 k)) = 9 ∧
      ∀ x ∈ ((qSub (k := k)).map (MulAut.conj B).toMonoidHom).map (proj 3 k),
        (conjAut 3 k jGL * (fieldAut 3 k σ * dualAut 3 k)) x = x := by
  set B : Matrix.SpecialLinearGroup (Fin 3) k := ⟨bM ω, det_bM hk hω0 hω1⟩ with hBdef
  have hB : (B : Matrix (Fin 3) (Fin 3) k) = bM ω := rfl
  have hγ := gamma_eq hσ hk hω0 hω1 B hB
  have hcard := card_map_proj_qSub hk
  have hcardB :
      Nat.card (((qSub (k := k)).map (MulAut.conj B).toMonoidHom).map (proj 3 k)) = 9 := by
    rw [map_conj_map_proj, Subgroup.card_map_of_injective (MulEquiv.injective _), hcard]
  refine ⟨B, hB, hγ, gamma_sq hσ hk hω0 hω1 B hB, card_qSub hk,
    isElementaryAbelian_three_of_card hcard fun x hx => pow_three_of_mem_map_proj hk hx, hcard,
    fun x hx => beta_fixed hσ hk hx,
    isElementaryAbelian_three_of_card hcardB fun x hx => ?_, hcardB, fun x hx => ?_⟩
  · rw [map_conj_map_proj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, pow_three_of_mem_map_proj hk hy, map_one]
  · rw [map_conj_map_proj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hγ]
    have hβ := beta_fixed hσ hk hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply] at hβ ⊢
    rw [hβ]

end CFSG.LocalAnalysis.ComponentInitial
