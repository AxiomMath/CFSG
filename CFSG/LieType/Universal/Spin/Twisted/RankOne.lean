module

public import CFSG.LieType.Universal.Spin.Twisted.ShortAction
public import CFSG.LieType.Steinberg.PartBRankOne

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.Steinberg

variable (n : ℕ) {K : Type*} [Field K] (b c : K)

@[expose] noncomputable def planeRefl (a p : Fin 2 → K) : Fin 2 → K :=
  p - (polarPlane b c p a / planeNorm b c a) • a

variable {b c}

theorem polarPlane_planeRefl {a : Fin 2 → K} (ha : planeNorm b c a ≠ 0) (p : Fin 2 → K) :
    polarPlane b c (planeRefl b c a p) a = -polarPlane b c p a := by
  rw [planeRefl, sub_eq_add_neg, polarPlane_add_left, ← neg_smul, polarPlane_smul_left,
    polarPlane_self]
  field_simp
  ring

theorem planeRefl_planeRefl {a : Fin 2 → K} (ha : planeNorm b c a ≠ 0) (p : Fin 2 → K) :
    planeRefl b c a (planeRefl b c a p) = p := by
  conv_lhs => rw [planeRefl]
  rw [polarPlane_planeRefl ha, planeRefl]
  ext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem planeRefl_neg (a p : Fin 2 → K) : planeRefl b c (-a) p = planeRefl b c a p := by
  rw [planeRefl, planeRefl, planeNorm_neg, polarPlane_comm, polarPlane_neg_left,
    polarPlane_comm]
  ext k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem planeRefl_zero (a : Fin 2 → K) : planeRefl b c a 0 = 0 := by
  simp [planeRefl, polarPlane_zero_left]

@[expose] def planeOne : Fin 2 → K := ![1, 0]

theorem planeNorm_planeOne : planeNorm b c (planeOne : Fin 2 → K) = 1 := by
  simp [planeNorm, planeOne]

theorem planeNorm_planeOne_ne_zero : planeNorm b c (planeOne : Fin 2 → K) ≠ 0 := by
  rw [planeNorm_planeOne]
  exact one_ne_zero

theorem planeOne_ne_zero : (planeOne : Fin 2 → K) ≠ 0 := by
  intro h
  simpa [planeOne] using congrFun h 0

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def shortWeylElt (i : Fin (n - 1)) (a : Fin 2 → K) :
    spinGroup (quadMinus n K b c) :=
  shortPosHom n hirr i (.ofAdd a) * shortNegHom n hirr i (.ofAdd ((planeNorm b c a)⁻¹ • a)) *
    shortPosHom n hirr i (.ofAdd a)

@[expose] noncomputable def shortWeyl (i : Fin (n - 1)) : spinGroup (quadMinus n K b c) :=
  shortWeylElt n hirr i planeOne

@[expose] noncomputable def shortTorusElt (i : Fin (n - 1)) (a : Fin 2 → K) :
    spinGroup (quadMinus n K b c) :=
  shortWeylElt n hirr i a * (shortWeyl n hirr i)⁻¹

@[expose] noncomputable def shortTorus (i : Fin (n - 1)) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  Subgroup.closure (shortTorusElt n hirr i '' {a | a ≠ 0})

theorem shortWeyl_eq (i : Fin (n - 1)) :
    shortWeyl n hirr i = shortPosHom n hirr i (.ofAdd planeOne) *
      shortNegHom n hirr i (.ofAdd planeOne) * shortPosHom n hirr i (.ofAdd planeOne) := by
  rw [shortWeyl, shortWeylElt, planeNorm_planeOne, inv_one, one_smul]

theorem shortWeylElt_neg (i : Fin (n - 1)) (a : Fin 2 → K) :
    shortWeylElt n hirr i (-a) = (shortWeylElt n hirr i a)⁻¹ := by
  rw [shortWeylElt, shortWeylElt, planeNorm_neg, smul_neg, ofAdd_neg, ofAdd_neg, map_inv,
    map_inv]
  group

theorem shortTorusElt_mem (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    shortTorusElt n hirr i a ∈ shortTorus n hirr i :=
  Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem spinAction_shortWeylElt_wVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) (l : K)
    (p : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (wVec n i l p m) =
      wVec n i (-(planeNorm b c a) * m) (planeRefl b c a p) (-(planeNorm b c a)⁻¹ * l) := by
  have hN := planeNorm_ne_zero hirr ha
  rw [shortWeylElt, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    spinAction_shortPosHom_wVec, spinAction_shortNegHom_wVec, spinAction_shortPosHom_wVec,
    wVec_eq_iff]
  simp only [polarPlane_add_left, polarPlane_smul_left, polarPlane_smul_right, planeNorm_smul,
    polarPlane_self]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · ext k
    simp only [planeRefl, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · field_simp
    ring

theorem spinAction_shortWeylElt_eVec_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (eVec n j) = eVec n j := by
  rw [shortWeylElt, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    spinAction_shortPosHom_eVec, spinAction_shortNegHom_eVec_of_ne n hirr hij,
    spinAction_shortPosHom_eVec]

theorem spinAction_shortWeylElt_fVec_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (fVec n j) = fVec n j := by
  rw [shortWeylElt, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    spinAction_shortPosHom_fVec_of_ne n hirr hij, spinAction_shortNegHom_fVec,
    spinAction_shortPosHom_fVec_of_ne n hirr hij]

theorem spinAction_shortWeyl_wVec (i : Fin (n - 1)) (l : K) (p : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (wVec n i l p m) =
      wVec n i (-m) (planeRefl b c planeOne p) (-l) := by
  rw [shortWeyl, spinAction_shortWeylElt_wVec n hirr i planeOne_ne_zero, planeNorm_planeOne,
    inv_one, neg_one_mul, neg_one_mul]

theorem spinAction_shortWeyl_inv_wVec (i : Fin (n - 1)) (l : K) (p : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i)⁻¹ (wVec n i l p m) =
      wVec n i (-m) (planeRefl b c planeOne p) (-l) := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [spinAction_shortWeyl_wVec, planeRefl_planeRefl planeNorm_planeOne_ne_zero, neg_neg,
    neg_neg]

theorem spinAction_shortWeylElt_eVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (eVec n i) =
      (-(planeNorm b c a)⁻¹) • fVec n i := by
  rw [← wVec_eVec, spinAction_shortWeylElt_wVec n hirr i ha, ← wVec_fVec, wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortWeylElt_fVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (fVec n i) =
      (-planeNorm b c a) • eVec n i := by
  rw [← wVec_fVec, spinAction_shortWeylElt_wVec n hirr i ha, ← wVec_eVec, wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortWeylElt_planeVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeylElt n hirr i a) (planeVec n p) =
      planeVec n (planeRefl b c a p) := by
  rw [← wVec_planeVec n i p, spinAction_shortWeylElt_wVec n hirr i ha, ← wVec_planeVec,
    wVec_eq_iff]
  simp

theorem spinAction_shortTorusElt_wVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) (l : K)
    (p : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (wVec n i l p m) =
      wVec n i (planeNorm b c a * l) (planeRefl b c a (planeRefl b c planeOne p))
        ((planeNorm b c a)⁻¹ * m) := by
  rw [shortTorusElt, map_mul, LinearEquiv.mul_apply, spinAction_shortWeyl_inv_wVec,
    spinAction_shortWeylElt_wVec n hirr i ha, wVec_eq_iff]
  exact ⟨by ring, rfl, by ring⟩

theorem spinAction_shortTorusElt_eVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (eVec n i) =
      planeNorm b c a • eVec n i := by
  rw [← wVec_eVec, spinAction_shortTorusElt_wVec n hirr i ha, wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortTorusElt_fVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (fVec n i) =
      (planeNorm b c a)⁻¹ • fVec n i := by
  rw [← wVec_fVec, spinAction_shortTorusElt_wVec n hirr i ha, wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortTorusElt_planeVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (planeVec n p) =
      planeVec n (planeRefl b c a (planeRefl b c planeOne p)) := by
  rw [← wVec_planeVec n i p, spinAction_shortTorusElt_wVec n hirr i ha, ← wVec_planeVec,
    wVec_eq_iff]
  simp

theorem spinAction_shortTorusElt_inv_planeVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a)⁻¹ (planeVec n p) =
      planeVec n (planeRefl b c planeOne (planeRefl b c a p)) := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [spinAction_shortTorusElt_planeVec n hirr i ha, planeRefl_planeRefl planeNorm_planeOne_ne_zero,
    planeRefl_planeRefl (planeNorm_ne_zero hirr ha)]

theorem spinAction_shortTorusElt_inv_eVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a)⁻¹ (eVec n i) =
      (planeNorm b c a)⁻¹ • eVec n i := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [map_smul, spinAction_shortTorusElt_eVec n hirr i ha, smul_smul,
    inv_mul_cancel₀ (planeNorm_ne_zero hirr ha), one_smul]

theorem spinAction_shortTorusElt_inv_fVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a)⁻¹ (fVec n i) =
      planeNorm b c a • fVec n i := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [map_smul, spinAction_shortTorusElt_fVec n hirr i ha, smul_smul,
    mul_inv_cancel₀ (planeNorm_ne_zero hirr ha), one_smul]

theorem spinAction_shortWeyl_eVec (i : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (eVec n i) = -fVec n i := by
  rw [shortWeyl, spinAction_shortWeylElt_eVec n hirr i planeOne_ne_zero, planeNorm_planeOne,
    inv_one, neg_one_smul]

theorem spinAction_shortWeyl_fVec (i : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (fVec n i) = -eVec n i := by
  rw [shortWeyl, spinAction_shortWeylElt_fVec n hirr i planeOne_ne_zero, planeNorm_planeOne,
    neg_one_smul]

theorem spinAction_shortWeyl_planeVec (i : Fin (n - 1)) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (planeVec n p) =
      planeVec n (planeRefl b c planeOne p) :=
  spinAction_shortWeylElt_planeVec n hirr i planeOne_ne_zero p

theorem spinAction_shortWeyl_inv_eVec (i : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i)⁻¹ (eVec n i) = -fVec n i := by
  rw [← wVec_eVec, spinAction_shortWeyl_inv_wVec, ← wVec_fVec, ← neg_one_smul K (wVec n i _ _ _),
    wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortWeyl_inv_fVec (i : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i)⁻¹ (fVec n i) = -eVec n i := by
  rw [← wVec_fVec, spinAction_shortWeyl_inv_wVec, ← wVec_eVec, ← neg_one_smul K (wVec n i _ _ _),
    wVec_smul, wVec_eq_iff]
  simp [planeRefl_zero]

theorem spinAction_shortWeyl_inv_planeVec (i : Fin (n - 1)) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i)⁻¹ (planeVec n p) =
      planeVec n (planeRefl b c planeOne p) := by
  rw [← wVec_planeVec n i p, spinAction_shortWeyl_inv_wVec, ← wVec_planeVec, wVec_eq_iff]
  simp

theorem spinAction_shortTorusElt_eVec_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (eVec n j) = eVec n j := by
  rw [shortTorusElt, map_mul, LinearEquiv.mul_apply,
    spinAction_inv_apply_of_apply _ (shortWeyl n hirr i)
      (spinAction_shortWeylElt_eVec_of_ne n hirr hij planeOne),
    spinAction_shortWeylElt_eVec_of_ne n hirr hij]

theorem spinAction_shortTorusElt_fVec_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (fVec n j) = fVec n j := by
  rw [shortTorusElt, map_mul, LinearEquiv.mul_apply,
    spinAction_inv_apply_of_apply _ (shortWeyl n hirr i)
      (spinAction_shortWeylElt_fVec_of_ne n hirr hij planeOne),
    spinAction_shortWeylElt_fVec_of_ne n hirr hij]

theorem conj_shortPosHom_of_eVec (g : spinGroup (quadMinus n K b c)) (j : Fin (n - 1))
    {p q : Fin 2 → K} {r : K} (he : spinAction (quadMinus n K b c) g (eVec n j) = r • eVec n j)
    (hp : spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    g * shortPosHom n hirr j (.ofAdd p) * g⁻¹ = shortPosHom n hirr j (.ofAdd (r • q)) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_shortPosHom, coe_conj_one_add_ι_mul_ι, he, hp,
    coe_shortPosHom, planeVec_smul, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

theorem conj_shortPosHom_of_fVec (g : spinGroup (quadMinus n K b c)) (j : Fin (n - 1))
    {p q : Fin 2 → K} {r : K} (he : spinAction (quadMinus n K b c) g (eVec n j) = r • fVec n j)
    (hp : spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    g * shortPosHom n hirr j (.ofAdd p) * g⁻¹ = shortNegHom n hirr j (.ofAdd (r • q)) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_shortPosHom, coe_conj_one_add_ι_mul_ι, he, hp,
    coe_shortNegHom, planeVec_smul, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

theorem conj_shortNegHom_of_fVec (g : spinGroup (quadMinus n K b c)) (j : Fin (n - 1))
    {p q : Fin 2 → K} {r : K} (hf : spinAction (quadMinus n K b c) g (fVec n j) = r • fVec n j)
    (hp : spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    g * shortNegHom n hirr j (.ofAdd p) * g⁻¹ = shortNegHom n hirr j (.ofAdd (r • q)) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_shortNegHom, coe_conj_one_add_ι_mul_ι, hf, hp,
    coe_shortNegHom, planeVec_smul, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

theorem conj_shortNegHom_of_eVec (g : spinGroup (quadMinus n K b c)) (j : Fin (n - 1))
    {p q : Fin 2 → K} {r : K} (hf : spinAction (quadMinus n K b c) g (fVec n j) = r • eVec n j)
    (hp : spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    g * shortNegHom n hirr j (.ofAdd p) * g⁻¹ = shortPosHom n hirr j (.ofAdd (r • q)) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_shortNegHom, coe_conj_one_add_ι_mul_ι, hf, hp,
    coe_shortPosHom, planeVec_smul, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

theorem shortWeylElt_mem (i : Fin (n - 1)) (a : Fin 2 → K) :
    shortWeylElt n hirr i a ∈ (shortPosHom n hirr i).range ⊔ (shortNegHom n hirr i).range :=
  mul_mem (mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩))
    (Subgroup.mem_sup_left ⟨_, rfl⟩)

theorem shortWeyl_mem (i : Fin (n - 1)) :
    shortWeyl n hirr i ∈ (shortPosHom n hirr i).range ⊔ (shortNegHom n hirr i).range :=
  shortWeylElt_mem n hirr i planeOne

theorem shortTorus_le (i : Fin (n - 1)) :
    shortTorus n hirr i ≤ (shortPosHom n hirr i).range ⊔ (shortNegHom n hirr i).range := by
  rw [shortTorus, Subgroup.closure_le]
  rintro _ ⟨a, -, rfl⟩
  exact mul_mem (shortWeylElt_mem n hirr i a) (inv_mem (shortWeyl_mem n hirr i))

theorem shortWeyl_sq_mem (i : Fin (n - 1)) : shortWeyl n hirr i ^ 2 ∈ shortTorus n hirr i := by
  have h : shortWeyl n hirr i ^ 2 = (shortTorusElt n hirr i (-planeOne))⁻¹ := by
    rw [shortTorusElt, shortWeylElt_neg, ← shortWeyl, pow_two, mul_inv_rev, inv_inv]
  rw [h]
  exact inv_mem (shortTorusElt_mem n hirr i (neg_ne_zero.2 planeOne_ne_zero))

theorem shortWeyl_conj_shortPosHom (i : Fin (n - 1)) (p : Fin 2 → K) :
    shortWeyl n hirr i * shortPosHom n hirr i (.ofAdd p) * (shortWeyl n hirr i)⁻¹ =
      shortNegHom n hirr i (.ofAdd (-planeRefl b c planeOne p)) := by
  rw [conj_shortPosHom_of_fVec n hirr _ i (r := -1)
    (by rw [spinAction_shortWeyl_eVec, neg_one_smul]) (spinAction_shortWeyl_planeVec n hirr i p),
    neg_one_smul]

theorem shortWeyl_conj_shortNegHom (i : Fin (n - 1)) (p : Fin 2 → K) :
    shortWeyl n hirr i * shortNegHom n hirr i (.ofAdd p) * (shortWeyl n hirr i)⁻¹ =
      shortPosHom n hirr i (.ofAdd (-planeRefl b c planeOne p)) := by
  rw [conj_shortNegHom_of_eVec n hirr _ i (r := -1)
    (by rw [spinAction_shortWeyl_fVec, neg_one_smul]) (spinAction_shortWeyl_planeVec n hirr i p),
    neg_one_smul]

theorem shortWeyl_inv_conj_shortPosHom (i : Fin (n - 1)) (p : Fin 2 → K) :
    (shortWeyl n hirr i)⁻¹ * shortPosHom n hirr i (.ofAdd p) * (shortWeyl n hirr i)⁻¹⁻¹ =
      shortNegHom n hirr i (.ofAdd (-planeRefl b c planeOne p)) := by
  rw [conj_shortPosHom_of_fVec n hirr _ i (r := -1)
    (by rw [spinAction_shortWeyl_inv_eVec, neg_one_smul])
    (spinAction_shortWeyl_inv_planeVec n hirr i p), neg_one_smul]

theorem shortWeyl_inv_conj_shortNegHom (i : Fin (n - 1)) (p : Fin 2 → K) :
    (shortWeyl n hirr i)⁻¹ * shortNegHom n hirr i (.ofAdd p) * (shortWeyl n hirr i)⁻¹⁻¹ =
      shortPosHom n hirr i (.ofAdd (-planeRefl b c planeOne p)) := by
  rw [conj_shortNegHom_of_eVec n hirr _ i (r := -1)
    (by rw [spinAction_shortWeyl_inv_fVec, neg_one_smul])
    (spinAction_shortWeyl_inv_planeVec n hirr i p), neg_one_smul]

private theorem shortTorusElt_conj_mem_pos (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (x : spinGroup (quadMinus n K b c)) (hx : x ∈ (shortPosHom n hirr i).range) :
    shortTorusElt n hirr i a * x * (shortTorusElt n hirr i a)⁻¹ ∈ (shortPosHom n hirr i).range ∧
      (shortTorusElt n hirr i a)⁻¹ * x * (shortTorusElt n hirr i a)⁻¹⁻¹ ∈
        (shortPosHom n hirr i).range := by
  obtain ⟨p, rfl⟩ := hx
  rw [← ofAdd_toAdd p]
  exact ⟨⟨_, (conj_shortPosHom_of_eVec n hirr _ i (spinAction_shortTorusElt_eVec n hirr i ha)
    (spinAction_shortTorusElt_planeVec n hirr i ha _)).symm⟩,
    ⟨_, (conj_shortPosHom_of_eVec n hirr _ i (spinAction_shortTorusElt_inv_eVec n hirr i ha)
    (spinAction_shortTorusElt_inv_planeVec n hirr i ha _)).symm⟩⟩

private theorem shortTorusElt_conj_mem_neg (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (x : spinGroup (quadMinus n K b c)) (hx : x ∈ (shortNegHom n hirr i).range) :
    shortTorusElt n hirr i a * x * (shortTorusElt n hirr i a)⁻¹ ∈ (shortNegHom n hirr i).range ∧
      (shortTorusElt n hirr i a)⁻¹ * x * (shortTorusElt n hirr i a)⁻¹⁻¹ ∈
        (shortNegHom n hirr i).range := by
  obtain ⟨p, rfl⟩ := hx
  rw [← ofAdd_toAdd p]
  exact ⟨⟨_, (conj_shortNegHom_of_fVec n hirr _ i (spinAction_shortTorusElt_fVec n hirr i ha)
    (spinAction_shortTorusElt_planeVec n hirr i ha _)).symm⟩,
    ⟨_, (conj_shortNegHom_of_fVec n hirr _ i (spinAction_shortTorusElt_inv_fVec n hirr i ha)
    (spinAction_shortTorusElt_inv_planeVec n hirr i ha _)).symm⟩⟩

private theorem closure_le_normalizer {G : Type*} [Group G] {T : Set G} {S : Subgroup G}
    (h : ∀ g ∈ T, ∀ x ∈ S, g * x * g⁻¹ ∈ S ∧ g⁻¹ * x * g⁻¹⁻¹ ∈ S) :
    Subgroup.closure T ≤ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => (h g hg x hx).1, fun hx => ?_⟩
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
    (h g hg _ hx).2

theorem shortTorus_le_normalizer_pos (i : Fin (n - 1)) :
    shortTorus n hirr i ≤
      Subgroup.normalizer ((shortPosHom n hirr i).range : Set (spinGroup (quadMinus n K b c))) :=
  closure_le_normalizer fun _ ⟨_, ha, hg⟩ x hx => hg ▸ shortTorusElt_conj_mem_pos n hirr i ha x hx

theorem shortTorus_le_normalizer_neg (i : Fin (n - 1)) :
    shortTorus n hirr i ≤
      Subgroup.normalizer ((shortNegHom n hirr i).range : Set (spinGroup (quadMinus n K b c))) :=
  closure_le_normalizer fun _ ⟨_, ha, hg⟩ x hx => hg ▸ shortTorusElt_conj_mem_neg n hirr i ha x hx

theorem shortPos_eq_one_of_mem_normalizer (i : Fin (n - 1)) {u : spinGroup (quadMinus n K b c)}
    (hu : u ∈ (shortPosHom n hirr i).range)
    (hn : u ∈ Subgroup.normalizer
      ((shortNegHom n hirr i).range : Set (spinGroup (quadMinus n K b c)))) :
    u = 1 := by
  obtain ⟨p, rfl⟩ := hu
  rw [← ofAdd_toAdd p] at hn ⊢
  obtain ⟨q, hq⟩ := (Subgroup.mem_normalizer_iff.mp hn
    (shortNegHom n hirr i (.ofAdd planeOne))).mp ⟨_, rfl⟩
  have hf := congrArg (fun g => spinAction (quadMinus n K b c) g (fVec n i)) hq
  rw [← ofAdd_toAdd q, spinAction_shortNegHom_fVec, ← map_inv, ← ofAdd_neg, map_mul, map_mul,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← wVec_fVec, spinAction_shortPosHom_wVec,
    spinAction_shortNegHom_wVec, spinAction_shortPosHom_wVec, wVec_eq_iff] at hf
  obtain ⟨-, hw, hm⟩ := hf
  have h0 := congrFun hw 0
  rw [← hm] at h0
  simp [planeOne, polarPlane_zero_left, planeNorm_neg, Matrix.vecHead] at h0
  have hp : p.toAdd = 0 := by
    by_contra hp
    exact planeNorm_ne_zero hirr hp (by linear_combination h0)
  rw [hp, ofAdd_zero, map_one]

variable (b c) in
abbrev ShortField : Type _ := QuadraticAlgebra K (-c) b

omit hirr in
theorem fact_shortField (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Fact (∀ r : K, r ^ 2 ≠ -c + b * r) :=
  ⟨fun r hr => hirr (-r) (by linear_combination hr)⟩

omit hirr in
theorem finite_shortField [Finite K] : Finite (ShortField b c) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-c) b).symm

@[expose] def fieldCoord (t : ShortField b c) : Fin 2 → K := ![t.re, t.im]

@[expose] def starCoord (t : ShortField b c) : Fin 2 → K := ![-(t.re + b * t.im), t.im]

omit hirr in
theorem fieldCoord_add (s t : ShortField b c) :
    fieldCoord (s + t) = fieldCoord s + fieldCoord t := by
  ext k
  fin_cases k <;> simp [fieldCoord]

omit hirr in
theorem starCoord_add (s t : ShortField b c) : starCoord (s + t) = starCoord s + starCoord t := by
  ext k
  fin_cases k
  · simp [starCoord]
    ring
  · simp [starCoord]

omit hirr in
theorem fieldCoord_one : fieldCoord (1 : ShortField b c) = planeOne := by
  ext k
  fin_cases k <;> rfl

omit hirr in
theorem fieldCoord_ne_zero {t : ShortField b c} (ht : t ≠ 0) : fieldCoord t ≠ 0 := by
  intro h
  apply ht
  ext
  · simpa [fieldCoord] using congrFun h 0
  · simpa [fieldCoord] using congrFun h 1

omit hirr in
theorem exists_fieldCoord_eq (p : Fin 2 → K) : ∃ t : ShortField b c, fieldCoord t = p :=
  ⟨⟨p 0, p 1⟩, by ext k; fin_cases k <;> rfl⟩

omit hirr in
theorem exists_starCoord_eq (p : Fin 2 → K) : ∃ t : ShortField b c, starCoord t = p :=
  ⟨⟨-p 0 - b * p 1, p 1⟩, by ext k; fin_cases k <;> simp [starCoord]⟩

omit hirr in
theorem planeNorm_fieldCoord (t : ShortField b c) :
    planeNorm b c (fieldCoord t) = QuadraticAlgebra.norm t := by
  simp [planeNorm, fieldCoord, QuadraticAlgebra.norm_def]
  ring

omit hirr in
theorem starCoord_neg_inv (t : ShortField b c) :
    starCoord (-t⁻¹) = (planeNorm b c (fieldCoord t))⁻¹ • fieldCoord t := by
  rw [planeNorm_fieldCoord]
  ext k
  fin_cases k <;> simp [starCoord, fieldCoord, QuadraticAlgebra.re_inv, QuadraticAlgebra.im_inv]
  ring

omit hirr in
theorem starCoord_conj [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] {t : ShortField b c} (ht : t ≠ 0)
    (a : ShortField b c) :
    starCoord (-(t ^ 2)⁻¹ * a) =
      (-(planeNorm b c (fieldCoord t))⁻¹) • planeRefl b c (fieldCoord t) (fieldCoord a) := by
  have hN : QuadraticAlgebra.norm t ≠ 0 := by
    rwa [ne_eq, QuadraticAlgebra.norm_eq_zero_iff_eq_zero]
  rw [← inv_pow]
  simp only [planeRefl, planeNorm_fieldCoord]
  ext k
  fin_cases k <;>
    simp [starCoord, fieldCoord, polarPlane, QuadraticAlgebra.re_inv, QuadraticAlgebra.im_inv,
      pow_two] <;>
    field_simp <;>
    rw [QuadraticAlgebra.norm_def] <;>
    ring

@[expose] noncomputable def shortX (i : Fin (n - 1)) (t : ShortField b c) :
    spinGroup (quadMinus n K b c) :=
  shortPosHom n hirr i (.ofAdd (fieldCoord t))

@[expose] noncomputable def shortY (i : Fin (n - 1)) (t : ShortField b c) :
    spinGroup (quadMinus n K b c) :=
  shortNegHom n hirr i (.ofAdd (starCoord t))

theorem shortX_mul_shortY_mul_shortX (i : Fin (n - 1)) (t : ShortField b c) :
    shortX n hirr i t * shortY n hirr i (-t⁻¹) * shortX n hirr i t =
      shortWeylElt n hirr i (fieldCoord t) := by
  rw [shortX, shortY, starCoord_neg_inv]
  rfl

theorem shortWeylElt_conj_shortX [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (i : Fin (n - 1))
    {t : ShortField b c} (ht : t ≠ 0) (a : ShortField b c) :
    shortWeylElt n hirr i (fieldCoord t) * shortX n hirr i a *
        (shortWeylElt n hirr i (fieldCoord t))⁻¹ = shortY n hirr i (-(t ^ 2)⁻¹ * a) := by
  rw [shortX, conj_shortPosHom_of_fVec n hirr _ i
    (spinAction_shortWeylElt_eVec n hirr i (fieldCoord_ne_zero ht))
    (spinAction_shortWeylElt_planeVec n hirr i (fieldCoord_ne_zero ht) _), shortY,
    starCoord_conj ht]

@[expose] noncomputable def shortRels [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (i : Fin (n - 1)) :
    RankOneRels (spinGroup (quadMinus n K b c)) (ShortField b c) where
  x := shortX n hirr i
  y := shortY n hirr i
  x_add s t := by rw [shortX, shortX, shortX, fieldCoord_add, ofAdd_add, map_mul]
  y_add s t := by rw [shortY, shortY, shortY, starCoord_add, ofAdd_add, map_mul]
  conj_x t ht a := by
    rw [shortX_mul_shortY_mul_shortX, shortWeylElt_conj_shortX n hirr i ht]

section Rels

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

theorem shortRels_x (i : Fin (n - 1)) (t : ShortField b c) :
    (shortRels n hirr i).x t = shortPosHom n hirr i (.ofAdd (fieldCoord t)) :=
  rfl

theorem shortRels_y (i : Fin (n - 1)) (t : ShortField b c) :
    (shortRels n hirr i).y t = shortNegHom n hirr i (.ofAdd (starCoord t)) :=
  rfl

theorem shortRels_w (i : Fin (n - 1)) (t : ShortField b c) :
    (shortRels n hirr i).w t = shortWeylElt n hirr i (fieldCoord t) :=
  shortX_mul_shortY_mul_shortX n hirr i t

theorem shortRels_w_one (i : Fin (n - 1)) : (shortRels n hirr i).w 1 = shortWeyl n hirr i := by
  rw [shortRels_w, fieldCoord_one, shortWeyl]

theorem shortRels_h (i : Fin (n - 1)) (t : ShortField b c) :
    (shortRels n hirr i).h t = shortTorusElt n hirr i (fieldCoord t) := by
  rw [RankOneRels.h_def, shortRels_w, shortRels_w_one, shortTorusElt]

theorem shortRels_sub (i : Fin (n - 1)) :
    (shortRels n hirr i).sub = (shortPosHom n hirr i).range ⊔ (shortNegHom n hirr i).range := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [RankOneRels.sub, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · exact Subgroup.mem_sup_right ⟨_, rfl⟩
  · rintro _ ⟨p, rfl⟩
    obtain ⟨t, ht⟩ := exists_fieldCoord_eq (b := b) (c := c) p.toAdd
    have h := (shortRels n hirr i).x_mem_sub t
    rwa [shortRels_x, ht, ofAdd_toAdd] at h
  · rintro _ ⟨p, rfl⟩
    obtain ⟨t, ht⟩ := exists_starCoord_eq (b := b) (c := c) p.toAdd
    have h := (shortRels n hirr i).y_mem_sub t
    rwa [shortRels_y, ht, ofAdd_toAdd] at h

theorem shortRels_h_mem (i : Fin (n - 1)) {t : ShortField b c} (ht : t ≠ 0) :
    (shortRels n hirr i).h t ∈ shortTorus n hirr i := by
  rw [shortRels_h]
  exact shortTorusElt_mem n hirr i (fieldCoord_ne_zero ht)

theorem exists_shortRels_h_eq (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    ∃ t : ShortField b c, t ≠ 0 ∧ (shortRels n hirr i).h t = shortTorusElt n hirr i a := by
  obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
  exact ⟨t, fun h => ha (by rw [h]; ext k; fin_cases k <;> rfl), shortRels_h n hirr i t⟩

end Rels

theorem shortRankOne_bruhat [Finite K] (i : Fin (n - 1)) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (shortPosHom n hirr i).range ⊔ (shortNegHom n hirr i).range) :
    (∃ h ∈ shortTorus n hirr i, ∃ u ∈ (shortPosHom n hirr i).range, g = h * u) ∨
      ∃ u ∈ (shortPosHom n hirr i).range, ∃ h ∈ shortTorus n hirr i,
        ∃ v ∈ (shortPosHom n hirr i).range, g = u * shortWeyl n hirr i * h * v := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set R := shortRels n hirr i
  rw [← shortRels_sub] at hg
  rcases R.sub_subset_bruhat (fun s t hs ht => R.h_mul hs ht) hg with
    ⟨a, t, ht, rfl⟩ | ⟨a, a', t, ht, rfl⟩
  · refine Or.inl ⟨R.h t, shortRels_h_mem n hirr i ht, R.x ((t ^ 2)⁻¹ * a), ⟨_, rfl⟩, ?_⟩
    rw [R.h_mul_x ht, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht), one_mul]
  · refine Or.inr ⟨R.x a, ⟨_, rfl⟩, R.h t, shortRels_h_mem n hirr i ht, R.x ((t ^ 2)⁻¹ * a'),
      ⟨_, rfl⟩, ?_⟩
    rw [← shortRels_w_one n hirr i, mul_assoc (R.x a * R.w 1) (R.h t), R.h_mul_x ht,
      ← mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero 2 ht)]

theorem mem_shortTorus_iff [Finite K] (i : Fin (n - 1)) {g : spinGroup (quadMinus n K b c)} :
    g ∈ shortTorus n hirr i ↔ ∃ a : Fin 2 → K, a ≠ 0 ∧ shortTorusElt n hirr i a = g := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set R := shortRels n hirr i
  refine ⟨fun hg => ?_, fun ⟨a, ha, hga⟩ => hga ▸ shortTorusElt_mem n hirr i ha⟩
  suffices h : ∃ t : ShortField b c, t ≠ 0 ∧ R.h t = g by
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨fieldCoord t, fieldCoord_ne_zero ht, (shortRels_h n hirr i t).symm⟩
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨a, ha, rfl⟩ := hg
    exact exists_shortRels_h_eq n hirr i ha
  | inv_mem g hg =>
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr i ha
    exact ⟨t⁻¹, inv_ne_zero ht, by rw [← R.h_inv (fun s t hs ht => R.h_mul hs ht) ht, he]⟩
  | one => exact ⟨1, one_ne_zero, R.h_one⟩
  | mul g g' _ _ hg hg' =>
    obtain ⟨t, ht, rfl⟩ := hg
    obtain ⟨t', ht', rfl⟩ := hg'
    exact ⟨t * t', mul_ne_zero ht ht', R.h_mul ht ht'⟩

theorem shortTorus_commute [Finite K] (i : Fin (n - 1)) {g g' : spinGroup (quadMinus n K b c)}
    (hg : g ∈ shortTorus n hirr i) (hg' : g' ∈ shortTorus n hirr i) : Commute g g' := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr i).1 hg
  obtain ⟨a', ha', rfl⟩ := (mem_shortTorus_iff n hirr i).1 hg'
  obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr i ha
  obtain ⟨t', ht', he'⟩ := exists_shortRels_h_eq n hirr i ha'
  rw [← he, ← he']
  exact (shortRels n hirr i).commute_h ht ht'

theorem shortWeyl_conj_mem_shortTorus [Finite K] (i : Fin (n - 1))
    {g : spinGroup (quadMinus n K b c)} (hg : g ∈ shortTorus n hirr i) :
    shortWeyl n hirr i * g * (shortWeyl n hirr i)⁻¹ ∈ shortTorus n hirr i := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set R := shortRels n hirr i
  obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr i).1 hg
  obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr i ha
  rw [← he, ← shortRels_w_one n hirr i, R.w_one_mul_h (fun s t hs ht => R.h_mul hs ht) ht,
    mul_inv_cancel_right]
  exact shortRels_h_mem n hirr i (inv_ne_zero ht)

theorem shortWeyl_inv_conj_mem_shortTorus [Finite K] (i : Fin (n - 1))
    {g : spinGroup (quadMinus n K b c)} (hg : g ∈ shortTorus n hirr i) :
    (shortWeyl n hirr i)⁻¹ * g * shortWeyl n hirr i ∈ shortTorus n hirr i := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set R := shortRels n hirr i
  obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr i).1 hg
  obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr i ha
  rw [← he, ← shortRels_w_one n hirr i, mul_assoc,
    R.h_mul_w_one (fun s t hs ht => R.h_mul hs ht) ht, inv_mul_cancel_left]
  exact shortRels_h_mem n hirr i (inv_ne_zero ht)

@[expose] noncomputable def shortTorusHom [Finite K] (i : Fin (n - 1)) :
    (ShortField b c)ˣ →* spinGroup (quadMinus n K b c) where
  toFun t := shortTorusElt n hirr i (fieldCoord (t : ShortField b c))
  map_one' := by
    rw [Units.val_one, fieldCoord_one, shortTorusElt, ← shortWeyl, mul_inv_cancel]
  map_mul' s t := by
    have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    rw [Units.val_mul, ← shortRels_h, ← shortRels_h, ← shortRels_h]
    exact (shortRels n hirr i).h_mul s.ne_zero t.ne_zero

theorem shortTorusHom_apply [Finite K] (i : Fin (n - 1)) (t : (ShortField b c)ˣ) :
    shortTorusHom n hirr i t = shortTorusElt n hirr i (fieldCoord (t : ShortField b c)) :=
  rfl

theorem range_shortTorusHom [Finite K] (i : Fin (n - 1)) :
    (shortTorusHom n hirr i).range = shortTorus n hirr i := by
  have := fact_shortField hirr
  ext g
  rw [MonoidHom.mem_range, mem_shortTorus_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, fieldCoord_ne_zero t.ne_zero, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
    have ht : t ≠ 0 := fun h => ha (by rw [h]; ext k; fin_cases k <;> rfl)
    exact ⟨Units.mk0 t ht, rfl⟩

theorem shortWeyl_conj_shortPosHom_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (p : Fin 2 → K) :
    shortWeyl n hirr i * shortPosHom n hirr j (.ofAdd p) * (shortWeyl n hirr i)⁻¹ =
      shortPosHom n hirr j (.ofAdd (planeRefl b c planeOne p)) := by
  rw [conj_shortPosHom_of_eVec n hirr _ j (r := 1)
    (by rw [one_smul]; exact spinAction_shortWeylElt_eVec_of_ne n hirr hij planeOne)
    (spinAction_shortWeyl_planeVec n hirr i p), one_smul]

theorem shortWeyl_conj_shortNegHom_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) (p : Fin 2 → K) :
    shortWeyl n hirr i * shortNegHom n hirr j (.ofAdd p) * (shortWeyl n hirr i)⁻¹ =
      shortNegHom n hirr j (.ofAdd (planeRefl b c planeOne p)) := by
  rw [conj_shortNegHom_of_fVec n hirr _ j (r := 1)
    (by rw [one_smul]; exact spinAction_shortWeylElt_fVec_of_ne n hirr hij planeOne)
    (spinAction_shortWeyl_planeVec n hirr i p), one_smul]

theorem shortTorusElt_conj_shortPosHom (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (p : Fin 2 → K) :
    shortTorusElt n hirr i a * shortPosHom n hirr i (.ofAdd p) * (shortTorusElt n hirr i a)⁻¹ =
      shortPosHom n hirr i
        (.ofAdd (planeNorm b c a • planeRefl b c a (planeRefl b c planeOne p))) :=
  conj_shortPosHom_of_eVec n hirr _ i (spinAction_shortTorusElt_eVec n hirr i ha)
    (spinAction_shortTorusElt_planeVec n hirr i ha p)

theorem shortTorusElt_conj_shortNegHom (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (p : Fin 2 → K) :
    shortTorusElt n hirr i a * shortNegHom n hirr i (.ofAdd p) * (shortTorusElt n hirr i a)⁻¹ =
      shortNegHom n hirr i
        (.ofAdd ((planeNorm b c a)⁻¹ • planeRefl b c a (planeRefl b c planeOne p))) :=
  conj_shortNegHom_of_fVec n hirr _ i (spinAction_shortTorusElt_fVec n hirr i ha)
    (spinAction_shortTorusElt_planeVec n hirr i ha p)

theorem shortTorusElt_conj_shortPosHom_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) {a : Fin 2 → K}
    (ha : a ≠ 0) (p : Fin 2 → K) :
    shortTorusElt n hirr i a * shortPosHom n hirr j (.ofAdd p) * (shortTorusElt n hirr i a)⁻¹ =
      shortPosHom n hirr j (.ofAdd (planeRefl b c a (planeRefl b c planeOne p))) := by
  rw [conj_shortPosHom_of_eVec n hirr _ j (r := 1)
    (by rw [one_smul]; exact spinAction_shortTorusElt_eVec_of_ne n hirr hij a)
    (spinAction_shortTorusElt_planeVec n hirr i ha p), one_smul]

theorem shortTorusElt_conj_shortNegHom_of_ne {i j : Fin (n - 1)} (hij : j ≠ i) {a : Fin 2 → K}
    (ha : a ≠ 0) (p : Fin 2 → K) :
    shortTorusElt n hirr i a * shortNegHom n hirr j (.ofAdd p) * (shortTorusElt n hirr i a)⁻¹ =
      shortNegHom n hirr j (.ofAdd (planeRefl b c a (planeRefl b c planeOne p))) := by
  rw [conj_shortNegHom_of_fVec n hirr _ j (r := 1)
    (by rw [one_smul]; exact spinAction_shortTorusElt_fVec_of_ne n hirr hij a)
    (spinAction_shortTorusElt_planeVec n hirr i ha p), one_smul]

end CFSG.LieType.Universal.Spin.Twisted
