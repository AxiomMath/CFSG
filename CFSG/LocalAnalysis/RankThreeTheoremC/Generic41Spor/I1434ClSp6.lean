module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSp6Aux
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.GH74.KGroups.FieldGF

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.GH74.KGroups Matrix

namespace Sp6

@[expose] def omega4 : GF4 := GF4.ofNat' 2

@[expose] def tMat : Matrix (Fin 2) (Fin 2) GF4 := !![0, 1; 1, omega4]

@[expose] def sMat : Matrix (Fin 2) (Fin 2) GF4 := !![0, 1; 1, 0]

theorem card_gf4 : Fintype.card GF4 = 4 := by decide

theorem tMat_det : tMat.det = 1 := by decide +kernel

theorem sMat_det : sMat.det = 1 := by decide +kernel

theorem tMat_pow_five : tMat ^ 5 = 1 := by decide +kernel

theorem sMat_mul_tMat : sMat * tMat = tMat ^ 4 * sMat := by decide +kernel

theorem tMat_det_pow : ∀ a : Fin 5, (tMat ^ (a : ℕ) - 1).det = 0 ↔ a = 0 := by decide +kernel

theorem tMat_pow_eq_one : ∀ a : Fin 5, tMat ^ (a : ℕ) = 1 → a = 0 := by decide +kernel

variable {F : Type} [Field F]

noncomputable def psi4 [Fintype F] (hF : Fintype.card F = 4) : GF4 ≃+* F :=
  FiniteField.ringEquivOfCardEq (by rw [hF, card_gf4])

noncomputable def slOfGf4 [Fintype F] (hF : Fintype.card F = 4) (M : Matrix (Fin 2) (Fin 2) GF4)
    (h : M.det = 1) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨M.map (psi4 hF), by
    rw [show M.map (psi4 hF) = (psi4 hF).toRingHom.mapMatrix M from rfl, ← RingHom.map_det, h]
    exact map_one _⟩

noncomputable def tSL [Fintype F] (hF : Fintype.card F = 4) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  slOfGf4 hF tMat tMat_det

noncomputable def sSL [Fintype F] (hF : Fintype.card F = 4) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  slOfGf4 hF sMat sMat_det

section Fin4

variable [Fintype F]

theorem coe_tSL_pow (hF : Fintype.card F = 4) (n : ℕ) :
    ((tSL hF ^ n : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (tMat ^ n).map (psi4 hF) := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show ((tMat.map (psi4 hF)) ^ n) = _
  have : tMat.map (psi4 hF) = (psi4 hF).toRingHom.mapMatrix tMat := rfl
  rw [this, ← map_pow]
  rfl

theorem tSL_pow_five (hF : Fintype.card F = 4) : tSL hF ^ 5 = 1 := by
  apply Subtype.ext
  rw [coe_tSL_pow, tMat_pow_five]
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

abbrev matG (x : ↥(StatedSp 3 F)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  ((x : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)

theorem mulVec_lam (j : Fin 3) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (w : Fin 3 ⊕ Fin 3 → F) (x : Fin 3 ⊕ Fin 3) :
    (matG (lam j g)).mulVec w x =
      if x = Sum.inl j then (g : Matrix (Fin 2) (Fin 2) F) 0 0 * w (Sum.inl j) +
          (g : Matrix (Fin 2) (Fin 2) F) 0 1 * w (Sum.inr j)
      else if x = Sum.inr j then (g : Matrix (Fin 2) (Fin 2) F) 1 0 * w (Sum.inl j) +
          (g : Matrix (Fin 2) (Fin 2) F) 1 1 * w (Sum.inr j)
      else w x := by
  have hab : (Sum.inl j : Fin 3 ⊕ Fin 3) ≠ Sum.inr j := Sum.inl_ne_inr
  rw [show matG (lam j g) = pairMat (Sum.inl j) (Sum.inr j) (g : Matrix (Fin 2) (Fin 2) F) from
    coe_lam j g]
  simp only [Matrix.mulVec, dotProduct]
  by_cases h1 : x = Sum.inl j
  · subst h1
    rw [if_pos rfl, Fintype.sum_eq_add (Sum.inl j) (Sum.inr j) hab]
    · simp [pairMat_apply_fst, hab.symm]
    · intro z hz
      rw [pairMat_apply_fst_of_ne hz.1 hz.2, zero_mul]
  · by_cases h2 : x = Sum.inr j
    · subst h2
      rw [if_neg h1, if_pos rfl, Fintype.sum_eq_add (Sum.inl j) (Sum.inr j) hab]
      · simp [pairMat_apply_snd hab, hab.symm]
      · intro z hz
        rw [pairMat_apply_snd_of_ne hab hz.1 hz.2, zero_mul]
    · rw [if_neg h1, if_neg h2]
      rw [Finset.sum_eq_single x]
      · rw [pairMat_apply_of_ne h1 h2, one_apply_eq, one_mul]
      · intro z _ hzx
        rw [pairMat_apply_of_ne h1 h2, one_apply_ne (Ne.symm hzx), zero_mul]
      · simp

@[expose] noncomputable def tor3 (g : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) F) :
    ↥(StatedSp 3 F) :=
  lam 0 (g 0) * lam 1 (g 1) * lam 2 (g 2)

theorem matG_tor3 (g : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) F) :
    matG (tor3 g) = matG (lam 0 (g 0)) * matG (lam 1 (g 1)) * matG (lam 2 (g 2)) := rfl

theorem mulVec_tor3_inl (g : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) F)
    (w : Fin 3 ⊕ Fin 3 → F) (j : Fin 3) :
    (matG (tor3 g)).mulVec w (Sum.inl j) =
      (g j : Matrix (Fin 2) (Fin 2) F) 0 0 * w (Sum.inl j) +
        (g j : Matrix (Fin 2) (Fin 2) F) 0 1 * w (Sum.inr j) := by
  rw [matG_tor3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  fin_cases j <;> simp only [mulVec_lam] <;> simp

theorem mulVec_tor3_inr (g : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) F)
    (w : Fin 3 ⊕ Fin 3 → F) (j : Fin 3) :
    (matG (tor3 g)).mulVec w (Sum.inr j) =
      (g j : Matrix (Fin 2) (Fin 2) F) 1 0 * w (Sum.inl j) +
        (g j : Matrix (Fin 2) (Fin 2) F) 1 1 * w (Sum.inr j) := by
  rw [matG_tor3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  fin_cases j <;> simp only [mulVec_lam] <;> simp

theorem tor3_mul (g g' : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) F) :
    tor3 g * tor3 g' = tor3 (fun j => g j * g' j) := by
  unfold tor3
  rw [survivor_mul_comm_three (commute_lam_lam (by decide) _ _) (commute_lam_lam (by decide) _ _)
    (commute_lam_lam (by decide) _ _)]
  simp only [map_mul]

theorem tSL_pow_val_add (hF : Fintype.card F = 4) (x y : ZMod 5) :
    tSL hF ^ (x + y).val = tSL hF ^ x.val * tSL hF ^ y.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ (tSL_pow_five hF)]

@[expose] noncomputable def torus (hF : Fintype.card F = 4) (v : Fin 3 → ZMod 5) :
    ↥(StatedSp 3 F) :=
  tor3 (fun j => tSL hF ^ (v j).val)

theorem torus_add (hF : Fintype.card F = 4) (v w : Fin 3 → ZMod 5) :
    torus hF (v + w) = torus hF v * torus hF w := by
  unfold torus
  rw [tor3_mul]
  congr 1
  funext j
  exact tSL_pow_val_add hF (v j) (w j)

@[expose] noncomputable def torHom (hF : Fintype.card F = 4) :
    Multiplicative (Fin 3 → ZMod 5) →* ↥(StatedSp 3 F) :=
  MonoidHom.mk' (fun v => torus hF (Multiplicative.toAdd v)) (fun v w => torus_add hF _ _)

theorem torHom_apply (hF : Fintype.card F = 4) (v : Fin 3 → ZMod 5) :
    torHom hF (Multiplicative.ofAdd v) = torus hF v := rfl

theorem coe_tSL_pow_eq_one_iff (hF : Fintype.card F = 4) (n : ℕ) :
    ((tSL hF ^ n : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 ↔
      tMat ^ n = 1 := by
  rw [coe_tSL_pow]
  constructor
  · intro h
    have h1 : (tMat ^ n).map (psi4 hF) = (1 : Matrix (Fin 2) (Fin 2) GF4).map (psi4 hF) := by
      rw [h]
      ext i j
      simp [Matrix.one_apply]
    exact Matrix.map_injective (psi4 hF).injective h1
  · intro h
    rw [h]
    ext i j
    simp [Matrix.one_apply]

theorem torus_val_eq_zero (hF : Fintype.card F = 4) {v : Fin 3 → ZMod 5} (hv : torus hF v = 1)
    (j : Fin 3) : v j = 0 := by
  have hg : ((tSL hF ^ (v j).val : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h00 := mulVec_tor3_inl (fun j => tSL hF ^ (v j).val) (Pi.single (Sum.inl j) 1) j
    have h01 := mulVec_tor3_inl (fun j => tSL hF ^ (v j).val) (Pi.single (Sum.inr j) 1) j
    have h10 := mulVec_tor3_inr (fun j => tSL hF ^ (v j).val) (Pi.single (Sum.inl j) 1) j
    have h11 := mulVec_tor3_inr (fun j => tSL hF ^ (v j).val) (Pi.single (Sum.inr j) 1) j
    have hv' : matG (tor3 (fun j => tSL hF ^ (v j).val)) = 1 := congrArg matG hv
    rw [hv'] at h00 h01 h10 h11
    simp [Sum.inl_ne_inr, Sum.inr_ne_inl] at h00 h01 h10 h11
    ext a b
    fin_cases a <;> fin_cases b
    · simpa using h00.symm
    · simpa using h01.symm
    · simpa using h10.symm
    · simpa using h11.symm
  rw [coe_tSL_pow_eq_one_iff] at hg
  have hlt : (v j).val < 5 := ZMod.val_lt (v j)
  have := tMat_pow_eq_one ⟨(v j).val, hlt⟩ hg
  have h0 : (v j).val = 0 := congrArg Fin.val this
  exact (ZMod.val_eq_zero (v j)).1 h0

theorem torus_injective (hF : Fintype.card F = 4) : Function.Injective (torHom hF) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  funext j
  exact torus_val_eq_zero hF hv j

theorem eq_zero_of_det_ne_zero (M : Matrix (Fin 2) (Fin 2) F) (hM : (M - 1).det ≠ 0) (a b : F)
    (e1 : M 0 0 * a + M 0 1 * b = a) (e2 : M 1 0 * a + M 1 1 * b = b) : a = 0 ∧ b = 0 := by
  have hd : (M - 1).det = (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 := by
    simp [Matrix.det_fin_two]
  rw [hd] at hM
  constructor
  · have h : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * a = 0 := by
      linear_combination (M 1 1 - 1) * e1 - M 0 1 * e2
    exact (mul_eq_zero.1 h).resolve_left hM
  · have h : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * b = 0 := by
      linear_combination (M 0 0 - 1) * e2 - M 1 0 * e1
    exact (mul_eq_zero.1 h).resolve_left hM

theorem det_tSL_pow_sub_one_ne_zero (hF : Fintype.card F = 4) {x : ZMod 5} (hx : x ≠ 0) :
    (((tSL hF ^ x.val : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      1).det ≠ 0 := by
  rw [coe_tSL_pow]
  have h1 : (tMat ^ x.val).map (psi4 hF) - 1 =
      (psi4 hF).toRingHom.mapMatrix (tMat ^ x.val - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [h1, ← RingHom.map_det]
  intro h0
  have h2 := (psi4 hF).injective (h0.trans (map_zero (psi4 hF).toRingHom).symm)
  have hlt : x.val < 5 := ZMod.val_lt x
  have h3 := (tMat_det_pow ⟨x.val, hlt⟩).1 h2
  exact hx ((ZMod.val_eq_zero x).1 (congrArg Fin.val h3))

theorem eq_zero_of_mulVec_torus (hF : Fintype.card F = 4) (v : Fin 3 → ZMod 5)
    (hv : ∀ j, v j ≠ 0) (w : Fin 3 ⊕ Fin 3 → F)
    (hw : (matG (torus hF v) - 1).mulVec w = 0) : w = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw
  funext y
  rcases y with j | j
  · have e1 := congrFun hw (Sum.inl j)
    have e2 := congrFun hw (Sum.inr j)
    rw [show torus hF v = tor3 (fun j => tSL hF ^ (v j).val) from rfl] at e1 e2
    rw [mulVec_tor3_inl] at e1
    rw [mulVec_tor3_inr] at e2
    exact (eq_zero_of_det_ne_zero _ (det_tSL_pow_sub_one_ne_zero hF (hv j)) _ _ e1 e2).1
  · have e1 := congrFun hw (Sum.inl j)
    have e2 := congrFun hw (Sum.inr j)
    rw [show torus hF v = tor3 (fun j => tSL hF ^ (v j).val) from rfl] at e1 e2
    rw [mulVec_tor3_inl] at e1
    rw [mulVec_tor3_inr] at e2
    exact (eq_zero_of_det_ne_zero _ (det_tSL_pow_sub_one_ne_zero hF (hv j)) _ _ e1 e2).2

@[expose] def plane (x : Fin 3 ⊕ Fin 3) : Fin 3 := Sum.elim id id x

theorem mulVec_torus_single (hF : Fintype.card F = 4) (v : Fin 3 → ZMod 5) (x : Fin 3 ⊕ Fin 3)
    (hx : v (plane x) = 0) :
    (matG (torus hF v)).mulVec (Pi.single x (1 : F)) = Pi.single x 1 := by
  funext y
  have hg : ∀ l, v l = 0 → ((tSL hF ^ (v l).val : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    intro l hl
    rw [hl]
    simp
  rcases y with l | l
  · show (matG (tor3 (fun j => tSL hF ^ (v j).val))).mulVec _ _ = _
    rw [mulVec_tor3_inl]
    by_cases hl : l = plane x
    · subst hl
      rw [hg _ hx]
      rcases x with x | x <;> simp [plane] at hx ⊢
    · have h1 : (Pi.single x (1 : F) : Fin 3 ⊕ Fin 3 → F) (Sum.inl l) = 0 := by
        rw [Pi.single_apply, if_neg]
        rintro rfl
        exact hl rfl
      have h2 : (Pi.single x (1 : F) : Fin 3 ⊕ Fin 3 → F) (Sum.inr l) = 0 := by
        rw [Pi.single_apply, if_neg]
        rintro rfl
        exact hl rfl
      rw [h1, h2]
      simp
  · show (matG (tor3 (fun j => tSL hF ^ (v j).val))).mulVec _ _ = _
    rw [mulVec_tor3_inr]
    by_cases hl : l = plane x
    · subst hl
      rw [hg _ hx]
      rcases x with x | x <;> simp [plane] at hx ⊢
    · have h1 : (Pi.single x (1 : F) : Fin 3 ⊕ Fin 3 → F) (Sum.inl l) = 0 := by
        rw [Pi.single_apply, if_neg]
        rintro rfl
        exact hl rfl
      have h2 : (Pi.single x (1 : F) : Fin 3 ⊕ Fin 3 → F) (Sum.inr l) = 0 := by
        rw [Pi.single_apply, if_neg]
        rintro rfl
        exact hl rfl
      rw [h1, h2]
      simp

theorem four_le_finrank_ker (hF : Fintype.card F = 4) {v : Fin 3 → ZMod 5} {i j : Fin 3}
    (hij : i ≠ j) (hi : v i = 0) (hj : v j = 0) :
    4 ≤ Module.finrank F (LinearMap.ker (Matrix.toLin' (matG (torus hF v) - 1))) := by
  let e : Fin 4 → Fin 3 ⊕ Fin 3 := ![Sum.inl i, Sum.inr i, Sum.inl j, Sum.inr j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [e, hij, hij.symm, Sum.inl_ne_inr, Sum.inr_ne_inl] at hab ⊢
  have := survivor_card_le_finrank_ker (matG (torus hF v) - 1) 1 1 (Matrix.one_mul 1) e he
    (fun s => by
      have hpl : v (plane (e s)) = 0 := by
        fin_cases s <;> simp [e, plane, hi, hj]
      rw [Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        mulVec_torus_single hF v _ hpl, sub_self])
  simpa using this

theorem exactly_one_zero (hF : Fintype.card F = 4) {v : Fin 3 → ZMod 5}
    (h : Module.finrank F (LinearMap.ker (Matrix.toLin' (matG (torus hF v) - 1))) = 2) :
    (v 0 = 0 ∧ v 1 ≠ 0 ∧ v 2 ≠ 0) ∨ (v 0 ≠ 0 ∧ v 1 = 0 ∧ v 2 ≠ 0) ∨
      (v 0 ≠ 0 ∧ v 1 ≠ 0 ∧ v 2 = 0) := by
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0
  · have := four_le_finrank_ker hF (v := v) (i := 0) (j := 1) (by decide) h0 h1
    omega
  · have := four_le_finrank_ker hF (v := v) (i := 0) (j := 1) (by decide) h0 h1
    omega
  · have := four_le_finrank_ker hF (v := v) (i := 0) (j := 2) (by decide) h0 h2
    omega
  · exact Or.inl ⟨h0, h1, h2⟩
  · have := four_le_finrank_ker hF (v := v) (i := 1) (j := 2) (by decide) h1 h2
    omega
  · exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
  · have hv : ∀ j, v j ≠ 0 := by
      intro j
      fin_cases j <;> assumption
    have hbot : LinearMap.ker (Matrix.toLin' (matG (torus hF v) - 1)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      rw [Matrix.toLin'_apply] at hw
      exact eq_zero_of_mulVec_torus hF v hv w hw
    rw [hbot, finrank_bot] at h
    omega

theorem factorization_card_statedSp (hF : Fintype.card F = 4) :
    (Nat.card ↥(StatedSp 3 F)).factorization 5 = 3 := by
  have hcardF : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  rw [SymplecticFlag.card_statedSp, hcardF]
  have h : (4 ^ 3 ^ 2 * ∏ j ∈ Finset.Icc 1 3, (4 ^ (2 * j) - 1) : ℕ) =
      5 ^ 3 * (4 ^ 9 * (3 * 51 * 819)) := by decide +kernel
  have h5 : Nat.factorization (4 ^ 9 * (3 * 51 * 819)) 5 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, h5,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
  simp

theorem sSL_mul_tSL (hF : Fintype.card F = 4) : sSL hF * tSL hF = tSL hF ^ 4 * sSL hF := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tSL_pow]
  have h := congrArg ((psi4 hF).toRingHom.mapMatrix) sMat_mul_tMat
  rw [map_mul, map_mul] at h
  exact h

theorem sSL_conj_tSL (hF : Fintype.card F = 4) : sSL hF * tSL hF * (sSL hF)⁻¹ = (tSL hF)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, sSL_mul_tSL]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact tSL_pow_five hF

theorem tSL_pow_val_neg (hF : Fintype.card F = 4) (x : ZMod 5) :
    (tSL hF ^ x.val)⁻¹ = tSL hF ^ (-x).val := by
  apply inv_eq_of_mul_eq_one_right
  rw [← tSL_pow_val_add, add_neg_cancel, ZMod.val_zero, pow_zero]

theorem sSL_conj_tSL_pow (hF : Fintype.card F = 4) (x : ZMod 5) :
    sSL hF * tSL hF ^ x.val * (sSL hF)⁻¹ = tSL hF ^ (-x).val := by
  have h : (MulAut.conj (sSL hF)) (tSL hF ^ x.val) = ((MulAut.conj (sSL hF)) (tSL hF)) ^ x.val :=
    map_pow _ _ _
  rw [MulAut.conj_apply, MulAut.conj_apply, sSL_conj_tSL, inv_pow] at h
  rw [h, tSL_pow_val_neg]

@[expose] noncomputable def torus3 (hF : Fintype.card F = 4) (a b c : ZMod 5) : ↥(StatedSp 3 F) :=
  torus hF ![a, b, c]

theorem torus3_eq (hF : Fintype.card F = 4) (a b c : ZMod 5) :
    torus3 hF a b c = lam 0 (tSL hF ^ a.val) * lam 1 (tSL hF ^ b.val) * lam 2 (tSL hF ^ c.val) :=
  rfl

theorem torus_eq_torus3 (hF : Fintype.card F = 4) (v : Fin 3 → ZMod 5) :
    torus hF v = torus3 hF (v 0) (v 1) (v 2) := by
  unfold torus3
  congr 1
  funext j
  fin_cases j <;> rfl

theorem conj_lam_self (j : Fin 3) (s g : Matrix.SpecialLinearGroup (Fin 2) F) :
    lam j s * lam j g * (lam j s)⁻¹ = lam (k := F) j (s * g * s⁻¹) := by
  simp [map_mul, map_inv]

theorem conj_iota1 (hF : Fintype.card F = 4) (a b c : ZMod 5) :
    lam 1 (sSL hF) * torus3 hF a b c * (lam 1 (sSL hF))⁻¹ = torus3 hF a (-b) c := by
  have h0 := (commute_lam_lam (r := 3) (k := F) (i := 1) (j := 0) (by decide) (sSL hF)
    (tSL hF ^ a.val)).mul_inv_cancel
  have h2 := (commute_lam_lam (r := 3) (k := F) (i := 1) (j := 2) (by decide) (sSL hF)
    (tSL hF ^ c.val)).mul_inv_cancel
  rw [torus3_eq, torus3_eq, survivor_conj_mul_three, h0, h2, conj_lam_self, sSL_conj_tSL_pow]

theorem conj_iota2 (hF : Fintype.card F = 4) (a b c : ZMod 5) :
    lam 2 (sSL hF) * torus3 hF a b c * (lam 2 (sSL hF))⁻¹ = torus3 hF a b (-c) := by
  have h0 := (commute_lam_lam (r := 3) (k := F) (i := 2) (j := 0) (by decide) (sSL hF)
    (tSL hF ^ a.val)).mul_inv_cancel
  have h1 := (commute_lam_lam (r := 3) (k := F) (i := 2) (j := 1) (by decide) (sSL hF)
    (tSL hF ^ b.val)).mul_inv_cancel
  rw [torus3_eq, torus3_eq, survivor_conj_mul_three, h0, h1, conj_lam_self, sSL_conj_tSL_pow]

theorem conj_rho_lam_fst {i j : Fin 3} (hij : i ≠ j) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    rho i j hij sl2W * lam i g * (rho i j hij sl2W)⁻¹ = lam (k := F) j g := by
  have h := DFunLike.congr_fun (conj_rho_sl2W_comp_lam_fst (k := F) hij) g
  simpa [MulAut.conj_apply] using h

theorem conj_rho_lam_snd {i j : Fin 3} (hij : i ≠ j) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    rho i j hij sl2W * lam j g * (rho i j hij sl2W)⁻¹ = lam (k := F) i g := by
  have h := DFunLike.congr_fun (conj_rho_sl2W_comp_lam_snd (k := F) hij) g
  simpa [MulAut.conj_apply] using h

noncomputable def swap02 : ↥(StatedSp 3 F) := rho 0 2 (by decide) sl2W

noncomputable def swap12 : ↥(StatedSp 3 F) := rho 1 2 (by decide) sl2W

theorem conj_swap02 (hF : Fintype.card F = 4) (a b c : ZMod 5) :
    swap02 * torus3 hF a b c * swap02⁻¹ = torus3 hF c b a := by
  have h1 := (commute_rho_lam (r := 3) (k := F) (i := 0) (j := 2) (by decide) (l := 1)
    (by decide) (by decide) sl2W (tSL hF ^ b.val)).mul_inv_cancel
  rw [torus3_eq, torus3_eq, swap02, survivor_conj_mul_three, conj_rho_lam_fst, h1, conj_rho_lam_snd]
  exact survivor_rev_three (commute_lam_lam (by decide) _ _) (commute_lam_lam (by decide) _ _)
    (commute_lam_lam (by decide) _ _)

theorem conj_swap12 (hF : Fintype.card F = 4) (a b c : ZMod 5) :
    swap12 * torus3 hF a b c * swap12⁻¹ = torus3 hF a c b := by
  have h0 := (commute_rho_lam (r := 3) (k := F) (i := 1) (j := 2) (by decide) (l := 0)
    (by decide) (by decide) sl2W (tSL hF ^ a.val)).mul_inv_cancel
  rw [torus3_eq, torus3_eq, swap12, survivor_conj_mul_three, conj_rho_lam_fst, h0, conj_rho_lam_snd,
    mul_assoc, mul_assoc]
  rw [(commute_lam_lam (r := 3) (k := F) (i := 2) (j := 1) (by decide) _ _).eq]

noncomputable def cel (hF : Fintype.card F = 4) : Fin 6 → ↥(StatedSp 3 F) :=
  ![1, lam 1 (sSL hF), swap02, lam 2 (sSL hF) * swap02, swap12, lam 2 (sSL hF) * swap12]

@[expose] def wvec (a b : ZMod 5) : Fin 6 → Fin 3 → ZMod 5 :=
  ![![a, b, 0], ![a, -b, 0], ![0, b, a], ![0, b, -a], ![a, 0, b], ![a, 0, -b]]

theorem wvec_ne : ∀ a b : ZMod 5, a ≠ 0 → b ≠ 0 → ∀ i j : Fin 6, ∀ n : ZMod 5,
    (fun k => n * wvec a b i k) = wvec a b j → i = j := by
  decide +kernel

theorem cel_conj (hF : Fintype.card F = 4) (a b : ZMod 5) (i : Fin 6) :
    cel hF i * torus3 hF a b 0 * (cel hF i)⁻¹ = torus hF (wvec a b i) := by
  fin_cases i
  · simp [cel, wvec, torus3]
  · simp [cel, wvec]
    exact conj_iota1 hF a b 0
  · simp [cel, wvec]
    exact conj_swap02 hF a b 0
  · simp only [cel, wvec]
    show (lam 2 (sSL hF) * swap02) * torus3 hF a b 0 * (lam 2 (sSL hF) * swap02)⁻¹ =
      torus hF ![0, b, -a]
    rw [_root_.mul_inv_rev, show (lam 2 (sSL hF) * swap02) * torus3 hF a b 0 *
        (swap02⁻¹ * (lam 2 (sSL hF))⁻¹) = lam 2 (sSL hF) * (swap02 * torus3 hF a b 0 *
        swap02⁻¹) * (lam 2 (sSL hF))⁻¹ from by group, conj_swap02, conj_iota2]
    rfl
  · simp [cel, wvec]
    exact conj_swap12 hF a b 0
  · simp only [cel, wvec]
    show (lam 2 (sSL hF) * swap12) * torus3 hF a b 0 * (lam 2 (sSL hF) * swap12)⁻¹ =
      torus hF ![a, 0, -b]
    rw [_root_.mul_inv_rev, show (lam 2 (sSL hF) * swap12) * torus3 hF a b 0 *
        (swap12⁻¹ * (lam 2 (sSL hF))⁻¹) = lam 2 (sSL hF) * (swap12 * torus3 hF a b 0 *
        swap12⁻¹) * (lam 2 (sSL hF))⁻¹ from by group, conj_swap12, conj_iota2]
    rfl

theorem six_lines_of_normal_form (hF : Fintype.card F = 4) (g n : ↥(StatedSp 3 F))
    (v : Fin 3 → ZMod 5) (a b : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0)
    (hn : n * torus hF v * n⁻¹ = torus3 hF a b 0) :
    6 ≤ Set.ncard {B : Subgroup ↥(StatedSp 3 F) | ∃ g' : ↥(StatedSp 3 F),
      B = (Subgroup.zpowers (g * torus hF v * g⁻¹)).map (MulAut.conj g').toMonoidHom ∧
        B ≤ (torHom hF).range.map (MulAut.conj g).toMonoidHom} := by
  refine survivor_lines_torus (torHom hF) (torus_injective hF) g v
    (fun i => cel hF i * n) (fun i => wvec a b i) ?_ ?_
  · intro i
    show (cel hF i * n) * torus hF v * (cel hF i * n)⁻¹ = torus hF (wvec a b i)
    calc (cel hF i * n) * torus hF v * (cel hF i * n)⁻¹
        = cel hF i * (n * torus hF v * n⁻¹) * (cel hF i)⁻¹ := by group
      _ = torus hF (wvec a b i) := by rw [hn]; exact cel_conj hF a b i
  · intro i j m hm
    exact wvec_ne a b ha hb i j m hm

theorem finrank_ker_conj_sp (g A : ↥(StatedSp 3 F)) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (matG (g⁻¹ * A * g) - 1))) =
      Module.finrank F (LinearMap.ker (Matrix.toLin' (matG A - 1))) := by
  have h := survivor_finrank_ker_conj (g : GL (Fin 3 ⊕ Fin 3) F) (matG A - 1)
  have e : matG (g⁻¹ * A * g) - 1 = (((g : GL (Fin 3 ⊕ Fin 3) F)⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * (matG A - 1) *
        ((g : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    have h1 : (((g : GL (Fin 3 ⊕ Fin 3) F)⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
        ((g : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    symm
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rfl
  rw [e]
  exact h

end Fin4

end Sp6

theorem dsp6_lines {F : Type} [Field F] [Fintype F] [DecidableEq F] (hF : Fintype.card F = 4)
    (Q : Sylow 5 ↥(StatedSp 3 F)) (A : ↥(StatedSp 3 F)) (hAQ : A ∈ (Q : Subgroup ↥(StatedSp 3 F)))
    (hA5 : A ^ 5 = 1) (hA1 : A ≠ 1)
    (hker : Module.finrank F (LinearMap.ker (Matrix.toLin' (((A : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) - 1))) = 2) :
    6 ≤ Set.ncard {B : Subgroup ↥(StatedSp 3 F) | ∃ g : ↥(StatedSp 3 F),
      B = (Subgroup.zpowers A).map (MulAut.conj g).toMonoidHom ∧
        B ≤ (Q : Subgroup ↥(StatedSp 3 F))} := by
  obtain ⟨g, v, hAeq, hQeq⟩ := survivor_exists_conj_torus (Sp6.torHom hF) (Sp6.torus_injective hF)
    (Sp6.factorization_card_statedSp hF) Q hAQ
  rw [Sp6.torHom_apply] at hAeq
  have hker' : Module.finrank F (LinearMap.ker (Matrix.toLin'
      (Sp6.matG (Sp6.torus hF v) - 1))) = 2 := by
    have hv : Sp6.torus hF v = g⁻¹ * A * g := by rw [hAeq]; group
    rw [hv, Sp6.finrank_ker_conj_sp]
    exact hker
  rw [hQeq, hAeq]
  rcases Sp6.exactly_one_zero hF hker' with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine Sp6.six_lines_of_normal_form hF g Sp6.swap02 v (v 2) (v 1) h2 h1 ?_
    rw [Sp6.torus_eq_torus3, h0, Sp6.conj_swap02]
  · refine Sp6.six_lines_of_normal_form hF g Sp6.swap12 v (v 0) (v 2) h0 h2 ?_
    rw [Sp6.torus_eq_torus3, h1, Sp6.conj_swap12]
  · refine Sp6.six_lines_of_normal_form hF g 1 v (v 0) (v 1) h0 h1 ?_
    rw [Sp6.torus_eq_torus3, h2]
    simp

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
