module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreClaimR

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSU3Core

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F CFSG.RankThree.PartTwo.Sec19.U38F
  CFSG.RankThree.PartTwo.Sec19 Matrix

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section R

variable {F : Type} [Field F]

theorem regFlag_sound (ι : Q8 →+* F) {A : M3 Q8} (G : GL (Fin 3) F)
    (hG : (G : Matrix (Fin 3) (Fin 3) F) = toMat ι A) (hA : KSU38R.regFlag A = true) :
    RegularU38 G := by
  simp only [KSU38R.regFlag, Bool.and_eq_true, decide_eq_true_eq] at hA
  obtain ⟨⟨hsc, hc3⟩, hcyc⟩ := hA
  refine ⟨⟨ι (A * A * A).a00, ?_, ?_⟩, ?_⟩
  · rw [← map_pow, hc3, map_one]
  · rw [hG, pow_three', ← toMat_mul, ← toMat_mul]
    exact toMat_scalar_of_isScalar ι hsc
  · rintro ⟨a, b, hab⟩
    rw [hG, pow_two] at hab
    unfold KSU38R.hasCyc at hcyc
    obtain ⟨v, -, hv⟩ := List.any_eq_true.1 hcyc
    have hv' : KSU38R.cycDet A v ≠ 0 := of_decide_eq_true hv
    have e00 := congrFun (congrFun hab 0) 0
    have e01 := congrFun (congrFun hab 0) 1
    have e02 := congrFun (congrFun hab 0) 2
    have e10 := congrFun (congrFun hab 1) 0
    have e11 := congrFun (congrFun hab 1) 1
    have e12 := congrFun (congrFun hab 1) 2
    have e20 := congrFun (congrFun hab 2) 0
    have e21 := congrFun (congrFun hab 2) 1
    have e22 := congrFun (congrFun hab 2) 2
    simp [toMat, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
    have hdet : ι (KSU38R.cycDet A v) = 0 := by
      unfold KSU38R.cycDet
      simp only [M3.det, ofCols, KSU38R.mulVec, map_sub, map_add, map_mul]
      set x := ι v.1
      set y := ι v.2.1
      set z := ι v.2.2
      set w0 := ι A.a00 * x + ι A.a01 * y + ι A.a02 * z
      set w1 := ι A.a10 * x + ι A.a11 * y + ι A.a12 * z
      set w2 := ι A.a20 * x + ι A.a21 * y + ι A.a22 * z
      linear_combination ((y * w2 - z * w1) * x) * e00 + ((y * w2 - z * w1) * y) * e01 +
        ((y * w2 - z * w1) * z) * e02 + ((z * w0 - x * w2) * x) * e10 +
        ((z * w0 - x * w2) * y) * e11 + ((z * w0 - x * w2) * z) * e12 +
        ((x * w1 - y * w0) * x) * e20 + ((x * w1 - y * w0) * y) * e21 +
        ((x * w1 - y * w0) * z) * e22
    exact hv' ((map_eq_zero ι).1 hdet)

theorem regFlag_exists_of_dCheck {d Z : M3 Q8}
    (hd : d ∈ (u38Table.drop 3).map (·.Y)) (hZe : entriesL4 Z = true) (hZu : unitaryOk Z = true)
    (hZ3 : isScalar (Z * Z * Z) = true) (hZs : isScalar Z = false)
    (hcm : KSU38R.commMod d Z = true) (hp1 : KSU38R.propto Z d = false)
    (hp2 : KSU38R.propto Z (d * d) = false) :
    ∃ j : ℕ, j < 3 ∧ KSU38R.regFlag (KSU38R.mpow d j * Z) = true := by
  have hD : KSU38R.dCheck () = true := (u38RCheck_parts).2.2.2.2.2
  have h1 : KSU38R.dCheckOne d = true := by
    unfold KSU38R.dCheck at hD
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
    exact List.all_eq_true.1 hD y hy
  unfold KSU38R.dCheckOne at h1
  have h2 := forallUnitary_sound h1 hZe hZu
  simp only [hZ3, hZs, hcm, hp1, hp2, Bool.not_true, Bool.false_or, Bool.or_false,
    Bool.not_false] at h2
  obtain ⟨j, hj, hreg⟩ := List.any_eq_true.1 h2
  exact ⟨j, List.mem_range.1 hj, hreg⟩

theorem exists_regular_of_commMod (h : UnitaryFieldData 2 3 F)
    {ι : Q8 →+* F} (hι : Function.Surjective ι) {d Z : M3 Q8}
    (hd : d ∈ (u38Table.drop 3).map (·.Y)) (hdu : unitaryOk d = true)
    (hZu : unitaryOk Z = true) (hZe : entriesL4 Z = true)
    (hZ3 : isScalar (Z * Z * Z) = true) (hZs : isScalar Z = false)
    (hcm : KSU38R.commMod d Z = true) (hp1 : KSU38R.propto Z d = false)
    (hp2 : KSU38R.propto Z (d * d) = false) :
    ∃ j : ℕ, j < 3 ∧ ∃ Y : unitaryIsom3 h, RegularU38 (Y : GL (Fin 3) F) ∧
      suConj h Y = suConj h (toIsom h ι d hdu) ^ j * suConj h (toIsom h ι Z hZu) := by
  obtain ⟨j, hj, hreg⟩ := regFlag_exists_of_dCheck hd hZe hZu hZ3 hZs hcm hp1 hp2
  refine ⟨j, hj, toIsom h ι d hdu ^ j * toIsom h ι Z hZu, ?_, by rw [map_mul, map_pow]⟩
  refine regFlag_sound ι _ ?_ hreg
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_toIsom,
    coe_toIsom, toMat_mul, toMat_mpow]

end R

section Witness

variable {F : Type} [Field F]

theorem witness_e0Check_parts :
    sgOk (KSU38R.e0 ()) = true ∧ entriesL4 (KSU38R.e0 ()) = true ∧
      KSU38R.e0 () * KSU38R.e0 () * KSU38R.e0 () = 1 ∧ isScalar (KSU38R.e0 ()) = false ∧
      (∀ y ∈ u38Table, KSU38R.commMod (KSU38R.e0 ()) y.Y = true ∧
        KSU38R.propto (KSU38R.e0 ()) y.Y = false ∧
        KSU38R.propto (KSU38R.e0 ()) (y.Y * y.Y) = false) ∧
      ∀ y ∈ u38Table.drop 3, commutes (KSU38R.e0 ()) y.Y = true := by
  have h := (u38RCheck_parts).2.2.2.1
  simp only [KSU38R.e0Check, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, fun y hy => ⟨(h5 y hy).1.1, (h5 y hy).1.2, (h5 y hy).2⟩, h6⟩

theorem witness_exists_su_e0 (h : UnitaryFieldData 2 3 F)
    (ι : Q8 →+* F) :
    ∃ e : unitarySU 2 3 F 3,
      ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι (KSU38R.e0 ()) := by
  obtain ⟨hsg, -⟩ := witness_e0Check_parts
  obtain ⟨hdet, -⟩ := sgOk_spec hsg
  have hu : unitaryOk (KSU38R.e0 ()) = true := by
    unfold sgOk at hsg
    rw [Bool.and_eq_true] at hsg
    exact hsg.2
  exact exists_su_of_matrix h (by rw [toMat_det, hdet, map_one]) (toMat_unitary h ι hu)

theorem witness_pow_three_eq_one {ι : Q8 →+* F} {e : unitarySU 2 3 F 3} {E : M3 Q8}
    (he : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι E)
    (hE : E * E * E = 1) : e ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h1 : toMat ι E * toMat ι E * toMat ι E = 1 := by
    rw [← toMat_mul, ← toMat_mul, hE, toMat_one]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, Subgroup.coe_one, Units.val_one]
  rw [pow_succ, pow_succ, pow_one]
  exact h1

theorem witness_suField_eq_self (h : UnitaryFieldData 2 3 F) {σ : F ≃+* F} {ι : Q8 →+* F}
    (hσω : σ (ι w0) = ι w0) {e : unitarySU 2 3 F 3} {E : M3 Q8}
    (he : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι E)
    (hE : entriesL4 E = true) : suField h σ e = e := by
  apply Subtype.ext
  rw [coe_suField, glAut_eq_iff]
  intro i j
  rw [he]
  exact congrFun (congrFun (map_toMat_fixed ι hσω hE) i) j

theorem witness_conj_ne_one (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F}
    {e : unitarySU 2 3 F 3} {E : M3 Q8}
    (he : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι E)
    (hE : isScalar E = false) : MulAut.conj e ≠ 1 := by
  intro h1
  have hq : 2 < 2 ^ 3 := by norm_num
  have hz : e ∈ Subgroup.center (unitarySU 2 3 F 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg (fun χ : MulAut (unitarySU 2 3 F 3) => χ y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc y * e = e * y * e⁻¹ * e := by rw [h2]
      _ = e * y := by group
  rw [center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, -, -, hzc⟩ := hz
  have hsc : toMat ι E = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← he, hzc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have h3 := isScalar_of_toMat ι hsc
  rw [hE] at h3
  exact Bool.false_ne_true h3

theorem witness_mem_center_of_smul_one {z : unitarySU 2 3 F 3} {a : F}
    (hz : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = a • (1 : Matrix (Fin 3) (Fin 3) F)) :
    z ∈ Subgroup.center (unitarySU 2 3 F 3) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

theorem witness_exists_central_of_commMod (h : UnitaryFieldData 2 3 F) (Y : unitaryIsom3 h)
    (e : unitarySU 2 3 F 3) {c : F}
    (hc : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c • (((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) :
    ∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), suConj h Y e = e * z := by
  refine ⟨e⁻¹ * suConj h Y e, ?_, by rw [mul_inv_cancel_left]⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact Units.ne_zero ((e : GL (Fin 3) F) * (Y : GL (Fin 3) F)) (by rw [Units.val_mul]; exact hc)
  have hBA : ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c⁻¹ • (((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hAA := Units.inv_mul (e : GL (Fin 3) F)
  have hBB := Units.mul_inv (Y : GL (Fin 3) F)
  apply witness_mem_center_of_smul_one (a := c⁻¹)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj, Units.val_mul]
  rw [hBA, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc _ = (((e : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((Y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((Y : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hAA, hBB, Matrix.mul_one]

theorem witness_not_mem_zpowers (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F}
    (hι : Function.Surjective ι) {e : unitarySU 2 3 F 3} {E R : M3 Q8}
    (he : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι E)
    (hRu : unitaryOk R = true) (hR3 : isScalar (R * R * R) = true) (hEs : isScalar E = false)
    (hp1 : KSU38R.propto E R = false) (hp2 : KSU38R.propto E (R * R) = false) :
    MulAut.conj e ∉ Subgroup.zpowers (suConj h (toIsom h ι R hRu)) := by
  rintro ⟨k, hk⟩
  replace hk : suConj h (toIsom h ι R hRu) ^ k = MulAut.conj e := hk
  have hY3 : suConj h (toIsom h ι R hRu) ^ 3 = 1 := by
    have hsc := toMat_scalar_of_isScalar ι hR3
    rw [toMat_mul, toMat_mul] at hsc
    apply suConj_pow_eq_one_of_scalar h _ 3 (c := ι (R * R * R).a00)
    rw [coe_toIsom, pow_succ, pow_succ, pow_one]
    exact hsc
  have hY3' : suConj h (toIsom h ι R hRu) ^ (3 : ℤ) = 1 := by exact_mod_cast hY3
  rw [zpow_eq_zpow_emod k hY3'] at hk
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hce : MulAut.conj e =
      suConj h ⟨(e : GL (Fin 3) F), unitarySU_le_unitaryIsom3 e.2⟩ := by
    ext g
    rfl
  rcases hr with hr | hr | hr
  · rw [hr, zpow_zero] at hk
    exact witness_conj_ne_one h he hEs hk.symm
  · rw [hr, zpow_one, hce] at hk
    obtain ⟨c, hc⟩ := exists_matrix_eq_smul_of_suConj_eq h hk.symm
    have hc' : toMat ι E = c • toMat ι R := by
      rw [← he]
      exact hc
    obtain ⟨l, rfl⟩ := hι c
    have hE : E = M3.smul l R := toMat_inj ι (by rw [toMat_smul]; exact hc')
    have h4 : KSU38R.propto E R = true := decide_eq_true ⟨l, hE⟩
    rw [hp1] at h4
    exact Bool.false_ne_true h4
  · rw [hr, zpow_two, ← map_mul, hce] at hk
    obtain ⟨c, hc⟩ := exists_matrix_eq_smul_of_suConj_eq h hk.symm
    have hc' : toMat ι E = c • toMat ι (R * R) := by
      rw [toMat_mul, ← he]
      refine hc.trans ?_
      rw [Subgroup.coe_mul, Units.val_mul]
      rfl
    obtain ⟨l, rfl⟩ := hι c
    have hE : E = M3.smul l (R * R) := toMat_inj ι (by rw [toMat_smul]; exact hc')
    have h4 : KSU38R.propto E (R * R) = true := decide_eq_true ⟨l, hE⟩
    rw [hp2] at h4
    exact Bool.false_ne_true h4

theorem witness_suConj_eq_self_of_commutes (h : UnitaryFieldData 2 3 F) {ι : Q8 →+* F}
    {e : unitarySU 2 3 F 3} {E R : M3 Q8}
    (he : ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι E)
    (hRu : unitaryOk R = true) (hc : commutes E R = true) :
    suConj h (toIsom h ι R hRu) e = e := by
  have h1 : E * R = R * E := of_decide_eq_true hc
  have hm : ((toIsom h ι R hRu : unitaryIsom3 h) : GL (Fin 3) F) * (e : GL (Fin 3) F) =
      (e : GL (Fin 3) F) * ((toIsom h ι R hRu : unitaryIsom3 h) : GL (Fin 3) F) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_toIsom, he, ← toMat_mul, ← toMat_mul, h1]
  apply Subtype.ext
  rw [coe_suConj, Subgroup.coe_inv, hm, mul_inv_cancel_right]

theorem exists_witness (h : UnitaryFieldData 2 3 F)
    {σ : F ≃+* F} (hσ : orderOf σ = 3) {ι : Q8 →+* F} (hι : Function.Surjective ι)
    (hωι : IsPrimitiveRoot (ι w0) 3) (hσω : σ (ι w0) = ι w0) :
    ∃ e : unitarySU 2 3 F 3, e ^ 3 = 1 ∧ suField h σ e = e ∧ MulAut.conj e ≠ 1 ∧
      ∀ (R : M3 Q8) (hRu : unitaryOk R = true), R ∈ u38Table.map (·.Y) →
        (∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), suConj h (toIsom h ι R hRu) e = e * z) ∧
        MulAut.conj e ∉ Subgroup.zpowers (suConj h (toIsom h ι R hRu)) ∧
        (R ∈ (u38Table.drop 3).map (·.Y) → suConj h (toIsom h ι R hRu) e = e) := by
  obtain ⟨-, hE4, hE3, hEs, htab, hdrop⟩ := witness_e0Check_parts
  obtain ⟨e, he⟩ := witness_exists_su_e0 h ι
  have hrep := (u38RCheck_parts).2.2.1
  simp only [KSU38R.repCheck, Bool.and_eq_true, List.all_eq_true] at hrep
  refine ⟨e, witness_pow_three_eq_one he hE3, witness_suField_eq_self h hσω he hE4,
    witness_conj_ne_one h he hEs, ?_⟩
  intro R hRu hRmem
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hRmem
  obtain ⟨hcm, hp1, hp2⟩ := htab y hy
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := of_decide_eq_true hcm
    have h1 := congrArg (toMat ι) hl
    rw [toMat_mul, toMat_smul, toMat_mul] at h1
    refine witness_exists_central_of_commMod h _ e (c := ι l) ?_
    rw [coe_toIsom, he]
    exact h1
  · exact witness_not_mem_zpowers h hι he hRu (hrep y hy).2 hEs hp1 hp2
  · intro hd
    obtain ⟨y', hy', hyy'⟩ := List.mem_map.1 hd
    have hc : commutes (KSU38R.e0 ()) y.Y = true := by
      rw [← hyy']
      exact hdrop y' hy'
    exact witness_suConj_eq_self_of_commutes h he hRu hc

end Witness

section Dichotomy

variable {F : Type} [Field F]

theorem conj_apply_aut {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    MulAut.conj (γ x) = γ * MulAut.conj x * γ⁻¹ := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem conj_matrix_pow {N N' M : Matrix (Fin 3) (Fin 3) F} (hN : N' * N = 1) (hN2 : N * N' = 1)
    (n : ℕ) : (N * M * N') ^ n = N * M ^ n * N' := by
  induction n with
  | zero => simp [hN2]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc N * M ^ n * N' * (N * M * N') = N * M ^ n * (N' * N) * M * N' := by
          simp only [Matrix.mul_assoc]
      _ = N * (M ^ n * M) * N' := by rw [hN, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem regularU38_conj {Y : GL (Fin 3) F} (G : GL (Fin 3) F) (hY : RegularU38 Y) :
    RegularU38 (G * Y * G⁻¹) := by
  obtain ⟨⟨κ, hκ3, hκ⟩, hnr⟩ := hY
  have hN : ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (G : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hN2 : (G : Matrix (Fin 3) (Fin 3) F) * ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcoe : ((G * Y * G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * (Y : Matrix (Fin 3) (Fin 3) F) *
        ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    simp only [Units.val_mul]
  refine ⟨⟨κ, hκ3, ?_⟩, ?_⟩
  · rw [hcoe, conj_matrix_pow hN hN2, hκ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hN2]
  · rintro ⟨a, b, hab⟩
    apply hnr
    refine ⟨a, b, ?_⟩
    rw [hcoe, conj_matrix_pow hN hN2] at hab
    set N : Matrix (Fin 3) (Fin 3) F := (G : Matrix (Fin 3) (Fin 3) F) with hNdef
    set N' : Matrix (Fin 3) (Fin 3) F := ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN'def
    have e : ∀ X : Matrix (Fin 3) (Fin 3) F, N' * (N * X * N') * N = X := by
      intro X
      calc N' * (N * X * N') * N = (N' * N) * X * (N' * N) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hN, Matrix.one_mul, Matrix.mul_one]
    calc (Y : Matrix (Fin 3) (Fin 3) F) ^ 2 = N' * (N * (Y : Matrix (Fin 3) (Fin 3) F) ^ 2 * N') * N :=
          (e _).symm
      _ = N' * (a • (N * (Y : Matrix (Fin 3) (Fin 3) F) * N') + b • 1) * N := by rw [hab]
      _ = a • (N' * (N * (Y : Matrix (Fin 3) (Fin 3) F) * N') * N) + b • (N' * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one]
      _ = a • (Y : Matrix (Fin 3) (Fin 3) F) + b • 1 := by rw [e, hN]

section Inn

variable (h : UnitaryFieldData 2 3 F)

theorem exists_inn_mul_pow {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {A : Subgroup (MulAut (unitarySU 2 3 F 3))} (hA : IsElemAbelian 3 A) (hf : suField h σ ∈ A)
    {α : MulAut (unitarySU 2 3 F 3)} (hα : α ∈ A) :
    ∃ c ∈ A ⊓ (suConj h).range, ∃ k : ℕ, α = c * suField h σ ^ k := by
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨B, k, -, hk, -, -⟩ := exists_suConj_mul_suField_pow h hq hσ (hA.2 α hα) (hA.comm hα hf)
  refine ⟨suConj h B, ⟨?_, B, rfl⟩, k, hk⟩
  have : suConj h B = α * (suField h σ ^ k)⁻¹ := by rw [hk, mul_inv_cancel_right]
  rw [this]
  exact A.mul_mem hα (A.inv_mem (A.pow_mem hf k))

theorem exists_toIsom_of_mem_inn {σ : F ≃+* F} (hσ : orderOf σ = 3) {ι : Q8 →+* F}
    (hωι : IsPrimitiveRoot (ι w0) 3) {A : Subgroup (MulAut (unitarySU 2 3 F 3))}
    (hA : IsElemAbelian 3 A) (hf : suField h σ ∈ A) {a : MulAut (unitarySU 2 3 F 3)}
    (ha : a ∈ A ⊓ (suConj h).range) :
    ∃ (Ym : M3 Q8) (hu : unitaryOk Ym = true), entriesL4 Ym = true ∧
      a = suConj h (toIsom h ι Ym hu) := by
  have hd : a ∈ Dsub h σ :=
    Subgroup.mem_inf.2 ⟨ha.2, Subgroup.mem_centralizer_singleton_iff.2 (hA.comm ha.1 hf)⟩
  exact exists_toIsom_of_mem_Dsub h hσ hωι hd

theorem mpow_three_eq (ι : Q8 →+* F) (Ym : M3 Q8) : KSU38R.mpow Ym 3 = Ym * Ym * Ym := by
  apply toMat_inj ι
  rw [toMat_mpow, toMat_mul, toMat_mul, pow_three']

theorem exists_normalization
    {σ : F ≃+* F} {ι : Q8 →+* F} (hσω : σ (ι w0) = ι w0) {Ym : M3 Q8}
    (hu : unitaryOk Ym = true) (he : entriesL4 Ym = true) (hns : isScalar Ym = false)
    (h3 : isScalar (Ym * Ym * Ym) = true) :
    ∃ (R : M3 Q8) (_ : R ∈ u38Table.map (·.Y)) (hRu : unitaryOk R = true) (G : unitaryIsom3 h),
      glAut σ (G : GL (Fin 3) F) = G ∧
      suConj h (toIsom h ι Ym hu) = suConj h G * suConj h (toIsom h ι R hRu) * (suConj h G)⁻¹ := by
  have hq : 2 ^ 3 = 8 := by norm_num
  obtain ⟨e, hetab, g, hg, ⟨hgE, hgU⟩, l, hl, hYm⟩ :=
    class_sound Certificates.certificate188005 he hu hns h3
  have hrep := (u38RCheck_parts).2.2.1
  simp only [KSU38R.repCheck, List.all_eq_true, Bool.and_eq_true] at hrep
  obtain ⟨⟨hRu, -⟩, -⟩ := hrep e hetab
  refine ⟨e.Y, List.mem_map.2 ⟨e, hetab, rfl⟩, hRu, toIsom h ι g hgU, ?_, ?_⟩
  · rw [glAut_eq_iff]
    intro i j
    exact congrFun (congrFun (map_toMat_fixed ι hσω hgE) i) j
  · rw [← map_mul, ← map_inv, ← map_mul]
    apply suConj_eq_of_matrix_eq_smul h (c := ι l)
    have hinv : (((toIsom h ι g hgU)⁻¹ : unitaryIsom3 h) : GL (Fin 3) F) =
        (((toIsom h ι g hgU : unitaryIsom3 h) : GL (Fin 3) F))⁻¹ := rfl
    simp only [Subgroup.coe_mul, Units.val_mul, hinv, coe_toIsom]
    rw [hYm, toMat_smul, toMat_mul, toMat_mul, toMat_gstar h hq ι]
    rfl

theorem apply_mem_center {G : Type*} [Group G] (x : MulAut G) {w : G}
    (hw : w ∈ Subgroup.center G) : x w ∈ Subgroup.center G := by
  have := Subgroup.map_center_eq x
  rw [← this]
  exact Subgroup.mem_map_of_mem _ hw

@[expose] def fixModCenter {G : Type*} [Group G] (e : G) : Subgroup (MulAut G) where
  carrier := {x | ∃ z ∈ Subgroup.center G, x e = e * z}
  one_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
    refine ⟨z * x w, Subgroup.mul_mem _ hz (apply_mem_center x hw), ?_⟩
    rw [MulAut.mul_apply, hy, map_mul, hx, mul_assoc]
  inv_mem' := by
    rintro x ⟨z, hz, hx⟩
    refine ⟨(x⁻¹ z)⁻¹, Subgroup.inv_mem _ (apply_mem_center x⁻¹ hz), ?_⟩
    have h1 : x⁻¹ (x e) = x⁻¹ (e * z) := by rw [hx]
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : x⁻¹ (e * z) = x⁻¹ e * x⁻¹ z := map_mul _ _ _
    rw [h2] at h1
    calc x⁻¹ e = x⁻¹ e * x⁻¹ z * (x⁻¹ z)⁻¹ := by group
      _ = e * (x⁻¹ z)⁻¹ := by rw [← h1]

theorem le_of_inn_le_zpowers {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {A : Subgroup (MulAut (unitarySU 2 3 F 3))} (hA : IsElemAbelian 3 A) (hf : suField h σ ∈ A)
    {a₁ : MulAut (unitarySU 2 3 F 3)} {S : Subgroup (MulAut (unitarySU 2 3 F 3))}
    (hfS : suField h σ ∈ S) (ha₁S : a₁ ∈ S)
    (hcyc : ∀ a₂ ∈ A ⊓ (suConj h).range, a₂ ∈ Subgroup.zpowers a₁) : A ≤ S := by
  intro α hα
  obtain ⟨c, hc, k, rfl⟩ := exists_inn_mul_pow h hσ hA hf hα
  exact S.mul_mem ((Subgroup.zpowers_le.2 ha₁S) (hcyc c hc)) (S.pow_mem hfS k)

end Inn

section Cases

variable (h : UnitaryFieldData 2 3 F)

theorem exists_regular_of_regular_rep {ι : Q8 →+* F}
    {R : M3 Q8} (hR3 : R ∈ (u38Table.take 3).map (·.Y)) (hRu : unitaryOk R = true)
    (G : unitaryIsom3 h) :
    ∃ Y : unitaryIsom3 h, RegularU38 (Y : GL (Fin 3) F) ∧
      suConj h Y = suConj h G * suConj h (toIsom h ι R hRu) * (suConj h G)⁻¹ := by
  have hreg : KSU38R.regFlag R = true := by
    have h4 : KSU38R.regCheck () = true := (u38RCheck_parts).2.2.2.2.1
    unfold KSU38R.regCheck at h4
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hR3
    exact List.all_eq_true.1 h4 y hy
  have hRreg : RegularU38 ((toIsom h ι R hRu : unitaryIsom3 h) : GL (Fin 3) F) :=
    regFlag_sound ι _ (coe_toIsom h ι R hRu) hreg
  refine ⟨G * toIsom h ι R hRu * G⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have := regularU38_conj (G : GL (Fin 3) F) hRreg
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem exists_regular_of_rankTwo {σ : F ≃+* F}
    (hσ : orderOf σ = 3) {A : Subgroup (MulAut (unitarySU 2 3 F 3))} (hA : IsElemAbelian 3 A)
    (hf : suField h σ ∈ A) {ι : Q8 →+* F} (hι : Function.Surjective ι)
    (hωι : IsPrimitiveRoot (ι w0) 3) {R : M3 Q8} (hRd : R ∈ (u38Table.drop 3).map (·.Y))
    (hRu : unitaryOk R = true) (G : unitaryIsom3 h)
    (hγf : suField h σ * suConj h G = suConj h G * suField h σ)
    {a₁ a₂ : MulAut (unitarySU 2 3 F 3)} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A ⊓ (suConj h).range)
    (ha₁eq : a₁ = suConj h G * suConj h (toIsom h ι R hRu) * (suConj h G)⁻¹)
    (hnot : a₂ ∉ Subgroup.zpowers a₁) :
    ∃ Y : unitaryIsom3 h, RegularU38 (Y : GL (Fin 3) F) ∧ suConj h Y ∈ A := by
  obtain ⟨W₂, hW₂⟩ := ha₂.2
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = suConj h G := ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ cR, cR = suConj h (toIsom h ι R hRu) := ⟨_, rfl⟩
  rw [← hγ, ← hcR] at ha₁eq
  rw [← hγ] at hγf
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : MulAut (MulAut (unitarySU 2 3 F 3)), ψ = MulAut.conj γ⁻¹ :=
    ⟨_, rfl⟩
  have hψapp : ∀ x, ψ x = γ⁻¹ * x * γ := by
    intro x
    simp [hψdef, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := ψ.injective
  have hψcR : ψ a₁ = cR := by rw [hψapp, ha₁eq]; group
  have ha₂f : a₂ * suField h σ = suField h σ * a₂ := hA.comm ha₂.1 hf
  have hcomf : Commute (suField h σ) γ := hγf
  have e1 : suConj h (G⁻¹ * W₂ * G) = γ⁻¹ * a₂ * γ := by
    rw [map_mul, map_mul, map_inv, hW₂, hγ]
  have hd'' : suConj h (G⁻¹ * W₂ * G) ∈ Dsub h σ := by
    refine Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [e1]
    exact (((hcomf.symm.inv_left).mul_left (show Commute a₂ (suField h σ) from ha₂f)).mul_left
      hcomf.symm).eq
  obtain ⟨Z, hZu, hZe, hZeq⟩ := exists_toIsom_of_mem_Dsub h hσ hωι hd''
  have ha₂'' : suConj h (toIsom h ι Z hZu) = ψ a₂ := by rw [← hZeq, e1, hψapp]
  have hZ3 : isScalar (Z * Z * Z) = true := by
    have hpow : suConj h (toIsom h ι Z hZu) ^ 3 = 1 := by
      rw [ha₂'', ← map_pow, hA.2 a₂ ha₂.1, map_one]
    have := (suConj_toIsom_pow_eq_one_iff h hι Z hZu 3).1 hpow
    rwa [mpow_three_eq ι] at this
  have hZs : isScalar Z = false := by
    by_contra hs
    have h1 := (suConj_toIsom_eq_one_iff h hι Z hZu).2 (Bool.eq_true_of_not_eq_false hs)
    rw [ha₂'', ← map_one ψ] at h1
    exact hnot (by rw [hψinj h1]; exact Subgroup.one_mem _)
  have hcm : KSU38R.commMod R Z = true := by
    refine (suConj_toIsom_comm_iff h hι R Z hRu hZu).1 ?_
    rw [← hcR, ha₂'', ← hψcR, ← map_mul, ← map_mul, hA.comm ha₁ ha₂.1]
  have hp1 : KSU38R.propto Z R = false := by
    by_contra hcon
    obtain ⟨l, hl⟩ := of_decide_eq_true (Bool.eq_true_of_not_eq_false hcon)
    have h1 : suConj h (toIsom h ι Z hZu) = cR := by
      rw [hcR]
      apply suConj_eq_of_matrix_eq_smul h (c := ι l)
      rw [coe_toIsom, coe_toIsom, hl, toMat_smul]
    rw [ha₂'', ← hψcR] at h1
    exact hnot (by rw [hψinj h1]; exact Subgroup.mem_zpowers a₁)
  have hp2 : KSU38R.propto Z (R * R) = false := by
    by_contra hcon
    obtain ⟨l, hl⟩ := of_decide_eq_true (Bool.eq_true_of_not_eq_false hcon)
    have h1 : suConj h (toIsom h ι Z hZu) = cR * cR := by
      rw [hcR, ← map_mul]
      apply suConj_eq_of_matrix_eq_smul h (c := ι l)
      rw [Subgroup.coe_mul, Units.val_mul, coe_toIsom, coe_toIsom, hl, toMat_smul, toMat_mul]
    rw [ha₂'', ← hψcR, ← map_mul] at h1
    exact hnot (by
      rw [hψinj h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a₁) (Subgroup.mem_zpowers a₁))
  obtain ⟨j, -, Y', hY'reg, hsuY'⟩ :=
    exists_regular_of_commMod h hι hRd hRu hZu hZe hZ3 hZs hcm hp1 hp2
  refine ⟨G * Y' * G⁻¹, ?_, ?_⟩
  · have := regularU38_conj (G : GL (Fin 3) F) hY'reg
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  · have e2 : suConj h (G * Y' * G⁻¹) = γ * suConj h Y' * γ⁻¹ := by
      rw [map_mul, map_mul, map_inv, hγ]
    rw [e2, hsuY', ha₂'', ← hcR, ← hψcR]
    have hφψ : ∀ x, γ * ψ x * γ⁻¹ = x := fun x => by rw [hψapp]; group
    have e3 : γ * (ψ a₁ ^ j * ψ a₂) * γ⁻¹ = a₁ ^ j * a₂ := by
      have h1 := (MulAut.conj γ).map_mul (ψ a₁ ^ j) (ψ a₂)
      have h2 := map_pow (MulAut.conj γ) (ψ a₁) j
      simp only [MulAut.conj_apply] at h1 h2
      rw [h1, h2, hφψ, hφψ]
    rw [e3]
    exact A.mul_mem (A.pow_mem ha₁ j) ha₂.1

theorem exists_fixed_of_cyclic {σ : F ≃+* F}
    (hσ : orderOf σ = 3) {A : Subgroup (MulAut (unitarySU 2 3 F 3))} (hA : IsElemAbelian 3 A)
    (hf : suField h σ ∈ A) {ι : Q8 →+* F} {e : unitarySU 2 3 F 3} (he3 : e ^ 3 = 1)
    (hef : suField h σ e = e) {R : M3 Q8} (hRu : unitaryOk R = true)
    (hW : (∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), suConj h (toIsom h ι R hRu) e = e * z) ∧
        MulAut.conj e ∉ Subgroup.zpowers (suConj h (toIsom h ι R hRu)) ∧
        (R ∈ (u38Table.drop 3).map (·.Y) → suConj h (toIsom h ι R hRu) e = e))
    (G : unitaryIsom3 h) (hγf : suField h σ * suConj h G = suConj h G * suField h σ)
    {a₁ : MulAut (unitarySU 2 3 F 3)} (ha₁ : a₁ ∈ A)
    (ha₁eq : a₁ = suConj h G * suConj h (toIsom h ι R hRu) * (suConj h G)⁻¹)
    (hcyc : ∀ a₂ ∈ A ⊓ (suConj h).range, a₂ ∈ Subgroup.zpowers a₁) :
    ∃ e' : unitarySU 2 3 F 3, e' ^ 3 = 1 ∧
      (∀ α ∈ A, ∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), α e' = e' * z) ∧
      MulAut.conj e' ∉ A ∧ (R ∈ (u38Table.drop 3).map (·.Y) → ∀ α ∈ A, α e' = e') := by
  obtain ⟨⟨z, hz, hcRe⟩, hnotz, hexact⟩ := hW
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = suConj h G := ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ cR, cR = suConj h (toIsom h ι R hRu) := ⟨_, rfl⟩
  rw [← hγ, ← hcR] at ha₁eq
  rw [← hγ] at hγf
  rw [← hcR] at hcRe hnotz hexact
  have hfe' : suField h σ (γ e) = γ e := by
    calc suField h σ (γ e) = (suField h σ * γ) e := rfl
      _ = (γ * suField h σ) e := by rw [hγf]
      _ = γ (suField h σ e) := rfl
      _ = γ e := by rw [hef]
  have hfS : suField h σ ∈ fixModCenter (γ e) :=
    ⟨1, Subgroup.one_mem _, by rw [mul_one]; exact hfe'⟩
  have hcRγ : ∀ x, (γ * cR * γ⁻¹) (γ x) = γ (cR x) := by
    intro x
    simp [MulAut.mul_apply, MulAut.inv_apply]
  have ha₁S : a₁ ∈ fixModCenter (γ e) := by
    refine ⟨γ z, apply_mem_center γ hz, ?_⟩
    rw [ha₁eq, hcRγ, hcRe, map_mul]
  have hAS : A ≤ fixModCenter (γ e) := le_of_inn_le_zpowers h hσ hA hf hfS ha₁S hcyc
  refine ⟨γ e, by rw [← map_pow, he3, map_one], fun α hα => hAS hα, ?_, ?_⟩
  · intro hmem
    have hinn : MulAut.conj (γ e) ∈ A ⊓ (suConj h).range :=
      ⟨hmem, by
        rw [CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.conj_eq_suConj (h := h)]
        exact ⟨_, rfl⟩⟩
    have hz' := hcyc _ hinn
    rw [conj_apply_aut] at hz'
    apply hnotz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz'
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    have h1 : a₁ ^ m = γ * cR ^ m * γ⁻¹ := by
      have := map_zpow (MulAut.conj γ) cR m
      simp only [MulAut.conj_apply] at this
      rw [ha₁eq, ← this]
    rw [h1] at hm
    exact mul_right_cancel (mul_left_cancel hm)
  · intro hRd
    have hfS' : suField h σ ∈ MulAction.stabilizer (MulAut (unitarySU 2 3 F 3)) (γ e) :=
      MulAction.mem_stabilizer_iff.2 hfe'
    have ha₁S' : a₁ ∈ MulAction.stabilizer (MulAut (unitarySU 2 3 F 3)) (γ e) := by
      refine MulAction.mem_stabilizer_iff.2 ?_
      change a₁ (γ e) = γ e
      rw [ha₁eq, hcRγ, hexact hRd]
    exact fun α hα =>
      MulAction.mem_stabilizer_iff.1 ((le_of_inn_le_zpowers h hσ hA hf hfS' ha₁S' hcyc) hα)

theorem inn_dichotomy
    {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (A : Subgroup (MulAut (unitarySU 2 3 F 3))) (hA : IsElemAbelian 3 A)
    (hf : suField h σ ∈ A) :
    ((∃ a₁ ∈ A ⊓ (suConj h).range, a₁ ≠ 1 ∧
        ∃ a₂ ∈ A ⊓ (suConj h).range, a₂ ∉ Subgroup.zpowers a₁) ∧
      ∃ Y : unitaryIsom3 h, RegularU38 (Y : GL (Fin 3) F) ∧ suConj h Y ∈ A) ∨
    (∃ e : unitarySU 2 3 F 3, e ^ 3 = 1 ∧
      (∀ α ∈ A, ∃ z ∈ Subgroup.center (unitarySU 2 3 F 3), α e = e * z) ∧
      MulAut.conj e ∉ A ∧
      ((∃ Y : unitaryIsom3 h, RegularU38 (Y : GL (Fin 3) F) ∧ suConj h Y ∈ A) ∨
        ∀ α ∈ A, α e = e)) := by
  classical
  have := h.finite
  obtain ⟨ι, hι, hωι, hσω⟩ := exists_model38 h hσ
  obtain ⟨e, he3, hef, hconj1, hW⟩ := exists_witness h hσ hι hωι hσω
  by_cases hnt : ∃ a₁ ∈ A ⊓ (suConj h).range, a₁ ≠ 1
  swap
  ·
    push Not at hnt
    right
    have hcyc : ∀ a₂ ∈ A ⊓ (suConj h).range,
        a₂ ∈ Subgroup.zpowers (1 : MulAut (unitarySU 2 3 F 3)) := by
      intro a₂ ha₂
      rw [hnt a₂ ha₂]
      exact Subgroup.one_mem _
    have hAstab : A ≤ MulAction.stabilizer (MulAut (unitarySU 2 3 F 3)) e :=
      le_of_inn_le_zpowers h hσ hA hf (MulAction.mem_stabilizer_iff.2 hef) (Subgroup.one_mem _)
        hcyc
    have hfix : ∀ α ∈ A, α e = e := fun α hα => MulAction.mem_stabilizer_iff.1 (hAstab hα)
    refine ⟨e, he3, fun α hα => ⟨1, Subgroup.one_mem _, by rw [mul_one]; exact hfix α hα⟩, ?_,
      Or.inr hfix⟩
    intro hmem
    have : MulAut.conj e ∈ A ⊓ (suConj h).range :=
      ⟨hmem, by
        rw [CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.conj_eq_suConj (h := h)]
        exact ⟨_, rfl⟩⟩
    exact hconj1 (hnt _ this)
  obtain ⟨a₁, ha₁, hne⟩ := hnt
  obtain ⟨Ym₁, hu₁, he₁, hY₁⟩ := exists_toIsom_of_mem_inn h hσ hωι hA hf ha₁
  have hns₁ : isScalar Ym₁ = false := by
    by_contra hs
    exact hne (by
      rw [hY₁]
      exact (suConj_toIsom_eq_one_iff h hι Ym₁ hu₁).2 (Bool.eq_true_of_not_eq_false hs))
  have h3₁ : isScalar (Ym₁ * Ym₁ * Ym₁) = true := by
    have := (suConj_toIsom_pow_eq_one_iff h hι Ym₁ hu₁ 3).1 (by rw [← hY₁]; exact hA.2 a₁ ha₁.1)
    rwa [mpow_three_eq ι] at this
  obtain ⟨R, hR, hRu, G, hGfix, hnorm⟩ := exists_normalization h hσω hu₁ he₁ hns₁ h3₁
  have hγf : suField h σ * suConj h G = suConj h G * suField h σ := by
    have h1 := suField_mul_suConj_mul_inv h σ G
    have h2 : (⟨glAut σ (G : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ G.2⟩ : unitaryIsom3 h) = G :=
      Subtype.ext hGfix
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have ha₁eq : a₁ = suConj h G * suConj h (toIsom h ι R hRu) * (suConj h G)⁻¹ :=
    hY₁.trans hnorm
  have hRsplit : R ∈ (u38Table.take 3).map (·.Y) ∨ R ∈ (u38Table.drop 3).map (·.Y) := by
    have hR' : R ∈ (u38Table.take 3 ++ u38Table.drop 3).map (·.Y) := by
      rw [List.take_append_drop]; exact hR
    rw [List.map_append, List.mem_append] at hR'
    exact hR'
  by_cases hcyc : ∀ a₂ ∈ A ⊓ (suConj h).range, a₂ ∈ Subgroup.zpowers a₁
  swap
  ·
    left
    push Not at hcyc
    obtain ⟨a₂, ha₂, hnot⟩ := hcyc
    refine ⟨⟨a₁, ha₁, hne, a₂, ha₂, hnot⟩, ?_⟩
    rcases hRsplit with hR3 | hRd
    · obtain ⟨Y, hY, hYa⟩ := exists_regular_of_regular_rep h (ι := ι) hR3 hRu G
      exact ⟨Y, hY, by rw [hYa, ← ha₁eq]; exact ha₁.1⟩
    · exact exists_regular_of_rankTwo h hσ hA hf hι hωι hRd hRu G hγf ha₁.1 ha₂ ha₁eq hnot
  ·
    right
    obtain ⟨e', he'3, hfix, hconj, hexact⟩ :=
      exists_fixed_of_cyclic h hσ hA hf he3 hef hRu (hW R hRu hR) G hγf ha₁.1 ha₁eq hcyc
    refine ⟨e', he'3, hfix, hconj, ?_⟩
    rcases hRsplit with hR3 | hRd
    · obtain ⟨Y, hY, hYa⟩ := exists_regular_of_regular_rep h (ι := ι) hR3 hRu G
      exact Or.inl ⟨Y, hY, by rw [hYa, ← ha₁eq]; exact ha₁.1⟩
    · exact Or.inr (hexact hRd)

end Cases

end Dichotomy

section MaxStrict

variable {F : Type} [Field F]

theorem mem_map_conj_inv_of_eq_mul_inv {G : Type*} [Group G] {E : Subgroup G} {φ g : G} (ψ : G)
    (hφ : φ ∈ E) (hφg : φ = ψ * g * ψ⁻¹) : g ∈ E.map (MulAut.conj ψ⁻¹).toMonoidHom := by
  refine ⟨φ, hφ, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφg]
  group

theorem maxStrict_map_conj {G : Type*} [Group G] (c : MulAut G) (A : Subgroup (MulAut G))
    (hMax : ∀ e : G, e ^ 3 = 1 → (∀ α ∈ A, α e = e) → MulAut.conj e ∈ A) :
    ∀ e : G, e ^ 3 = 1 → (∀ α ∈ A.map (MulAut.conj c).toMonoidHom, α e = e) →
      MulAut.conj e ∈ A.map (MulAut.conj c).toMonoidHom := by
  intro e he3 hfix
  have he' : (c⁻¹ e) ^ 3 = 1 := by rw [← map_pow, he3, map_one]
  have hfix' : ∀ α ∈ A, α (c⁻¹ e) = c⁻¹ e := by
    intro α hα
    have h1 : c (α (c⁻¹ e)) = e :=
      hfix (c * α * c⁻¹) ⟨α, hα, by simp [MulAut.conj_apply]⟩
    calc α (c⁻¹ e) = c⁻¹ (c (α (c⁻¹ e))) := by simp
      _ = c⁻¹ e := by rw [h1]
  refine ⟨MulAut.conj (c⁻¹ e), hMax _ he' hfix', ?_⟩
  have h4 := conj_apply_aut c (c⁻¹ e)
  rw [MulAut.apply_inv_self] at h4
  rw [h4]
  simp [MulAut.conj_apply]

theorem exists_regular_inner_of_maxStrict
    {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (A : Subgroup (MulAut (unitarySU 2 3 F 3))) (hA : IsElemAbelian 3 A)
    (hφ : ∃ φ ∈ A, φ ∉ (suConj h).range)
    (hMax : ∀ e : unitarySU 2 3 F 3, e ^ 3 = 1 → (∀ α ∈ A, α e = e) → MulAut.conj e ∈ A) :
    ∃ (c : MulAut (unitarySU 2 3 F 3)) (σ : F ≃+* F) (Y : unitaryIsom3 h), orderOf σ = 3 ∧
      suField h σ ∈ A.map (MulAut.conj c).toMonoidHom ∧
      suConj h Y ∈ A.map (MulAut.conj c).toMonoidHom ∧ RegularU38 (Y : GL (Fin 3) F) := by
  obtain ⟨φ, hφA, hφN⟩ := hφ
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨σ, hσ, H, hH⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.eq_conj_suField_of_not_mem (h := h) hq
      (hA.2 φ hφA) hφN
  have hf₁ := mem_map_conj_inv_of_eq_mul_inv (suConj h H) hφA hH
  have hA₁ := hA.map (MulAut.conj (suConj h H)⁻¹).toMonoidHom
  have hMax₁ := maxStrict_map_conj (suConj h H)⁻¹ A hMax
  rcases inn_dichotomy h hσ _ hA₁ hf₁ with ⟨-, Y, hY, hYA⟩ | ⟨e, he3, -, hconj, hcase⟩
  · exact ⟨(suConj h H)⁻¹, σ, Y, hσ, hf₁, hYA, hY⟩
  · rcases hcase with ⟨Y, hY, hYA⟩ | hfix
    · exact ⟨(suConj h H)⁻¹, σ, Y, hσ, hf₁, hYA, hY⟩
    · exact absurd (hMax₁ e he3 hfix) hconj

theorem eq_bot_of_maxStrict
    (h : UnitaryFieldData 2 3 F)
    (A : Subgroup (MulAut (unitarySU 2 3 F 3))) (hA : IsElemAbelian 3 A)
    (hφ : ∃ φ ∈ A, φ ∉ (suConj h).range)
    (hMax : ∀ e : unitarySU 2 3 F 3, e ^ 3 = 1 → (∀ α ∈ A, α e = e) → MulAut.conj e ∈ A)
    (T : Subgroup (MulAut (unitarySU 2 3 F 3))) (hT : ¬ 3 ∣ Nat.card T)
    (hAT : A ≤ Subgroup.normalizer (T : Set (MulAut (unitarySU 2 3 F 3))))
    (hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z) : T = ⊥ := by
  obtain ⟨c, σ, Y, hσ, hf, hY, hreg⟩ := exists_regular_inner_of_maxStrict h A hA hφ hMax
  set A' : Subgroup (MulAut (unitarySU 2 3 F 3)) := A.map (MulAut.conj c).toMonoidHom with hA'
  set T' : Subgroup (MulAut (unitarySU 2 3 F 3)) := T.map (MulAut.conj c).toMonoidHom with hT'
  have hA'el : IsElemAbelian 3 A' := IsElemAbelian.map hA _
  have hcomm : suConj h Y * suField h σ = suField h σ * suConj h Y := hA'el.comm hY hf
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hT
  have hstable : ∀ a ∈ A', ∀ t ∈ T', a * t * a⁻¹ ∈ T' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨a * t * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAT ha) t).1 ht, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hAT' : A' ≤ Subgroup.normalizer (T' : Set (MulAut (unitarySU 2 3 F 3))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hstable a ha t ht, fun ht => ?_⟩
    have := hstable a⁻¹ (A'.inv_mem ha) _ ht
    simpa [mul_assoc] using this
  have hcen : ∀ (e : MulAut (unitarySU 2 3 F 3)) (z : unitarySU 2 3 F 3),
      z ∈ Subgroup.center (unitarySU 2 3 F 3) → e z ∈ Subgroup.center (unitarySU 2 3 F 3) := by
    intro e z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨u, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz u]
  have hT'Z : ∀ t ∈ T', ∀ z ∈ Subgroup.center (unitarySU 2 3 F 3), t z = z := by
    rintro _ ⟨t, ht, rfl⟩ z hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    have h2 : t (c.symm z) = c.symm z := hTZ t ht (c.symm z) (hcen c⁻¹ z hz)
    rw [h2]
    exact c.apply_symm_apply z
  have hbot := eq_bot_of_regular_field h hσ hreg hcomm T' hT'3 (hAT' hf) (hAT' hY) hT'Z
  rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
  intro t ht
  have := hbot _ ⟨t, ht, rfl⟩
  simpa [MulAut.conj_apply] using this

end MaxStrict

end KSU3Core

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
