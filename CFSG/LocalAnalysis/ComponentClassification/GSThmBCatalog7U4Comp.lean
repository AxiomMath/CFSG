module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Gen
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal val_of_mem_scal
  mem_center_of_mem_scal)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uStar_bd (a b : Matrix (Fin 2) (Fin 2) K) :
    uStar h (bd a b) = bd (uStar h a) (uStar h b) := by
  rw [uStar, uStar, uStar, map_bd, transpose_bd]

theorem unitary_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : uStar h A * A = 1)
    (hB : uStar h B * B = 1) : uStar h (A * B) * (A * B) = 1 := by
  rw [uStar_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uStar h A), hA, Matrix.one_mul, hB]

@[expose] def toSU {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hd : M.det = 1)
    (hu : uStar h M * M = 1) : unitarySU p f K n :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hd]; exact one_ne_zero),
    (mem_unitarySU_iff h).2 ⟨hd, hu⟩⟩

theorem coe_toSU {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hd : M.det = 1)
    (hu : uStar h M * M = 1) :
    (((toSU h M hd hu : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M :=
  rfl

include h in
theorem det_SU {n : ℕ} (g : unitarySU p f K n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  ((mem_unitarySU_iff h).1 g.2).1

theorem unitary_SU {n : ℕ} (g : unitarySU p f K n) :
    uStar h ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  ((mem_unitarySU_iff h).1 g.2).2

omit h in
theorem SU_ext {n : ℕ} {g g' : unitarySU p f K n}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : g = g' :=
  Subtype.ext (Units.ext hg)

@[expose] def bdUL : unitarySU p f K 2 →* unitarySU p f K 4 where
  toFun U := toSU h (bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1)
    (by rw [det_bd, det_SU h U, det_one, one_mul])
    (by rw [uStar_bd, bd_mul, unitary_SU h U, uStar_one, one_mul, bd_one])
  map_one' := SU_ext (by
    show bd (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1
    exact bd_one)
  map_mul' U V := SU_ext (by
    show bd (((U * V : unitarySU p f K 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 =
      bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 *
        bd ((V : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1
    rw [bd_mul, mul_one]
    rfl)

@[expose] def bdUR : unitarySU p f K 2 →* unitarySU p f K 4 where
  toFun W := toSU h (bd 1 ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by rw [det_bd, det_SU h W, det_one, one_mul])
    (by rw [uStar_bd, bd_mul, unitary_SU h W, uStar_one, one_mul, bd_one])
  map_one' := SU_ext (by
    show bd 1 (1 : Matrix (Fin 2) (Fin 2) K) = 1
    exact bd_one)
  map_mul' U V := SU_ext (by
    show bd 1 (((U * V : unitarySU p f K 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      bd 1 ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        bd 1 ((V : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [bd_mul, mul_one]
    rfl)

theorem coe_bdUL (U : unitarySU p f K 2) :
    (((bdUL h U : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem coe_bdUR (W : unitarySU p f K 2) :
    (((bdUR h W : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd 1 ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def factorUL : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
  ((QuotientGroup.mk' (scal p f K)).comp (bdUL h)).range

@[expose] def factorUR : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
  ((QuotientGroup.mk' (scal p f K)).comp (bdUR h)).range

theorem bdUL_mul_bdUR (U W : unitarySU p f K 2) :
    bdUL h U * bdUR h W = bdUR h W * bdUL h U := by
  apply SU_ext
  show bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 *
      bd 1 ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    bd 1 ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1
  rw [bd_mul, bd_mul, mul_one, one_mul, mul_one, one_mul]

theorem ul_smul_one (c : K) : ul (c • (1 : Matrix (Fin 4) (Fin 4) K)) = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul]

theorem lr_smul_one (c : K) : lr (c • (1 : Matrix (Fin 4) (Fin 4) K)) = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr]

theorem mk_bdUL_injective :
    Function.Injective ((QuotientGroup.mk' (scal p f K)).comp (bdUL h)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hU
  obtain ⟨c, hc⟩ := val_of_mem_scal hU
  rw [coe_bdUL] at hc
  have hlr := congrArg lr hc
  have hul := congrArg ul hc
  rw [lr_bd, lr_smul_one] at hlr
  rw [ul_bd, ul_smul_one] at hul
  have h1 : (c : K) = 1 := by
    have := congrFun (congrFun hlr 0) 0
    simpa using this.symm
  apply SU_ext
  rw [hul, h1, one_smul]
  rfl

theorem mk_bdUR_injective :
    Function.Injective ((QuotientGroup.mk' (scal p f K)).comp (bdUR h)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hU
  obtain ⟨c, hc⟩ := val_of_mem_scal hU
  rw [coe_bdUR] at hc
  have hlr := congrArg lr hc
  have hul := congrArg ul hc
  rw [lr_bd, lr_smul_one] at hlr
  rw [ul_bd, ul_smul_one] at hul
  have h1 : (c : K) = 1 := by
    have := congrFun (congrFun hul 0) 0
    simpa using this.symm
  apply SU_ext
  rw [hlr, h1, one_smul]
  rfl

omit h in
theorem mat_comm {g z : unitarySU p f K 4} {l : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) (hz : z * g = g * z) :
    ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * X1 l =
      X1 l * ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have := congrArg (fun y : unitarySU p f K 4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    hz
  simpa only [Subgroup.coe_mul, Units.val_mul, hg] using this

theorem lr_one' : lr (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr]

theorem blocks_of_comm (h2 : (2 : K) ≠ 0) {g z : unitarySU p f K 4} {l : K} (hl : l ≠ 0)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) (hz : z * g = g * z) :
    ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        bd (ul ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
          (lr ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ∧
      uStar h (ul ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
        ul ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      uStar h (lr ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
        lr ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hbd := eq_bd (isBD_of_comm_X1 h2 hl (mat_comm hg hz))
  have hu := unitary_SU h z
  rw [hbd, uStar_bd, bd_mul] at hu
  have hu1 := congrArg ul hu
  have hu2 := congrArg lr hu
  rw [ul_bd, ul_one] at hu1
  rw [lr_bd, lr_one'] at hu2
  exact ⟨hbd, hu1, hu2⟩

include h in
theorem ul_lr_mul_inv (h2 : (2 : K) ≠ 0) {g z : unitarySU p f K 4} {l : K} (hl : l ≠ 0)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) (hz : z * g = g * z) :
    ul ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ul (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      lr ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        lr (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hzi : z⁻¹ * g = g * z⁻¹ := (Commute.inv_left (show Commute z g from hz)).eq
  obtain ⟨b1, -, -⟩ := blocks_of_comm h h2 hl hg hz
  obtain ⟨b3, -, -⟩ := blocks_of_comm h h2 hl hg hzi
  have hm : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  rw [b1, b3, bd_mul] at hm
  have hu := congrArg ul hm
  have hl' := congrArg lr hm
  rw [ul_bd, ul_one] at hu
  rw [lr_bd, lr_one'] at hl'
  exact ⟨hu, hl'⟩

theorem comm_mem_sup (h2 : (2 : K) ≠ 0) {g : unitarySU p f K 4} {l : K} (hl : l ≠ 0)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) {z z' : unitarySU p f K 4}
    (hz : z * g = g * z) (hz' : z' * g = g * z') :
    ⁅z, z'⁆ ∈ (bdUL h).range ⊔ (bdUR h).range := by
  have hzi : z⁻¹ * g = g * z⁻¹ := (Commute.inv_left (show Commute z g from hz)).eq
  have hzi' : z'⁻¹ * g = g * z'⁻¹ := (Commute.inv_left (show Commute z' g from hz')).eq
  obtain ⟨b1, v1, w1⟩ := blocks_of_comm h h2 hl hg hz
  obtain ⟨b2, v2, w2⟩ := blocks_of_comm h h2 hl hg hz'
  obtain ⟨b3, v3, w3⟩ := blocks_of_comm h h2 hl hg hzi
  obtain ⟨b4, v4, w4⟩ := blocks_of_comm h h2 hl hg hzi'
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv h h2 hl hg hz
  obtain ⟨u2, l2⟩ := ul_lr_mul_inv h h2 hl hg hz'
  set M1 := ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set M2 := ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set M3 := (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set M4 := (((z'⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set u := ul M1 * ul M2 * ul M3 * ul M4 with hu
  set w := lr M1 * lr M2 * lr M3 * lr M4 with hw
  have hdu : u.det = 1 := by
    have e1 := congrArg Matrix.det u1
    have e2 := congrArg Matrix.det u2
    rw [det_mul, det_one] at e1 e2
    rw [hu, det_mul, det_mul, det_mul]
    linear_combination (ul M2).det * (ul M4).det * e1 + e2
  have hdw : w.det = 1 := by
    have e1 := congrArg Matrix.det l1
    have e2 := congrArg Matrix.det l2
    rw [det_mul, det_one] at e1 e2
    rw [hw, det_mul, det_mul, det_mul]
    linear_combination (lr M2).det * (lr M4).det * e1 + e2
  have huu : uStar h u * u = 1 :=
    unitary_mul h (unitary_mul h (unitary_mul h v1 v2) v3) v4
  have hww : uStar h w * w = 1 :=
    unitary_mul h (unitary_mul h (unitary_mul h w1 w2) w3) w4
  have hcomm : ⁅z, z'⁆ = bdUL h (toSU h u hdu huu) * bdUR h (toSU h w hdw hww) := by
    apply SU_ext
    rw [commutatorElement_def]
    show M1 * M2 * M3 * M4 = bd u 1 * bd 1 w
    rw [bd_mul, mul_one, one_mul, b1, b2, b3, b4, bd_mul, bd_mul, bd_mul]
  rw [hcomm]
  exact mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem conj_bdUL_mem (h2 : (2 : K) ≠ 0) {g : unitarySU p f K 4} {l : K} (hl : l ≠ 0)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) {z : unitarySU p f K 4}
    (hz : z * g = g * z) (U : unitarySU p f K 2) :
    z * bdUL h U * z⁻¹ ∈ (bdUL h).range := by
  have hzi : z⁻¹ * g = g * z⁻¹ := (Commute.inv_left (show Commute z g from hz)).eq
  obtain ⟨b1, v1, -⟩ := blocks_of_comm h h2 hl hg hz
  obtain ⟨b3, v3, -⟩ := blocks_of_comm h h2 hl hg hzi
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv h h2 hl hg hz
  set M1 := ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set M3 := (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set u := ul M1 * ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ul M3 with hu
  have hdu : u.det = 1 := by
    have e1 := congrArg Matrix.det u1
    rw [det_mul, det_one] at e1
    rw [hu, det_mul, det_mul, det_SU h U, mul_one, e1]
  have huu : uStar h u * u = 1 := unitary_mul h (unitary_mul h v1 (unitary_SU h U)) v3
  refine ⟨toSU h u hdu huu, ?_⟩
  apply SU_ext
  show bd u 1 = M1 * bd ((U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 * M3
  rw [b1, b3, bd_mul, bd_mul, mul_one, l1]

theorem conj_bdUR_mem (h2 : (2 : K) ≠ 0) {g : unitarySU p f K 4} {l : K} (hl : l ≠ 0)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) {z : unitarySU p f K 4}
    (hz : z * g = g * z) (W : unitarySU p f K 2) :
    z * bdUR h W * z⁻¹ ∈ (bdUR h).range := by
  have hzi : z⁻¹ * g = g * z⁻¹ := (Commute.inv_left (show Commute z g from hz)).eq
  obtain ⟨b1, -, w1⟩ := blocks_of_comm h h2 hl hg hz
  obtain ⟨b3, -, w3⟩ := blocks_of_comm h h2 hl hg hzi
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv h h2 hl hg hz
  set M1 := ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set M3 := (((z⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set w := lr M1 * ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * lr M3 with hw
  have hdw : w.det = 1 := by
    have e1 := congrArg Matrix.det l1
    rw [det_mul, det_one] at e1
    rw [hw, det_mul, det_mul, det_SU h W, mul_one, e1]
  have hww : uStar h w * w = 1 := unitary_mul h (unitary_mul h w1 (unitary_SU h W)) w3
  refine ⟨toSU h w hdw hww, ?_⟩
  apply SU_ext
  show bd 1 w = M1 * bd 1 ((W : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M3
  rw [b1, b3, bd_mul, bd_mul, mul_one, u1]

theorem bdUL_comm {g : unitarySU p f K 4} {l : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) (U : unitarySU p f K 2) :
    bdUL h U * g = g * bdUL h U := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_bdUL, hg]
  exact bd_comm_X1 _ _ l

theorem bdUR_comm {g : unitarySU p f K 4} {l : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l) (W : unitarySU p f K 2) :
    bdUR h W * g = g * bdUR h W := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_bdUR, hg]
  exact bd_comm_X1 _ _ l

@[expose] def negSU : unitarySU p f K 2 :=
  toSU h (-1) (by rw [det_neg, det_one, Fintype.card_fin]; norm_num)
    (by
      rw [uStar]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

theorem orderOf_negSU (h2 : (2 : K) ≠ 0) : orderOf (negSU h) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    apply SU_ext
    show (-1 : Matrix (Fin 2) (Fin 2) K) * (-1) = (1 : Matrix (Fin 2) (Fin 2) K)
    simp
  · intro h1
    have := congrArg (fun M : unitarySU p f K 2 => ((M : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0) h1
    change (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 = (1 : Matrix (Fin 2) (Fin 2) K) 0 0 at this
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2
    linear_combination -this

include h in
theorem exists_sl2_equiv [Finite K] :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (SpecialLinearGroup (Fin 2) F ≃* unitarySU p f K 2) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  exact ⟨_, inferInstance, inferInstance, LieType.Steinberg.card_fixedSubfield hK,
    RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two hK⟩

include h in
theorem card_SU2 [Finite K] : Nat.card (unitarySU p f K 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  exact RankThree.SubgroupLists.card_statedSU_two (by rw [h.card, ← pow_mul, mul_comm])

include h in
theorem isQuasisimple_SU2 [Finite K] (hp2 : p ≠ 2) (hq3 : p ^ f ≠ 3) :
    IsQuasisimple (unitarySU p f K 2) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_sl2_equiv h
  have hF2 : Nat.card F ≠ 2 := by
    rw [hF]
    intro h2
    apply hp2
    have : p ∣ 2 := h2 ▸ dvd_pow_self p (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hns : ¬ (2 = 1 ∨ 2 = 2 ∧ (Nat.card F = 2 ∨ Nat.card F = 3)) := by
    rw [hF] at hF2 ⊢
    omega
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1
    ((CatalogueBGeneralLinear.generalLinear_p_components 2 F (by norm_num)).2.2 hns).1

include h in
theorem isSolvable_SU2 [Finite K] (hq3 : p ^ f = 3) : Group.IsSolvable (unitarySU p f K 2) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_sl2_equiv h
  have := CatalogueBGeneralLinear.generalLinear_small_solvable 2 F
    (Or.inr ⟨rfl, Or.inr (hF.trans hq3)⟩)
  have : Group.IsSolvable (SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective (f := SpecialLinearGroup.toGL)
      SpecialLinearGroup.toGL_injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem eq_factorU_of_pComponent [Finite K] (hp2 : p ≠ 2) {g : unitarySU p f K 4} {l : K}
    (hl : l ≠ 0) (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l)
    {L : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hLle : L ≤ centralizer ({QuotientGroup.mk g} : Set (StatedProj (StatedSU 4 (p ^ f) K))))
    (hL : IsPComponent 2 (L.subgroupOf
      (centralizer ({QuotientGroup.mk g} : Set (StatedProj (StatedSU 4 (p ^ f) K)))))) :
    L = factorUL h ∨ L = factorUR h := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hZ : scal p f K ≤ center (unitarySU p f K 4) := fun z hz => mem_center_of_mem_scal hz
  have hcomm := fun z z' (hz : z * g = g * z) (hz' : z' * g = g * z') =>
    comm_mem_sup h h2 hl hg hz hz'
  by_cases hq3 : p ^ f = 3
  · have := isSolvable_SU2 h hq3
    exact (false_of_solvable hZ (bdUL h) (bdUR h) (bdUL_mul_bdUR h) hcomm hLle hL).elim
  · exact eq_factor_of_pComponent hZ (bdUL h) (bdUR h) hcomm (isQuasisimple_SU2 h hp2 hq3)
      (orderOf_negSU h h2) (mk_bdUL_injective h) (mk_bdUR_injective h) (bdUL_comm h hg)
      (bdUR_comm h hg) (fun _ hz U => conj_bdUL_mem h h2 hl hg hz U)
      (fun _ hz W => conj_bdUR_mem h h2 hl hg hz W) hLle hL

theorem pairConfig_factorsU [Finite K] (hp2 : p ≠ 2) {g : unitarySU p f K 4} {l : K}
    (hl : l ≠ 0) (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l)
    {K₁ K₂ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hc : Sp4Rec.PairConfig (StatedProj (StatedSU 4 (p ^ f) K)) (QuotientGroup.mk g) K₁ K₂) :
    (K₁ = factorUL h ∧ K₂ = factorUR h) ∨ (K₁ = factorUR h ∧ K₂ = factorUL h) := by
  rcases eq_factorU_of_pComponent h hp2 hl hg hc.K_le hc.isPComponent_K with h1 | h1 <;>
  rcases eq_factorU_of_pComponent h hp2 hl hg hc.K'_le hc.isPComponent_K' with h2 | h2
  · exact absurd (h1.trans h2.symm) hc.ne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hc.ne

theorem card_factorU_le [Finite K] {A : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hA : A = factorUL h ∨ A = factorUR h) :
    Nat.card A ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by
  rw [← card_SU2 h]
  rcases hA with rfl | rfl
  · exact (Nat.card_congr (MonoidHom.ofInjective (mk_bdUL_injective h)).toEquiv).symm.le
  · exact (Nat.card_congr (MonoidHom.ofInjective (mk_bdUR_injective h)).toEquiv).symm.le

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
