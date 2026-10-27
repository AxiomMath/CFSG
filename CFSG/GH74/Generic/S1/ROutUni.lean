module

public import CFSG.GH74.Generic.S1.RUniDet
public import CFSG.GH74.Generic.S1.ROutAbs
public import CFSG.GH74.Generic.S1.RSP
public import CFSG.GH74.Generic.S1.RAutLin
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def barE (h : UnitaryFieldData p f F) : F ≃+* F :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barE_sq (h : UnitaryFieldData p f F) : barE h * barE h = 1 := by
  ext c
  exact h.bar_bar c

theorem isUnit_eq_one_or_neg (ε : F) (h : ε * ε = 1) : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.1 h

abbrev UniY (F : Type) [Field F] : Type := (F ≃+* F) × ↥(rootsOfUnity 2 F)

theorem uniY_comm (h : UnitaryFieldData p f F) (y y' : UniY F) : y * y' = y' * y := by
  have : Finite F := h.finite
  have hcyc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic h.prime F h.card).2
  have h1 : IsCyclic (F ≃+* F) := hcyc
  refine Prod.ext ?_ (mul_comm _ _)
  exact (IsCyclic.commGroup (α := F ≃+* F)).mul_comm y.1 y'.1

@[expose] noncomputable def rdU (p f : ℕ) (N : GL (Fin 4) F) : Fˣ :=
  (Matrix.GeneralLinearGroup.det N) ^ ((p ^ f + 1) / 2)

theorem rdU_mul (p f : ℕ) (N N' : GL (Fin 4) F) : rdU p f (N * N') = rdU p f N * rdU p f N' := by
  unfold rdU
  rw [map_mul, mul_pow]

theorem rdU_one (p f : ℕ) : rdU p f (1 : GL (Fin 4) F) = 1 := by
  unfold rdU
  rw [map_one, one_pow]

theorem rdet_pow_succ (h : UnitaryFieldData p f F) {N : GL (Fin 4) F}
    (hN : RIsom h (N : Matrix (Fin 4) (Fin 4) F)) : (N : Matrix (Fin 4) (Fin 4) F).det ^ (p ^ f + 1) = 1 := by
  have h1 := congrArg Matrix.det hN
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((N : Matrix (Fin 4) (Fin 4) F).map h.bar).det = h.bar (N : Matrix (Fin 4) (Fin 4) F).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h2] at h1
  rw [pow_succ, ← UnitaryFieldData.bar_apply]
  exact h1

theorem rdU_sq (h : UnitaryFieldData p f F) (hq : p ^ f % 2 = 1) {N : GL (Fin 4) F}
    (hN : RIsom h (N : Matrix (Fin 4) (Fin 4) F)) : rdU p f N ^ 2 = 1 := by
  have h1 := rdet_pow_succ h hN
  apply Units.ext
  unfold rdU
  rw [← pow_mul, show (p ^ f + 1) / 2 * 2 = p ^ f + 1 by omega, Units.val_pow_eq_pow_val,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact h1

theorem rdU_glAut (h : UnitaryFieldData p f F) (hq : p ^ f % 2 = 1) {N : GL (Fin 4) F}
    (hN : RIsom h (N : Matrix (Fin 4) (Fin 4) F)) (σ : F ≃+* F) :
    rdU p f (glAut σ N) = rdU p f N := by
  have hsq := rdU_sq h hq hN
  have h1 : ((rdU p f N : Fˣ) : F) * ((rdU p f N : Fˣ) : F) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hsq
    simpa [sq] using this
  have h2 : ((rdU p f (glAut σ N) : Fˣ) : F) = σ ((rdU p f N : Fˣ) : F) := by
    unfold rdU
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_glAut]
    congr 1
    exact (RingHom.map_det (σ : F →+* F) (N : Matrix (Fin 4) (Fin 4) F)).symm ▸ rfl
  apply Units.ext
  rw [h2]
  rcases isUnit_eq_one_or_neg _ h1 with h3 | h3
  · rw [h3, map_one]
  · rw [h3, map_neg, map_one]

@[expose] noncomputable def uniChi (h : UnitaryFieldData p f F) (hq : p ^ f % 2 = 1) :
    UniPair h →* UniY F where
  toFun x := (x.1.right, ⟨rdU p f x.1.left, by
    rw [mem_rootsOfUnity]; exact rdU_sq h hq x.2⟩)
  map_one' := by
    refine Prod.ext rfl (Subtype.ext ?_)
    show rdU p f (1 : GL (Fin 4) F ⋊[glAut] (F ≃+* F)).left = 1
    rw [SemidirectProduct.one_left, rdU_one]
  map_mul' x y := by
    refine Prod.ext rfl (Subtype.ext ?_)
    show rdU p f ((x.1 * y.1).left) = rdU p f x.1.left * rdU p f y.1.left
    rw [SemidirectProduct.mul_left, rdU_mul, rdU_glAut h hq y.2 x.1.right]

@[expose] def rm1 (F : Type) [Field F] : ↥(rootsOfUnity 2 F) := ⟨-1, by rw [mem_rootsOfUnity]; simp⟩

theorem rootsOfUnity_two_eq (ε : ↥(rootsOfUnity 2 F)) : ε = 1 ∨ ε = rm1 F := by
  have h1 : ((ε : Fˣ) : F) * ((ε : Fˣ) : F) = 1 := by
    have h2 : (ε : Fˣ) ^ 2 = 1 := (mem_rootsOfUnity ..).1 ε.2
    have := congrArg (fun u : Fˣ => (u : F)) h2
    simpa [sq] using this
  rcases isUnit_eq_one_or_neg _ h1 with h3 | h3
  · left
    apply Subtype.ext
    apply Units.ext
    exact h3
  · right
    apply Subtype.ext
    apply Units.ext
    exact h3

theorem uniY_card_le_two (h : UnitaryFieldData p f F) (I : Subgroup (UniY F))
    (hI : ∀ y ∈ I, ∃ n : ℕ, y ^ (2 ^ n) = 1) (hy : ((barE h, 1) : UniY F) ∉ I) :
    Nat.card I ≤ 2 := by
  have : Finite F := h.finite
  have hL : ∀ y ∈ I, y ^ 4 = 1 → y ^ 2 = 1 := by
    intro y hyI hy4
    by_contra hy2
    have hzI : y ^ 2 ∈ I := I.pow_mem hyI 2
    have hz : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hy4
    have hz1 : y ^ 2 = ((y.1 ^ 2, 1) : UniY F) := by
      refine Prod.ext rfl ?_
      show (y.2 ^ 2 : ↥(rootsOfUnity 2 F)) = 1
      apply Subtype.ext
      have h2 : (y.2 : Fˣ) ^ 2 = 1 := (mem_rootsOfUnity ..).1 y.2.2
      exact h2
    have hσ : y.1 ^ 2 * y.1 ^ 2 = 1 := by
      have := congrArg Prod.fst hz
      simpa [sq] using this
    rcases ringEquiv_eq_refl_or_bar h (σ := y.1 ^ 2) (by simpa [sq] using hσ) with h3 | h3
    · apply hy2
      rw [hz1]
      have : y.1 ^ 2 = 1 := h3
      rw [this]
      rfl
    · apply hy
      have h4 : y.1 ^ 2 = barE h := by
        ext c
        exact h3 c
      rw [← h4, ← hz1]
      exact hzI
  have hsq : ∀ y ∈ I, y * y = 1 := by
    have key : ∀ n : ℕ, ∀ y ∈ I, y ^ (2 ^ (n + 1)) = 1 → y ^ 2 = 1 := by
      intro n
      induction n with
      | zero => intro y hyI h2; simpa using h2
      | succ n ih =>
        intro y hyI hyn
        have h1 : (y ^ 2) ^ (2 ^ (n + 1)) = 1 := by
          rw [← pow_mul, ← pow_succ']; exact hyn
        have h2 := ih (y ^ 2) (I.pow_mem hyI 2) h1
        apply hL y hyI
        rw [show 4 = 2 * 2 from rfl, pow_mul]
        exact h2
    intro y hyI
    obtain ⟨n, hn⟩ := hI y hyI
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have : y = 1 := by simpa using hn
      rw [this, mul_one]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [← sq]
      exact key m y hyI hn
  have hcls : ∀ y ∈ I, y = 1 ∨ y = ((1, rm1 F) : UniY F) ∨ y = ((barE h, rm1 F) : UniY F) := by
    intro y hyI
    have hyy := hsq y hyI
    have hσ : y.1 * y.1 = 1 := by
      have := congrArg Prod.fst hyy
      simpa using this
    rcases ringEquiv_eq_refl_or_bar h hσ with h3 | h3
    · rcases rootsOfUnity_two_eq y.2 with h4 | h4
      · left
        exact Prod.ext h3 h4
      · right; left
        exact Prod.ext h3 h4
    · have h5 : y.1 = barE h := by
        ext c
        exact h3 c
      rcases rootsOfUnity_two_eq y.2 with h4 | h4
      · exfalso
        apply hy
        have : y = (barE h, 1) := Prod.ext h5 h4
        rw [← this]
        exact hyI
      · right; right
        exact Prod.ext h5 h4
  set u : UniY F := ((1, rm1 F) : UniY F) with hu
  set v : UniY F := ((barE h, rm1 F) : UniY F) with hv
  have huv : u * v = ((barE h, 1) : UniY F) := by
    refine Prod.ext (one_mul _) ?_
    show rm1 F * rm1 F = 1
    apply Subtype.ext
    apply Units.ext
    simp [rm1]
  have hu2 : u ^ 2 = 1 := by
    refine Prod.ext (by show (1 : F ≃+* F) ^ 2 = 1; exact one_pow 2) ?_
    show (rm1 F) ^ 2 = 1
    apply Subtype.ext
    apply Units.ext
    simp [rm1]
  have hv2 : v ^ 2 = 1 := by
    refine Prod.ext ?_ ?_
    · show barE h ^ 2 = 1
      rw [sq]; exact barE_sq h
    · show (rm1 F) ^ 2 = 1
      apply Subtype.ext
      apply Units.ext
      simp [rm1]
  by_cases huI : u ∈ I
  · have hle : I ≤ Subgroup.zpowers u := by
      intro y hyI
      rcases hcls y hyI with h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers u
      · exfalso
        apply hy
        rw [← huv]
        exact I.mul_mem huI (h1 ▸ hyI)
    calc Nat.card I ≤ Nat.card (Subgroup.zpowers u) := Subgroup.card_le_of_le hle
      _ = orderOf u := Nat.card_zpowers u
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hu2
  · have hle : I ≤ Subgroup.zpowers v := by
      intro y hyI
      rcases hcls y hyI with h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · exfalso; exact huI (h1 ▸ hyI)
      · rw [h1]; exact Subgroup.mem_zpowers v
    calc Nat.card I ≤ Nat.card (Subgroup.zpowers v) := Subgroup.card_le_of_le hle
      _ = orderOf v := Nat.card_zpowers v
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hv2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem J2mat_map (h : UnitaryFieldData p f F) : (J2mat : Matrix (Fin 2) (Fin 2) F).map h.bar = J2mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2mat]

@[expose] noncomputable def Jgl (F : Type) [Field F] : GL (Fin 4) F :=
  Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F))

theorem Jgl_val : ((Jgl F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 J2mat J2mat := rfl

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem Jgl_map (h : UnitaryFieldData p f F) :
    ((Jgl F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar =
      ((Jgl F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Jgl_val]
  show (diagBlock J2mat J2mat).map h.bar = diagBlock J2mat J2mat
  rw [diagBlock_map, J2mat_map]

theorem risom_Jgl (h : UnitaryFieldData p f F) : RIsom h ((Jgl F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold RIsom
  rw [Jgl_map, Jgl_val, rblk4_transpose, J2mat_transpose, blk4_mul]
  have h1 : (-(J2mat : Matrix (Fin 2) (Fin 2) F)) * J2mat = 1 := by
    rw [neg_mul, J2mat_mul_self, neg_neg]
  rw [h1]
  exact blk4_one

@[expose] noncomputable def g0U (h : UnitaryFieldData p f F) : UniPair h :=
  ⟨⟨Jgl F, barE h⟩, risom_Jgl h⟩

theorem uniAct_g0 (h : UnitaryFieldData p f F) (k : ↥(StatedSU 4 (p ^ f) F)) :
    ((uniAct h (g0U h) k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      Jgl F * glAut (barE h) (k : GL (Fin 4) F) * (Jgl F)⁻¹ := rfl

theorem rglAut_bar (h : UnitaryFieldData p f F) (kS : SL(4, F))
    (hk : RIsom h (kS : Matrix (Fin 4) (Fin 4) F)) :
    glAut (barE h) (Matrix.SpecialLinearGroup.toGL kS) =
      Matrix.SpecialLinearGroup.toGL (CatalogueBGraphForm.slGraphAut 4 F kS) := by
  apply Units.ext
  rw [coe_glAut]
  have h2 : (kS : Matrix (Fin 4) (Fin 4) F) * ((kS⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h3 : ((kS : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ = ((kS⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
    left_inv_eq_right_inv hk h2
  have h4 : (kS : Matrix (Fin 4) (Fin 4) F).map h.bar =
      ((kS⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    rw [← h3, Matrix.transpose_transpose]
  show (kS : Matrix (Fin 4) (Fin 4) F).map (barE h) = _
  have h5 : (kS : Matrix (Fin 4) (Fin 4) F).map (barE h) =
      (kS : Matrix (Fin 4) (Fin 4) F).map h.bar := rfl
  rw [h5, h4]
  rfl

@[expose] def rframe (q : Q8 →* SL(2, F)) : Q8 × Q8 →* SL(4, F) where
  toFun a := blkSL4 (q a.1) (q a.2)
  map_one' := by simp [blkSL4_one]
  map_mul' a a' := by simp [blkSL4_mul]

theorem rframe_inj {q : Q8 →* SL(2, F)} (hq : Function.Injective q) :
    Function.Injective (rframe q) := by
  intro a a' h
  have := blkSL4_inj h
  exact Prod.ext (hq this.1) (hq this.2)

theorem rframe_isom (h : UnitaryFieldData p f F) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (ha : h.bar a = -a) (hb : h.bar b = -b) (x : Q8 × Q8) :
    RIsom h ((rframe (quatHom hab) x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
  (isUni_quatHom hab ha hb x.1).diagBlock (isUni_quatHom hab ha hb x.2)

theorem rframe_mem (h : UnitaryFieldData p f F) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (ha : h.bar a = -a) (hb : h.bar b = -b) (x : Q8 × Q8) :
    Matrix.SpecialLinearGroup.toGL (rframe (quatHom hab) x) ∈ StatedSU 4 (p ^ f) F := by
  rw [rmem_statedSU h]
  exact ⟨(rframe (quatHom hab) x).det_coe, rframe_isom h hab ha hb x⟩

theorem uniAct_frame_fix (h : UnitaryFieldData p f F) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (ha : h.bar a = -a) (hb : h.bar b = -b) (x : Q8 × Q8) :
    ((uniAct h (g0U h) ⟨Matrix.SpecialLinearGroup.toGL (rframe (quatHom hab) x),
        rframe_mem h hab ha hb x⟩ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      Matrix.SpecialLinearGroup.toGL (rframe (quatHom hab) x) := by
  rw [uniAct_g0]
  show Jgl F * glAut (barE h) (Matrix.SpecialLinearGroup.toGL (rframe (quatHom hab) x)) *
    (Jgl F)⁻¹ = _
  rw [rglAut_bar h _ (rframe_isom h hab ha hb x)]
  show Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F)) *
    Matrix.SpecialLinearGroup.toGL (CatalogueBGraphForm.slGraphAut 4 F (rframe (quatHom hab) x)) *
    (Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F)))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← tauJ_apply]
  exact blkSL4_fix _ _

theorem glAut_barE_Jgl (h : UnitaryFieldData p f F) : glAut (barE h) (Jgl F) = Jgl F := by
  apply Units.ext
  rw [coe_glAut]
  exact Jgl_map h

theorem Jgl_mul_self : Jgl F * Jgl F = Matrix.SpecialLinearGroup.toGL (rNegOne : SL(4, F)) := by
  show Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F)) * Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F)) = _
  rw [← map_mul, Jsl_sq]

theorem rNegOne_gl_central (g : GL (Fin 4) F) :
    Matrix.SpecialLinearGroup.toGL (rNegOne : SL(4, F)) * g =
      g * Matrix.SpecialLinearGroup.toGL (rNegOne : SL(4, F)) := by
  apply Units.ext
  show ((rNegOne : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
    (g : Matrix (Fin 4) (Fin 4) F) * ((rNegOne : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  rw [rNegOne_val]
  simp

theorem uniAct_g0_sq (h : UnitaryFieldData p f F) : uniAct h (g0U h) * uniAct h (g0U h) = 1 := by
  refine MulEquiv.ext fun k => Subtype.ext ?_
  show ((uniAct h (g0U h) (uniAct h (g0U h) k) : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = _
  rw [uniAct_g0, uniAct_g0]
  have hbb : ∀ g : GL (Fin 4) F, glAut (barE h) (glAut (barE h) g) = g := by
    intro g
    rw [← MulAut.mul_apply, ← map_mul, barE_sq, map_one]
    rfl
  rw [map_mul, map_mul, map_inv, hbb, glAut_barE_Jgl]
  show Jgl F * (Jgl F * (k : GL (Fin 4) F) * (Jgl F)⁻¹) * (Jgl F)⁻¹ = _
  calc Jgl F * (Jgl F * (k : GL (Fin 4) F) * (Jgl F)⁻¹) * (Jgl F)⁻¹
      = (Jgl F * Jgl F) * (k : GL (Fin 4) F) * (Jgl F * Jgl F)⁻¹ := by
        simp only [_root_.mul_inv_rev, mul_assoc]
    _ = (k : GL (Fin 4) F) := by
        rw [Jgl_mul_self, rNegOne_gl_central, mul_assoc, mul_inv_cancel, mul_one]

theorem uniAct_g0_not_inner (h : UnitaryFieldData p f F) (hq5 : 5 ≤ p ^ f)
    (s : ↥(StatedSU 4 (p ^ f) F)) : uniAct h (g0U h) ≠ MulAut.conj s := by
  classical
  intro heq
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨w, hw⟩ := sp_exists_normOne_mul_self_ne_one hF hq5
  set ω : F := ((w : Fˣ) : F) with hωdef
  have hω0 : ω ≠ 0 := (w : Fˣ).ne_zero
  have hωb : h.bar ω * ω = 1 := by
    have h1 : CFSG.LieType.BorelTits.unitaryInvolution F p f ω * ω = 1 := w.2
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
    rw [UnitaryFieldData.bar_apply]
    exact h1
  have hωne : ω ≠ 1 := by
    intro h1
    apply hw
    rw [h1, one_mul]
  set dd : Fin 4 → F := ![ω, ω, (ω * ω)⁻¹, 1] with hdd
  have hdet : (Matrix.diagonal dd).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    show ω * ω * (ω * ω)⁻¹ * 1 = 1
    rw [mul_one]
    exact mul_inv_cancel₀ (mul_ne_zero hω0 hω0)
  have hunit : IsUnit (Matrix.diagonal dd).det := by rw [hdet]; exact isUnit_one
  let kD : GL (Fin 4) F := Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal dd) hunit
  have hkD : (kD : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal dd := rfl
  have hbd : ∀ i, h.bar (dd i) * dd i = 1 := by
    intro i
    fin_cases i
    · exact hωb
    · exact hωb
    · simp only [hdd]
      show h.bar ((ω * ω)⁻¹) * (ω * ω)⁻¹ = 1
      rw [map_inv₀, map_mul, ← mul_inv]
      have : h.bar ω * h.bar ω * (ω * ω) = 1 := by
        calc h.bar ω * h.bar ω * (ω * ω) = (h.bar ω * ω) * (h.bar ω * ω) := by ring
          _ = 1 := by rw [hωb, one_mul]
      rw [this, inv_one]
    · simp [hdd]
  have hkDmem : kD ∈ StatedSU 4 (p ^ f) F := by
    rw [rmem_statedSU h, hkD]
    refine ⟨hdet, ?_⟩
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun i => h.bar (dd i) * dd i) = fun _ => (1 : F) := funext hbd
    rw [this]
    exact Matrix.diagonal_one
  have hEq := congrArg (fun φ : MulAut ↥(StatedSU 4 (p ^ f) F) =>
    ((φ ⟨kD, hkDmem⟩ : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F)) heq
  simp only [uniAct_g0, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hEq
  set Nn : GL (Fin 4) F := (s : GL (Fin 4) F)⁻¹ * Jgl F with hNn
  have hNB : Nn * glAut (barE h) kD = kD * Nn := by
    have E2 : Jgl F * glAut (barE h) kD = (s : GL (Fin 4) F) * kD * (s : GL (Fin 4) F)⁻¹ * Jgl F := by
      rw [← hEq]; group
    rw [hNn, mul_assoc, E2]
    group
  have hmat : (Nn : Matrix (Fin 4) (Fin 4) F) * (Matrix.diagonal (h.bar ∘ dd)) =
      Matrix.diagonal dd * (Nn : Matrix (Fin 4) (Fin 4) F) := by
    have h1 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hNB
    simp only [Units.val_mul, coe_glAut, hkD] at h1
    have h2 : (Matrix.diagonal dd).map (barE h) = Matrix.diagonal (h.bar ∘ dd) :=
      Matrix.diagonal_map (map_zero h.bar)
    rw [h2] at h1
    exact h1
  have hrow : ∀ j, (Nn : Matrix (Fin 4) (Fin 4) F) 0 j = 0 := by
    intro j
    have h1 := congrFun (congrFun hmat 0) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (Nn : Matrix (Fin 4) (Fin 4) F) 0 j * (h.bar (dd j) - ω) = 0 := by
      simp only [Function.comp] at h1
      have h3 : dd 0 = ω := rfl
      rw [h3] at h1
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exfalso
      have h4 : h.bar (dd j) = ω := sub_eq_zero.1 h3
      fin_cases j
      · exact hw (by have : h.bar ω = ω := h4; rw [this] at hωb; exact hωb)
      · exact hw (by have : h.bar ω = ω := h4; rw [this] at hωb; exact hωb)
      · apply hωne
        change h.bar ((ω * ω)⁻¹) = ω at h4
        rw [map_inv₀, map_mul] at h4
        have h5 : h.bar ω = ω⁻¹ := eq_inv_of_mul_eq_one_left hωb
        rw [h5, mul_inv, inv_inv] at h4
        exact mul_left_cancel₀ hω0 (h4.trans (mul_one ω).symm)
      · apply hωne
        change h.bar (1 : F) = ω at h4
        rw [map_one] at h4
        exact h4.symm
  have hdet0 : (Nn : Matrix (Fin 4) (Fin 4) F).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 0 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 Nn.isUnit).ne_zero hdet0

theorem rcongr_conj {C G : Type} [Group C] [Group G] (K : Subgroup C) [K.Normal] (e : ↥K ≃* G)
    (s : G) : MulAut.congr e.symm (MulAut.conj s) = MulAut.conjNormal ((e.symm s : ↥K) : C) := by
  ext k
  have h1 : (MulAut.congr e.symm (MulAut.conj s)) k = e.symm s * k * (e.symm s)⁻¹ := by
    show e.symm (s * e k * s⁻¹) = _
    rw [map_mul, map_mul, map_inv, e.symm_apply_apply]
  rw [h1, MulAut.conjNormal_apply]
  rfl

theorem rdU_Jgl (p f : ℕ) : rdU p f (Jgl F) = 1 := by
  unfold rdU
  have : Matrix.GeneralLinearGroup.det (Jgl F) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact (Jsl : SL(4, F)).det_coe
  rw [this, one_pow]

theorem uniChi_g0 (h : UnitaryFieldData p f F) (hq : p ^ f % 2 = 1) :
    uniChi h hq (g0U h) = ((barE h, 1) : UniY F) :=
  Prod.ext rfl (Subtype.ext (rdU_Jgl p f))

theorem outBound_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    {C : Type} [Group C] [Finite C] (hC : Gen4 C) (K : Subgroup C) [K.Normal]
    (e : ↥K ≃* ↥(StatedSU 4 (p ^ f) F)) (hcent : Subgroup.centralizer (K : Set C) ≤ K)
    (T : Subgroup C) (hT : IsPGroup 2 T) : (K.subgroupOf T).index ≤ 2 := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  have hq2 : p ^ f % 2 = 1 := by omega
  have hq1 : 1 < p ^ f := by
    have h1 := h.prime.one_lt
    have h2 := h.one_le
    calc 1 < p := h1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) h2
  have hq5 : 5 ≤ p ^ f := by omega
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hF
  have ha' : h.bar a = -a := by rw [UnitaryFieldData.bar_apply]; exact ha
  have hb' : h.bar b = -b := by rw [UnitaryFieldData.bar_apply]; exact hb
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hq : Function.Injective (quatHom hab : Q8 →* SL(2, F)) := quatHom_injective hK2 hab
  let frameU : Q8 × Q8 →* ↥(StatedSU 4 (p ^ f) F) :=
    ((Matrix.SpecialLinearGroup.toGL : SL(4, F) →* GL (Fin 4) F).comp (rframe (quatHom hab))).codRestrict
      (StatedSU 4 (p ^ f) F) (rframe_mem h hab ha' hb')
  have hfrinj : Function.Injective frameU := by
    intro x y hxy
    apply rframe_inj hq
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val hxy
  let φ : Q8 × Q8 →* C := K.subtype.comp (e.symm.toMonoidHom.comp frameU)
  have hφ : Function.Injective φ := K.subtype_injective.comp (e.symm.injective.comp hfrinj)
  have hφK : ∀ x, φ x ∈ K := fun x => (e.symm (frameU x)).2
  let ρ : UniPair h →* MulAut ↥K := (MulAut.congr e.symm).toMonoidHom.comp (uniAct h)
  have hcover : ∀ t : C, (∃ n : ℕ, t ^ (2 ^ n) = 1) → ∃ x : UniPair h,
      ρ x = MulAut.conjNormal t := by
    rintro t -
    set α : MulAut ↥(StatedSU 4 (p ^ f) F) := MulAut.congr e (MulAut.conjNormal t) with hα
    obtain ⟨N, σ, hN, hrep⟩ := uni_aut_rep h hp2 α
    refine ⟨⟨⟨N, σ⟩, hN⟩, ?_⟩
    have hx : uniAct h ⟨⟨N, σ⟩, hN⟩ = α := by
      refine MulEquiv.ext fun k => Subtype.ext ?_
      rw [uniAct_apply]
      exact (hrep k).symm
    show MulAut.congr e.symm (uniAct h ⟨⟨N, σ⟩, hN⟩) = _
    rw [hx, hα]
    ext k
    simp [MulAut.congr_apply]
  have hker : ∀ x : UniPair h, uniChi h hq2 x = 1 → ∃ k : ↥K,
      ρ x = MulAut.conjNormal (k : C) := by
    rintro ⟨⟨N, σ⟩, hN⟩ hx
    have h1 := Prod.ext_iff.1 hx
    have hσ : σ = 1 := h1.1
    have hd : rdU p f N = 1 := by
      have := congrArg Subtype.val h1.2
      exact this
    have hd' : (N : Matrix (Fin 4) (Fin 4) F).det ^ ((p ^ f + 1) / 2) = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) hd
      simpa [rdU, Matrix.GeneralLinearGroup.val_det_apply] using this
    obtain ⟨s, hs⟩ := uni_det_inner h hq4 hN hd'
    refine ⟨e.symm s, ?_⟩
    have hx' : uniAct h ⟨⟨N, σ⟩, hN⟩ = MulAut.conj s := by
      refine MulEquiv.ext fun k => Subtype.ext ?_
      rw [uniAct_apply]
      subst hσ
      exact hs k
    show MulAut.congr e.symm (uniAct h ⟨⟨N, σ⟩, hN⟩) = _
    rw [hx', rcongr_conj]
  have hg₀sq : ρ (g0U h) ^ (2 ^ 1) = 1 := by
    show (MulAut.congr e.symm (uniAct h (g0U h))) ^ (2 ^ 1) = 1
    rw [← map_pow, pow_one, pow_two, uniAct_g0_sq, map_one]
  have hfix : ∀ x, ρ (g0U h) ⟨φ x, hφK x⟩ = ⟨φ x, hφK x⟩ := by
    intro x
    have h1 : (⟨φ x, hφK x⟩ : ↥K) = e.symm (frameU x) := rfl
    show MulAut.congr e.symm (uniAct h (g0U h)) ⟨φ x, hφK x⟩ = ⟨φ x, hφK x⟩
    rw [h1]
    show e.symm (uniAct h (g0U h) (e (e.symm (frameU x)))) = e.symm (frameU x)
    rw [e.apply_symm_apply]
    congr 1
    exact Subtype.ext (uniAct_frame_fix h hab ha' hb' x)
  have hninn : ∀ k : ↥K, ρ (g0U h) ≠ MulAut.conjNormal (k : C) := by
    intro k hk
    apply uniAct_g0_not_inner h hq5 (e k)
    have h2 : MulAut.conjNormal (k : C) = MulAut.congr e.symm (MulAut.conj (e k)) := by
      rw [rcongr_conj]
      simp
    have h1 : ρ (g0U h) = MulAut.congr e.symm (uniAct h (g0U h)) := rfl
    rw [h1, h2] at hk
    exact (MulAut.congr e.symm).injective hk
  have hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    intro z hz hzc
    have hcen : ∀ k' : ↥(StatedSU 4 (p ^ f) F), e ⟨z, hz⟩ * k' = k' * e ⟨z, hz⟩ := by
      intro k'
      have := hzc (e.symm k' : C) (e.symm k').2
      have h3 : (⟨z, hz⟩ : ↥K) * e.symm k' = e.symm k' * ⟨z, hz⟩ := Subtype.ext this
      have h4 := congrArg e h3
      simpa using h4
    have h5 := uni_center_pow_four h hcen
    refine ⟨2, ?_⟩
    have h6 : (⟨z, hz⟩ : ↥K) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h5, map_one]
    have h7 := congrArg Subtype.val h6
    simpa using h7
  have hgrp : ∀ I : Subgroup (UniY F), (∀ y ∈ I, ∃ n : ℕ, y ^ (2 ^ n) = 1) →
      uniChi h hq2 (g0U h) ∉ I → Nat.card I ≤ 2 := by
    intro I hI hy
    rw [uniChi_g0] at hy
    exact uniY_card_le_two h I hI hy
  exact index_le_two_of_frame_type hC K hcent ρ (uniY_comm h) (uniChi h hq2) hcover hker φ hφ hφK
    (g0U h) ⟨1, hg₀sq⟩ hfix hninn hZ hgrp T hT

end CFSG.GH74.Generic.S1.Uni
