module

public import CFSG.GH74.Generic.BProg.B2.T3S1Mat
public import CFSG.GH74.Generic.BProg.B1.PilotS1Models
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs
public import CFSG.GH74.Generic.S1.LinDiag
public import CFSG.GH74.Generic.S1.LinGraph

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Matrix Subgroup Module
open scoped MatrixGroups

namespace Lin

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem mem_statedSL_iff' (g : GL (Fin 4) F) :
    g ∈ StatedSL 4 F ↔ (g : Matrix (Fin 4) (Fin 4) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

omit [Finite F] in
theorem det_inv_mul (P : GL (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F).det * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

omit [Finite F] in
theorem det_conj (P g : GL (Fin 4) F) :
    ((P * g * P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = (g : Matrix (Fin 4) (Fin 4) F).det := by
  have h := det_inv_mul P
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul]
  linear_combination ((g : Matrix (Fin 4) (Fin 4) F).det) * h

theorem center_lin (hF : Nat.card F % 4 = 3) :
    ∃ z : ↥(StatedSL 4 F), z ≠ 1 ∧
      (∀ g : ↥(StatedSL 4 F), g ∈ Subgroup.center ↥(StatedSL 4 F) ↔ g = 1 ∨ g = z) ∧
      ∀ E : Subgroup ↥(StatedSL 4 F), IsE8 E → z ∈ E := by
  obtain ⟨z, hz⟩ := B1.PilotS1.grpS1_lin hF
  refine ⟨z, ?_, hz.center, fun E hE => hz.e8 E hE.1 hE.2⟩
  intro h1
  have := hz.like.z_ord
  rw [h1, orderOf_one] at this
  omega

theorem frame (h2 : (2 : F) ≠ 0) (E : Subgroup ↥(StatedSL 4 F)) (hE : IsE8 E) :
    ∃ P : GL (Fin 4) F, ∀ e ∈ E, P⁻¹ * (e : GL (Fin 4) F) * P ∈ signDiag4 F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' : Subgroup (GL (Fin 4) F) := E.map (StatedSL 4 F).subtype with hE'
  have hel := hE.1
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun g : ↥E => ((g : ↥(StatedSL 4 F)) : GL (Fin 4) F)) this
  have hsq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a ha
    rw [sq] at this
    exact congrArg Subtype.val this
  obtain ⟨P, hP⟩ := exists_diag_frame h2 E' hcomm hsq
  refine ⟨P, fun e he => ?_⟩
  obtain ⟨μ, hμ, hPe⟩ := hP _ ⟨e, he, rfl⟩
  exact mem_signDiag4_of_frame hμ hPe ((mem_statedSL_iff' _).1 e.2)

omit [Finite F] in
theorem conj_mem_range (P : GL (Fin 4) F) :
    ∀ d ∈ signDiag4 F, P * d * P⁻¹ ∈ (StatedSL 4 F).subtype.range := by
  intro d hd
  refine ⟨⟨P * d * P⁻¹, (mem_statedSL_iff' _).2 ?_⟩, rfl⟩
  rw [det_conj, det_of_mem_signDiag4 hd]

theorem conj (h2 : (2 : F) ≠ 0) (E E' : Subgroup ↥(StatedSL 4 F)) (hE : IsE8 E) (hE' : IsE8 E') :
    ∃ k : ↥(StatedSL 4 F), E' = E.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨P, hP⟩ := frame h2 E hE
  obtain ⟨P', hP'⟩ := frame h2 E' hE'
  have hdP : (P : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
  have hdP' : (P' : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units P').ne_zero
  set t : F := (P : Matrix (Fin 4) (Fin 4) F).det / (P' : Matrix (Fin 4) (Fin 4) F).det with ht
  have ht0 : t ≠ 0 := div_ne_zero hdP hdP'
  let d : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![t, 1, 1, 1])
    (by rw [det_diagonal, Fin.prod_univ_four]; simpa using ht0)
  have hd : (d : Matrix (Fin 4) (Fin 4) F) = diagonal ![t, 1, 1, 1] := rfl
  have hP'' : ∀ e ∈ E', (P' * d)⁻¹ * (e : GL (Fin 4) F) * (P' * d) ∈ signDiag4 F :=
    fun e he => frame_mul_diag hd (hP' e he)
  have hk : P' * d * P⁻¹ ∈ StatedSL 4 F := by
    rw [mem_statedSL_iff', Units.val_mul, Units.val_mul, det_mul, det_mul, hd, det_diagonal,
      Fin.prod_univ_four]
    have h1 := det_inv_mul P
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one]
    rw [ht]
    field_simp
    linear_combination h1
  exact ⟨⟨_, hk⟩, conj_of_frames (StatedSL 4 F).subtype (Subgroup.subtype_injective _) h2 hE.2
    hE'.2 hP hP'' rfl⟩

theorem invol (h2 : (2 : F) ≠ 0) (t : ↥(StatedSL 4 F)) (ht : t * t = 1) :
    ∃ E : Subgroup ↥(StatedSL 4 F), IsE8 E ∧ t ∈ E := by
  classical
  set W : Subgroup (GL (Fin 4) F) := zpowers (t : GL (Fin 4) F) with hW
  have htt : (t : GL (Fin 4) F) * t = 1 := congrArg Subtype.val ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self _ m n).eq
  have hsq : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show (t : GL (Fin 4) F) ^ (2 : ℤ) = 1 by
      rw [_root_.zpow_two, htt], _root_.one_zpow]
  obtain ⟨P, hP⟩ := exists_diag_frame h2 W hcomm hsq
  obtain ⟨μ, hμ, hPt⟩ := hP _ (mem_zpowers _)
  have hts : P⁻¹ * (t : GL (Fin 4) F) * P ∈ signDiag4 F :=
    mem_signDiag4_of_frame hμ hPt ((mem_statedSL_iff' _).1 t.2)
  refine ⟨((signDiag4 F).map (MulAut.conj P).toMonoidHom).comap (StatedSL 4 F).subtype,
    isE8_comap _ (Subgroup.subtype_injective _) h2 P (conj_mem_range P), ?_⟩
  refine ⟨P⁻¹ * (t : GL (Fin 4) F) * P, hts, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, Subgroup.coe_subtype]
  group

omit [Finite F] in
theorem fix_of_conj {α : MulAut ↥(StatedSL 4 F)} {ρ P : GL (Fin 4) F} {μ : Fin 4 → F}
    (hα : ∀ k : ↥(StatedSL 4 F), ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) = ρ * k * ρ⁻¹)
    (hP : ((P⁻¹ * ρ * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal μ) :
    ∀ k ∈ ((signDiag4 F).map (MulAut.conj P).toMonoidHom).comap (StatedSL 4 F).subtype, α k = k := by
  intro k hk
  obtain ⟨s, ⟨ε, -, hs⟩, hsk⟩ := hk
  have hsk' : (k : GL (Fin 4) F) = P * s * P⁻¹ := hsk.symm
  have hc : (P⁻¹ * ρ * P) * s = s * (P⁻¹ * ρ * P) := comm_of_diag hP hs
  apply Subtype.ext
  rw [hα, hsk']
  calc ρ * (P * s * P⁻¹) * ρ⁻¹ = P * ((P⁻¹ * ρ * P) * s) * (P⁻¹ * ρ * P)⁻¹ * P⁻¹ := by group
    _ = P * (s * (P⁻¹ * ρ * P)) * (P⁻¹ * ρ * P)⁻¹ * P⁻¹ := by rw [hc]
    _ = P * s * P⁻¹ := by group

theorem exists_congr_diag (hodd : Odd (Nat.card F)) (S : Matrix (Fin 4) (Fin 4) F) (hS : Sᵀ = S)
    (hdet : S.det ≠ 0) :
    ∃ (Q : GL (Fin 4) F) (δ : Fin 4 → F), S = (Q : Matrix (Fin 4) (Fin 4) F) * diagonal δ *
      (Q : Matrix (Fin 4) (Fin 4) F)ᵀ := by
  classical
  have hBs : (Matrix.toBilin' S).IsSymm := LinearMap.BilinForm.isSymm_def.2 fun x y => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hS, dotProduct_comm]
  have hnd : (Matrix.toBilin' S).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
    hodd (finrank_fin_fun F) (by norm_num) hnd hBs
  obtain ⟨v, hv⟩ := h1 1 one_ne_zero
  obtain ⟨e, he_orth, -, -, -⟩ := h2 1 v one_ne_zero hv
  set Pe := S1.basisMat e with hPe
  have hgram : Peᵀ * S * Pe = diagonal (fun i => Matrix.toBilin' S (e i) (e i)) := by
    ext i j
    rw [hPe, S1.gram_basisMat]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      exact LinearMap.isOrthoᵢ_def.1 he_orth i j hij
  have hPePi : Pe * Pe⁻¹ = 1 := Matrix.mul_nonsing_inv _ (S1.isUnit_det_basisMat e)
  have hdetQ : ((Pe⁻¹)ᵀ).det ≠ 0 := by
    rw [det_transpose]
    exact (isUnit_det_of_left_inverse hPePi).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((Pe⁻¹)ᵀ) hdetQ,
    fun i => Matrix.toBilin' S (e i) (e i), ?_⟩
  show S = (Pe⁻¹)ᵀ * _ * ((Pe⁻¹)ᵀ)ᵀ
  rw [transpose_transpose, ← hgram]
  calc S = (Pe * Pe⁻¹)ᵀ * S * (Pe * Pe⁻¹) := by
        rw [hPePi, transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = (Pe⁻¹)ᵀ * (Peᵀ * S * Pe) * Pe⁻¹ := by
        simp only [transpose_mul, Matrix.mul_assoc]

omit [Finite F] in
theorem fix_of_graph_diag {α : MulAut ↥(StatedSL 4 F)} {B Q : GL (Fin 4) F} {δ : Fin 4 → F}
    (hα : ∀ k : ↥(StatedSL 4 F), ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      B * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * B⁻¹)
    (hBQ : (B : Matrix (Fin 4) (Fin 4) F) = (Q : Matrix (Fin 4) (Fin 4) F) * diagonal δ *
      (Q : Matrix (Fin 4) (Fin 4) F)ᵀ) :
    ∀ k ∈ ((signDiag4 F).map (MulAut.conj Q).toMonoidHom).comap (StatedSL 4 F).subtype, α k = k := by
  intro k hk
  obtain ⟨s, hsD, hsk⟩ := hk
  obtain ⟨ε, hε, hs⟩ := hsD
  have hsk' : (k : GL (Fin 4) F) = Q * s * Q⁻¹ := hsk.symm
  apply Subtype.ext
  rw [hα, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, hsk']
  have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right (mul_self_of_mem_signDiag4 ⟨ε, hε, hs⟩)
  set Qm : Matrix (Fin 4) (Fin 4) F := (Q : Matrix (Fin 4) (Fin 4) F) with hQm
  set Qi : Matrix (Fin 4) (Fin 4) F := ((Q⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hQi
  have hQiQ : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hT : Qmᵀ * Qiᵀ = 1 := by rw [← transpose_mul, hQiQ, transpose_one]
  have hinv : (((Q * s * Q⁻¹)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Qm * diagonal ε * Qi := by
    rw [show (Q * s * Q⁻¹)⁻¹ = Q * s⁻¹ * Q⁻¹ by group, hss, Units.val_mul, Units.val_mul, hs]
  have hDs : diagonal δ * diagonal ε = diagonal ε * diagonal δ := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hinv, hBQ, Units.val_mul, Units.val_mul, hs]
  rw [transpose_mul, transpose_mul, diagonal_transpose]
  calc Qm * diagonal δ * Qmᵀ * (Qiᵀ * (diagonal ε * Qmᵀ))
      = Qm * diagonal δ * (Qmᵀ * Qiᵀ) * diagonal ε * Qmᵀ := by simp only [Matrix.mul_assoc]
    _ = Qm * (diagonal δ * diagonal ε) * Qmᵀ := by rw [hT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Qm * (diagonal ε * diagonal δ) * Qmᵀ := by rw [hDs]
    _ = Qm * diagonal ε * (Qi * Qm) * diagonal δ * Qmᵀ := by
        rw [hQiQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Qm * diagonal ε * Qi * (Qm * diagonal δ * Qmᵀ) := by simp only [Matrix.mul_assoc]

theorem goodFixedQ8_of_phiP (hF : Nat.card F % 4 = 3) (α : MulAut ↥(StatedSL 4 F)) (P : GL (Fin 4) F)
    (hfix : ∀ X : SL(2, F),
      ((α (S1.phiP P X) : ↥(StatedSL 4 F)) : GL (Fin 4) F) = P * S1.kronGL X * P⁻¹) :
    GoodFixedQ8 (ThreeModel ↥(StatedSL 4 F)) α := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨⟨a, b, hab⟩, H⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices hF2
  obtain ⟨hdI, hdJ, hII, hJJ, hIJ, -⟩ := H a b hab
  let I' : SL(2, F) := ⟨_, hdI⟩
  let J' : SL(2, F) := ⟨_, hdJ⟩
  have hI'I' : I' * I' = -1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact congrFun (congrFun hII i) j
  have hJ'J' : J' * J' = -1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact congrFun (congrFun hJJ i) j
  have hI'J' : I' * J' = -1 * (J' * I') := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_one_mul]
    exact congrFun (congrFun hIJ i) j
  have hneg : (S1.phiP P (-1) : GL (Fin 4) F) = -1 := by
    rw [S1.coe_phiP, S1.kronGL_neg_one, mul_neg, mul_one, neg_mul, mul_inv_cancel]
  have hnegc : S1.phiP P (-1) ∈ Subgroup.center ↥(StatedSL 4 F) := by
    rw [mem_center_statedSL_four_iff hF]
    right
    rw [hneg, xGL_eq_neg_one]
  have hneg1 : S1.phiP P (-1) ≠ 1 := by
    intro h
    have h' := congrArg (fun g : ↥(StatedSL 4 F) => ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simp only [hneg, Units.val_neg, Units.val_one, Subgroup.coe_one] at h'
    apply h2
    have : (-1 : Matrix (Fin 4) (Fin 4) F) 0 0 = -1 := by simp
    rw [this, Matrix.one_apply_eq] at h'
    linear_combination (-1 : F) * h'
  refine ⟨(S1.phiP P).range, ?_, ?_, S1.phiP P I', ⟨I', rfl⟩, S1.phiP P J', ⟨J', rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, rfl⟩
    exact Subtype.ext (hfix X)
  · refine GoodSub.mono (fun h3 => ?_) (S1.goodSub_range_phiP hF P)
    exact ⟨F, inferInstance, inferInstance, h3, Or.inl ⟨MulEquiv.refl _⟩⟩
  · rw [← map_mul, hI'I']
    exact hnegc
  · rw [← map_mul, hI'I']
    exact hneg1
  · rw [← map_mul, ← map_mul, hI'I', hJ'J']
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hI'I', hI'J']

theorem dich (hF : Nat.card F % 4 = 3) (α : MulAut ↥(StatedSL 4 F)) (hα : α * α = 1) :
    (∃ E : Subgroup ↥(StatedSL 4 F), IsE8 E ∧ ∀ e ∈ E, α e = e) ∨
      GoodFixedQ8 (ThreeModel ↥(StatedSL 4 F)) α := by
  classical
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  let φ : ↥(StatedSL 4 F) ≃* SL(4, F) := (specialLinearGroupEquivStatedSL 4 F).symm
  have hφι : ∀ k : ↥(StatedSL 4 F), ((φ k : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro k
    have := specialLinearGroupEquivStatedSL_coe 4 F (φ k)
    have h3 : specialLinearGroupEquivStatedSL 4 F (φ k) = k := by simp [φ]
    rw [h3] at this
    exact this.symm
  let u : MulAut SL(4, F) := MulAut.congr φ α
  have hu : u * u = 1 := by rw [← map_mul, hα, map_one]
  have huφ : ∀ k, u (φ k) = φ (α k) := fun k => by simp [u, MulAut.congr_apply]
  by_cases hin : GenLocL4Out.IsInnerDiag4 u
  · obtain ⟨x, hx⟩ := hin
    obtain ⟨c, hc0, hc⟩ := GenLocL4Out.innerLift_sq (t := u) (g := x) hx hu
    have hαx : ∀ k : ↥(StatedSL 4 F), ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
        x * (k : GL (Fin 4) F) * x⁻¹ := by
      intro k
      apply Units.ext
      have h1 := hx (φ k)
      rw [huφ, hφι, hφι] at h1
      rw [Units.val_mul, Units.val_mul]
      exact h1
    by_cases hsq : ∃ d : F, d * d = c
    ·
      left
      obtain ⟨d, hd⟩ := hsq
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [← hd, zero_mul])
      set s : Fˣ := (Units.mk0 d hd0)⁻¹ with hsdef
      set ρ : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) s * x with hρ
      have hss : (s : F) * s * c = 1 := by
        simp only [hsdef, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [← hd]
        field_simp
      have hρρ : ρ * ρ = 1 := by
        apply Units.ext
        rw [hρ, Units.val_mul, Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.coe_scalar]
        calc Matrix.scalar (Fin 4) (s : F) * (x : Matrix (Fin 4) (Fin 4) F) *
              (Matrix.scalar (Fin 4) (s : F) * (x : Matrix (Fin 4) (Fin 4) F))
            = ((s : F) * s) • ((x : Matrix (Fin 4) (Fin 4) F) * x) := by
              simp only [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mul,
                Matrix.mul_smul, smul_smul]
          _ = 1 := by rw [hc, smul_smul, hss, one_smul]
      have hαρ : ∀ k : ↥(StatedSL 4 F), ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
          ρ * (k : GL (Fin 4) F) * ρ⁻¹ := by
        intro k
        rw [hαx, hρ, _root_.mul_inv_rev]
        have hcomm := Matrix.GeneralLinearGroup.scalar_commute s (x * (k : GL (Fin 4) F) * x⁻¹)
        calc x * (k : GL (Fin 4) F) * x⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 4) s * (x * (k : GL (Fin 4) F) * x⁻¹) *
              (Matrix.GeneralLinearGroup.scalar (Fin 4) s)⁻¹ := by
              rw [hcomm, mul_inv_cancel_right]
          _ = _ := by group
      set W : Subgroup (GL (Fin 4) F) := zpowers ρ with hW
      have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
        intro a ha b hb
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow_self _ m n).eq
      have hsqW : ∀ a ∈ W, a * a = 1 := by
        intro a ha
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show ρ ^ (2 : ℤ) = 1 by rw [_root_.zpow_two, hρρ], _root_.one_zpow]
      obtain ⟨P, hP⟩ := exists_diag_frame h2 W hcomm hsqW
      obtain ⟨μ, -, hPρ⟩ := hP ρ (mem_zpowers ρ)
      exact ⟨_, isE8_comap _ (Subgroup.subtype_injective _) h2 P (conj_mem_range P),
        fix_of_conj hαρ hPρ⟩
    ·
      right
      have hc' : ∀ μ : F, μ * μ ≠ c := fun μ h => hsq ⟨μ, h⟩
      obtain ⟨P, hP⟩ := S1.exists_conj_compK (x : Matrix (Fin 4) (Fin 4) F) hc hc'
      refine goodFixedQ8_of_phiP hF α P fun X => ?_
      set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
      set Pim : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPim
      have hPPi : Pm * Pim = 1 := by rw [hPm, hPim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hPiP : Pim * Pm = 1 := by rw [hPm, hPim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hPiA : Pim * (x : Matrix (Fin 4) (Fin 4) F) = S1.compK c * Pim := by
        calc Pim * (x : Matrix (Fin 4) (Fin 4) F) =
              Pim * ((x : Matrix (Fin 4) (Fin 4) F) * Pm) * Pim := by
              rw [Matrix.mul_assoc Pim, Matrix.mul_assoc, hPPi, Matrix.mul_one]
          _ = S1.compK c * Pim := by
              rw [hP, ← Matrix.mul_assoc Pim, hPiP, Matrix.one_mul]
      have hcomm : x * (P * S1.kronGL X * P⁻¹) = (P * S1.kronGL X * P⁻¹) * x := by
        apply Units.ext
        simp only [Units.val_mul]
        change (x : Matrix (Fin 4) (Fin 4) F) * (Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim) =
          Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim * (x : Matrix (Fin 4) (Fin 4) F)
        calc (x : Matrix (Fin 4) (Fin 4) F) * (Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim)
            = ((x : Matrix (Fin 4) (Fin 4) F) * Pm) * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim := by
              simp only [Matrix.mul_assoc]
          _ = Pm * (S1.compK c * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F)) * Pim := by
              rw [hP]
              simp only [Matrix.mul_assoc]
          _ = Pm * (S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * S1.compK c) * Pim := by
              rw [S1.kron1_compK]
          _ = Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * (S1.compK c * Pim) := by
              simp only [Matrix.mul_assoc]
          _ = Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * (Pim * (x : Matrix (Fin 4) (Fin 4) F)) := by
              rw [hPiA]
          _ = Pm * S1.kron1 (X : Matrix (Fin 2) (Fin 2) F) * Pim * (x : Matrix (Fin 4) (Fin 4) F) := by
              simp only [Matrix.mul_assoc]
      rw [hαx (S1.phiP P X), S1.coe_phiP]
      exact mul_inv_eq_iff_eq_mul.2 hcomm
  ·
    obtain ⟨B, hB, hsym⟩ := GenLocL4Out.exists_graph_form hF u hu hin
    have hαB : ∀ k : ↥(StatedSL 4 F), ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
        B * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * B⁻¹ := by
      intro k
      apply Units.ext
      have h1 := hB (φ k)
      rw [huφ, hφι] at h1
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, h1]
      have hinv : (((φ k)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
          (((k : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← map_inv, hφι]
        rfl
      rw [hinv]
    have hdetB : (B : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units B).ne_zero
    rcases hsym with hsym | hskew
    · left
      obtain ⟨Q, δ, hBQ⟩ := exists_congr_diag hodd (B : Matrix (Fin 4) (Fin 4) F) hsym hdetB
      exact ⟨_, isE8_comap _ (Subgroup.subtype_injective _) h2 Q (conj_mem_range Q),
        fix_of_graph_diag hαB hBQ⟩
    · right
      obtain ⟨P, hP, hgP⟩ := S1.exists_mul_skewK_transpose h2 _ hskew hdetB
      let Pg : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP.ne_zero
      refine goodFixedQ8_of_phiP hF α Pg fun X => ?_
      rw [hαB (S1.phiP Pg X), S1.coe_phiP]
      refine S1.graph_fix Pg B (-S1.skewK) hgP X ?_
      rw [Matrix.mul_neg, Matrix.neg_mul, S1.kron1_skewK _ X.2]

end Lin

theorem s1Facts_lin {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) :
    S1Facts ↥(StatedSL 4 F) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  exact ⟨Lin.center_lin hF, Lin.conj h2, Lin.invol h2, Lin.dich hF⟩

end CFSG.GH74.Generic.BProg.B2.T3S1
