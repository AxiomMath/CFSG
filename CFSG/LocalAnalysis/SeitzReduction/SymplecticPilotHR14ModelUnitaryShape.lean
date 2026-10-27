module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)

section Fixed

variable {f : ℕ} {K' : Type} [Field K'] {h : UnitaryFieldData 2 f K'} {n : ℕ}
  [CharP h.fixedField 2] {C₀ : GL (Fin (2 * n)) K'}

theorem coe_uModelSU_siegDiag
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) (p : Fin n) :
    (((uModelSU h hC₀ (siegDiag h.fixedField p 1) :
        gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K') =
      1 + single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) 1 := by
  rw [coe_uModelSU, coe_spModelSL_siegDiag]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp

omit [CharP h.fixedField 2] in
theorem transpose_mul_add_single_mul_of_fixed [CharP K' 2] (p : Fin n)
    {G : Matrix (Fin (2 * n)) (Fin (2 * n)) K'}
    (hfix : (1 + single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) 1) * G.map h.bar *
      (1 + single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) 1) = G)
    (hU : (G.map h.bar)ᵀ * blockSwapJ (2 * n) n * G = blockSwapJ (2 * n) n) :
    Gᵀ * (blockSwapJ (2 * n) n + single (spModelIdx n (Sum.inr p)) (spModelIdx n (Sum.inr p)) 1) *
      G = blockSwapJ (2 * n) n + single (spModelIdx n (Sum.inr p)) (spModelIdx n (Sum.inr p)) 1 := by
  set a := spModelIdx n (Sum.inl p) with ha
  set b := spModelIdx n (Sum.inr p) with hb
  set Z : Matrix (Fin (2 * n)) (Fin (2 * n)) K' := 1 + single a b 1 with hZ
  have hab : a ≠ b := fun e => Sum.inl_ne_inr ((spModelIdx n).injective e)
  have hZZ : Z * Z = 1 := by
    rw [hZ, ha, hb, ← coe_spModelSL_siegDiag (F := K'), ← Matrix.SpecialLinearGroup.coe_mul,
      ← map_mul, siegDiag_one_mul_self, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hZt : Zᵀ * Zᵀ = 1 := by rw [← transpose_mul, hZZ, transpose_one]
  have hZJ : Zᵀ * blockSwapJ (2 * n) n = blockSwapJ (2 * n) n + single b b 1 := by
    have h1 : (single a b (1 : K'))ᵀ * blockSwapJ (2 * n) n = single b b 1 := by
      rw [transpose_single]
      have := congrArg transpose (blockSwapJ_two_mul_mul_single (F := K') p)
      rw [transpose_mul, transpose_single, transpose_single,
        CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_transpose] at this
      exact this
    rw [hZ, transpose_add, transpose_one, add_mul, one_mul, h1]
  have hbar : G.map h.bar = Z * G * Z := by
    calc G.map h.bar = (Z * Z) * G.map h.bar * (Z * Z) := by rw [hZZ, one_mul, mul_one]
      _ = Z * (Z * G.map h.bar * Z) * Z := by simp only [Matrix.mul_assoc]
      _ = Z * G * Z := by rw [hfix]
  rw [hbar, transpose_mul, transpose_mul] at hU
  have hU' : Zᵀ * (Gᵀ * (Zᵀ * (blockSwapJ (2 * n) n * G))) = blockSwapJ (2 * n) n := by
    simpa only [Matrix.mul_assoc] using hU
  calc Gᵀ * (blockSwapJ (2 * n) n + single b b 1) * G
      = Gᵀ * (Zᵀ * blockSwapJ (2 * n) n) * G := by rw [hZJ]
    _ = (Zᵀ * Zᵀ) * (Gᵀ * (Zᵀ * blockSwapJ (2 * n) n) * G) := by rw [hZt, Matrix.one_mul]
    _ = Zᵀ * (Zᵀ * (Gᵀ * (Zᵀ * (blockSwapJ (2 * n) n * G)))) := by simp only [Matrix.mul_assoc]
    _ = Zᵀ * blockSwapJ (2 * n) n := by rw [hU']
    _ = blockSwapJ (2 * n) n + single b b 1 := hZJ

omit [CharP h.fixedField 2] in
theorem exists_sq_eq_of_norm_eq_one_of_charTwo [CharP K' 2] {m : ℕ} {c : K'ˣ} (hcN : h.norm (c : K') = 1)
    (hcm : c ^ m = 1) : ∃ μ : K'ˣ, μ * μ = c ∧ h.norm (μ : K') = 1 ∧ μ ^ m = 1 := by
  have : Finite K' := h.finite
  have : Fintype K' := Fintype.ofFinite K'
  obtain ⟨μ₀, hμ₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K' 2) (c : K')
  have hμ0 : μ₀ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ₀
    exact c.ne_zero hμ₀
  set μ : K'ˣ := Units.mk0 μ₀ hμ0 with hμ
  have hμμ : μ * μ = c := Units.ext (by rw [Units.val_mul, hμ, Units.val_mk0, ← hμ₀])
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  have hsq : ∀ {a : K'}, a * a = 1 → a = 1 := fun {a} ha => by
    have h3 : (a - 1) ^ 2 = 0 := by linear_combination ha + (1 - a) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.mp h3)
  refine ⟨μ, hμμ, hsq ?_, ?_⟩
  · rw [← norm_mul_eq, ← Units.val_mul, hμμ, hcN]
  · have h4 : ((μ ^ m : K'ˣ) : K') * ((μ ^ m : K'ˣ) : K') = 1 := by
      rw [← Units.val_mul, ← mul_pow, hμμ, hcm, Units.val_one]
    exact Units.ext (hsq h4)

theorem fixedSubgroup_conj_uModel_siegDiag_mul_fieldBar [CharP K' 2] (hn : 2 ≤ n)
    (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) (p : Fin n) :
    fixedSubgroup (MulAut.conj (uModelP h hC₀ (siegDiag h.fixedField p 1)) *
        primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) =
      (centralizer ({siegDiag h.fixedField p 1} : Set (StatedSp n h.fixedField))).map
        (uModelP h hC₀) := by
  set z := siegDiag h.fixedField p 1 with hz
  set a := spModelIdx n (Sum.inl p) with ha
  set b := spModelIdx n (Sum.inr p) with hb
  set S := gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') with hS
  set Zs : S := uModelSU h hC₀ z with hZs
  have hZmat : ((Zs : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') =
      1 + single a b 1 := coe_uModelSU_siegDiag hC₀ p
  have hZZ : Zs * Zs = 1 := by rw [hZs, ← map_mul, siegDiag_one_mul_self, map_one]
  have hZinv : Zs⁻¹ = Zs := inv_eq_of_mul_eq_one_right hZZ
  apply le_antisymm
  · intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ((Zs * primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) g * Zs⁻¹ : S) :
        primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) = (g : primeFormP h _) := by
      have h2 : (MulAut.conj (uModelP h hC₀ z) *
          primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) (g : primeFormP h _) = g := hy
      rw [MulAut.mul_apply] at h2
      change MulAut.conj (uModelP h hC₀ z)
        (primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h) (g : primeFormP h _)) = g at h2
      rw [primeFormFieldAut_mk, MulAut.conj_apply, uModelP_apply] at h2
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h2
    obtain ⟨c, hcN, hcm, hc⟩ := QuotientGroup.eq.1 h1.symm
    obtain ⟨μ, hμμ, hμN, hμm⟩ := exists_sq_eq_of_norm_eq_one_of_charTwo (h := h) hcN hcm
    have hμS : GeneralLinearGroup.scalar (Fin (2 * n)) μ ∈ S := by
      refine ⟨?_, ?_⟩
      · rw [GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hμN, one_smul]
      · rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hμm, Units.val_one]
    set g' : S := g * ⟨_, hμS⟩ with hg'
    have hμN' : (⟨_, hμS⟩ : S) ∈ normOneScalars h S (2 * n) := ⟨μ, hμN, hμm, rfl⟩
    have hgg' : (g' : primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) = g := by
      rw [hg', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hμN', mul_one]
    set G := ((g' : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') with hG
    have hcG : ((g⁻¹ * (Zs * primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) g * Zs⁻¹) : S) :
        GL (Fin (2 * n)) K') = GeneralLinearGroup.scalar (Fin (2 * n)) c := hc
    have hX : ((Zs * primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) g * Zs⁻¹ : S) :
        GL (Fin (2 * n)) K') = (g : GL (Fin (2 * n)) K') * GeneralLinearGroup.scalar (Fin (2 * n)) c := by
      rw [← hcG]
      simp
    have hXm := congrArg (fun x : GL (Fin (2 * n)) K' => (x : Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
      hX
    simp only [Subgroup.coe_mul, Units.val_mul, F4Pilot.coe_primeFormFieldSU, hZinv, hZmat,
      GeneralLinearGroup.coe_scalar] at hXm
    have hbarμ : h.bar (μ : K') * (c : K') = (μ : K') := by
      rw [← hμμ, Units.val_mul]
      have h3 : (μ : K') * h.bar (μ : K') = 1 := hμN
      linear_combination (μ : K') * h3
    have hcomm : ∀ (M : Matrix (Fin (2 * n)) (Fin (2 * n)) K') (d : K'),
        M * scalar (Fin (2 * n)) d = scalar (Fin (2 * n)) d * M :=
      fun M d => (Matrix.scalar_commute d (fun _ => Commute.all _ _) M).symm
    have hfix : (1 + single a b 1) * G.map h.bar * (1 + single a b 1) = G := by
      have hGdef : G = ((g : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') *
          scalar (Fin (2 * n)) (μ : K') := by
        rw [hG, hg']
        simp [GeneralLinearGroup.coe_scalar]
      rw [hGdef, Matrix.map_mul, scalar_apply, diagonal_map (map_zero h.bar), ← scalar_apply]
      calc (1 + single a b 1) * ((((g : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K')).map
            h.bar * scalar (Fin (2 * n)) (h.bar (μ : K'))) * (1 + single a b 1)
          = ((1 + single a b 1) * (((g : GL (Fin (2 * n)) K') :
              Matrix (Fin (2 * n)) (Fin (2 * n)) K')).map (UnitaryPilot.barRingEquiv h) *
                (1 + single a b 1)) * scalar (Fin (2 * n)) (h.bar (μ : K')) := by
            simp only [Matrix.mul_assoc]
            rw [← hcomm (1 + single a b 1)]
            rfl
        _ = ((g : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') *
              (scalar (Fin (2 * n)) (c : K') * scalar (Fin (2 * n)) (h.bar (μ : K'))) := by
            rw [hXm, Matrix.mul_assoc]
        _ = ((g : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') *
              scalar (Fin (2 * n)) (μ : K') := by
            rw [← RingHom.map_mul (scalar (Fin (2 * n))), mul_comm (c : K'), hbarμ]
    have hU : (G.map h.bar)ᵀ * blockSwapJ (2 * n) n * G = blockSwapJ (2 * n) n := by
      have := g'.2.1
      rw [hC₀] at this
      exact this
    have hiso := transpose_mul_add_single_mul_of_fixed p hfix hU
    have hJs : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K')ᵀ =
        blockSwapJ (2 * n) n := CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_transpose
    have hJd : ∀ i, (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i = 0 :=
      CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_apply_self (by omega)
    have hrow := row_eq_of_isometry_add_single hJs hJd b hiso
    have hgJ : (g' : GL (Fin (2 * n)) K') ∈ matrixIsometryGroup
        ((spBlockSwapGL n K' : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') := by
      rw [coe_spBlockSwapGL]
      exact transpose_mul_mul_eq_of_isometry_add_single hJs hJd b hiso
    have hcol := col_eq_of_mem_isometry (J := spBlockSwapGL n K') spBlockSwapGL_mul_self
      (blockSwapJ_apply_inl p) (blockSwapJ_apply_inr p) hgJ hrow
    have hGZ := mul_single_eq_single_mul hrow hcol
    have hZZm : (1 + single a b (1 : K')) * (1 + single a b 1) = 1 := by
      rw [← hZmat, ← Units.val_mul, ← Subgroup.coe_mul, hZZ]
      rfl
    have hGbar : G.map h.bar = G := by
      have h4 : G * (1 + single a b 1) = (1 + single a b 1) * G := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hGZ]
      calc G.map h.bar = ((1 + single a b 1) * (1 + single a b 1)) * G.map h.bar *
            ((1 + single a b 1) * (1 + single a b 1)) := by rw [hZZm, Matrix.one_mul, Matrix.mul_one]
        _ = (1 + single a b 1) * ((1 + single a b 1) * G.map h.bar * (1 + single a b 1)) *
            (1 + single a b 1) := by simp only [Matrix.mul_assoc]
        _ = (1 + single a b 1) * G * (1 + single a b 1) := by rw [hfix]
        _ = G * ((1 + single a b 1) * (1 + single a b 1)) := by
            rw [← h4, Matrix.mul_assoc]
        _ = G := by rw [hZZm, Matrix.mul_one]
    have hmemk : (g' : GL (Fin (2 * n)) K') ∈ gramSU h
        ((blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField).map
          h.fixedField.subtype) := by
      rw [map_subtype_blockSwapJ, ← hC₀]
      exact g'.2
    obtain ⟨g₀, hg₀J, hg₀⟩ := F4Pilot.exists_eq_map_of_map_bar_eq h hmemk hGbar
    have hg₀O : SpecialLinearGroup.toGL g₀ ∈ matrixIsometryGroup
        (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) := hg₀J
    set x : StatedSp n h.fixedField :=
      CFSG.ComponentClassification.OutcomeLocal.blockSwapIsometryEquivStatedSp
        (k := h.fixedField) (two_mul n).symm ⟨_, hg₀O⟩ with hxdef
    have hxmat : ((spModelSL n h.fixedField x : SpecialLinearGroup (Fin (2 * n)) h.fixedField) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) = g₀ := by
      simp only [spModelSL, MonoidHom.coe_comp, Function.comp_apply, hxdef,
        MulEquiv.coe_toMonoidHom]
      rw [MulEquiv.symm_apply_apply]
      rfl
    have hxg' : uModelSU h hC₀ x = g' := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_uModelSU, hxmat, ← hg₀]
      rfl
    refine ⟨x, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply uModelSU_injective hC₀
      apply Subtype.ext
      apply Units.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxg',
        ← hZs, hZmat]
      change G * (1 + single a b 1) = (1 + single a b 1) * G
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hGZ]
    · rw [uModelP_apply, hxg', hgg']
  · rintro _ ⟨x, hx, rfl⟩
    have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx
    change MulAut.conj (uModelP h hC₀ z)
      (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (uModelP h hC₀ x)) = uModelP h hC₀ x
    rw [fieldBar_uModelP hC hC₀ x, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul, ← hxz,
      mul_inv_cancel_right]

omit [CharP h.fixedField 2] in
theorem fieldBar_mul_self (hC : IsPrimeFormGram C₀) :
    primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) *
      primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) = 1 := by
  rw [← map_mul]
  have : UnitaryPilot.barRingEquiv h * UnitaryPilot.barRingEquiv h = 1 := by
    ext x
    change UnitaryPilot.barRingEquiv h (UnitaryPilot.barRingEquiv h x) = x
    rw [UnitaryPilot.barRingEquiv_apply, UnitaryPilot.barRingEquiv_apply, h.bar_bar]
  rw [this, map_one]

omit [CharP h.fixedField 2] in
theorem barRingEquiv_ne_one : UnitaryPilot.barRingEquiv h ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  have := congrArg (fun φ : K' ≃+* K' => φ c) h1
  simpa [UnitaryPilot.barRingEquiv_apply] using this

theorem exists_iType_conj_uModel_siegDiag [CharP K' 2] (hn : 2 ≤ n)
    (hq : ¬(2 * n = 3 ∧ 2 ^ f = 2)) (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) (p : Fin n) :
    ∃ (C₁ : GL (Fin (2 * n)) K') (hC₁ : IsPrimeFormGram C₁)
      (θ' : primeFormP h (C₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') ≃*
        primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')),
      (C₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = 1 ∧
      MulAut.conj (uModelP h hC₀ (siegDiag h.fixedField p 1)) *
          primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) =
        MulAut.congr θ' (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
  have : Finite K' := h.finite
  have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have hm : 3 ≤ 2 * n := by omega
  set z := siegDiag h.fixedField p 1 with hz
  set fb := primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) with hfb
  set α := MulAut.conj (uModelP h hC₀ z) * fb with hαdef
  have hαψ : α = primeFormPsi h hC ⟨⟨((uModelSU h hC₀ z : gramSU h _) : GL (Fin (2 * n)) K'),
      (uModelSU h hC₀ z).2.1⟩, UnitaryPilot.barRingEquiv h⟩ := by
    rw [primeFormPsi_apply, primeFormConjHom_eq_conj]
    rfl
  have hfac : ∀ x, primeFormFieldFactor h hC hm hq α x = h.bar x := by
    intro x
    rw [hαψ, primeFormFieldFactor_psi]
    rfl
  have hα2 : α * α = 1 := by
    have hfz : fb (uModelP h hC₀ z) = uModelP h hC₀ z := fieldBar_uModelP hC hC₀ z
    have hzz : uModelP h hC₀ z * uModelP h hC₀ z = 1 := by
      rw [← map_mul, hz, siegDiag_one_mul_self, map_one]
    calc α * α = MulAut.conj (uModelP h hC₀ z) * (fb * MulAut.conj (uModelP h hC₀ z)) * fb := by
          rw [hαdef]
          group
      _ = MulAut.conj (uModelP h hC₀ z * uModelP h hC₀ z) * (fb * fb) := by
          rw [mulAut_mul_conj_eq_conj_apply_mul, hfz, map_mul]
          group
      _ = 1 := by rw [hzz, map_one, fieldBar_mul_self, one_mul]
  have hα1 : α ≠ 1 := by
    intro h1
    have h2 := hfac
    rw [h1, map_one] at h2
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (h2 c).symm
  have hαo : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨-, -, C₁, hC₁, hcase₁, -, -, -, -, ⟨θ', -, hθ'α⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hm hq α hαo hfac
  have hφ : primeFormFieldFactor h hC hm hq α = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hfac, UnitaryPilot.barRingEquiv_apply]
  have hαθ : α = MulAut.congr θ' (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hθ'α x, hφ]
    rfl
  rcases hcase₁ with h1 | ⟨r, hr, hJ⟩
  · exact ⟨C₁, hC₁, θ', h1, hαθ⟩
  · exfalso
    have hrn : n = r := by omega
    subst hrn
    obtain rfl : C₁ = C₀ := Units.ext (hJ.trans hC₀.symm)
    have h1 : Nat.card (fixedSubgroup α) = Nat.card (StatedSp n h.fixedField) := by
      rw [hαθ, LinearPilot.card_fixedSubgroup_congr, ← range_uModelP hn hq hC₁ hC₀,
        ← Nat.card_congr (MonoidHom.ofInjective (uModelP_injective (by omega) hC₀)).toEquiv]
    have h2 : Nat.card (fixedSubgroup α) =
        Nat.card (centralizer ({z} : Set (StatedSp n h.fixedField))) := by
      rw [hαdef, hfb, fixedSubgroup_conj_uModel_siegDiag_mul_fieldBar hn hC hC₀ p,
        Subgroup.card_map_of_injective (uModelP_injective (by omega) hC₀)]
    have h3 : Nat.card (centralizer ({z} : Set (StatedSp n h.fixedField))) <
        Nat.card (StatedSp n h.fixedField) := card_centralizer_siegDiag_lt (K := h.fixedField) p
    omega

end Fixed

end CFSG.SeitzReduction.SymplecticPilot
