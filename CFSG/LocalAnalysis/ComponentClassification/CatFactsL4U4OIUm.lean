module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUj

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def barRE : K ≃+* K where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

theorem bar_conj_mem_SU {A : GL (Fin 4) K} (hAU : A ∈ uMat h 4) (w : unitarySU p f K 4) :
    A * GeneralLinearGroup.map h.bar (w : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4 := by
  have h1 := conj_mem_SU h hAU ⟨glAut (barRE h) (w : GL (Fin 4) K),
    ClassicalInvolution.ModelFacts.UnitaryAut.glAut_mem_unitarySU h (barRE h) w.2⟩
  change A * glAut (barRE h) (w : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4 at h1
  have h2 : glAut (barRE h) (w : GL (Fin 4) K) = GeneralLinearGroup.map h.bar (w : GL (Fin 4) K) :=
    Units.ext (by rw [coe_glAut]; rfl)
  rwa [h2] at h1

theorem map_gramQ {k₀ : Type} [Field k₀] (ι : k₀ →+* K) (δ : k₀) :
    (gramQ δ).map ι = gramQ (ι δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gramQ, map_ofNat]

theorem uStar_conj_gram {P Y : GL (Fin 4) K} {G : Matrix (Fin 4) (Fin 4) K} {d : K}
    (hPP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = d • G)
    (hY : uStar h (Y : Matrix (Fin 4) (Fin 4) K) * G * (Y : Matrix (Fin 4) (Fin 4) K) = G) :
    uStar h ((P * Y * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((P * Y * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  set Pm := (P : Matrix (Fin 4) (Fin 4) K)
  set Pi := (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)
  set Ym := (Y : Matrix (Fin 4) (Fin 4) K)
  have hPi : Pm * Pi = 1 := by
    change (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, uStar_mul, uStar_mul]
  calc uStar h Pi * (uStar h Ym * uStar h Pm) * (Pm * Ym * Pi)
      = uStar h Pi * (uStar h Ym * (uStar h Pm * Pm) * Ym) * Pi := by
        simp only [Matrix.mul_assoc]
    _ = uStar h Pi * (d • (uStar h Ym * G * Ym)) * Pi := by
        rw [hPP, Matrix.mul_smul, Matrix.smul_mul]
    _ = uStar h Pi * (uStar h Pm * Pm) * Pi := by rw [hY, hPP]
    _ = uStar h (Pm * Pi) * (Pm * Pi) := by rw [uStar_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hPi, uStar_one, Matrix.one_mul]

theorem uStar_gram_conj {V X : GL (Fin 4) K} {G : Matrix (Fin 4) (Fin 4) K}
    (hVr : (V : Matrix (Fin 4) (Fin 4) K).map h.bar = V)
    (hVG : (V : Matrix (Fin 4) (Fin 4) K)ᵀ * G * V = G)
    (hX : ((X : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * G * X = G) :
    uStar h ((V * X * V⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * G *
      ((V * X * V⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = G := by
  set Vm := (V : Matrix (Fin 4) (Fin 4) K)
  set Vi := (↑V⁻¹ : Matrix (Fin 4) (Fin 4) K)
  set Xm := (X : Matrix (Fin 4) (Fin 4) K)
  have hVi : Vi * Vm = 1 := by
    change (↑V⁻¹ : Matrix (Fin 4) (Fin 4) K) * (V : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hVir : Vi.map h.bar = Vi := by
    change ((↑V⁻¹ : Matrix (Fin 4) (Fin 4) K)).map h.bar = _
    have : GeneralLinearGroup.map h.bar V = V := Units.ext hVr
    have h1 : GeneralLinearGroup.map h.bar V⁻¹ = V⁻¹ := by rw [map_inv, this]
    exact congrArg Units.val h1
  have hG' : Viᵀ * G * Vi = G := by
    calc Viᵀ * G * Vi = Viᵀ * (Vmᵀ * G * Vm) * Vi := by rw [hVG]
      _ = (Vm * Vi)ᵀ * G * (Vm * Vi) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by
          have hVi' : Vm * Vi = 1 := by
            change (V : Matrix (Fin 4) (Fin 4) K) * (↑V⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          rw [hVi', Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, uStar, Matrix.map_mul, Matrix.map_mul, hVr, hVir,
    Matrix.transpose_mul, Matrix.transpose_mul]
  calc Viᵀ * ((Xm.map h.bar)ᵀ * Vmᵀ) * G * (Vm * Xm * Vi)
      = Viᵀ * ((Xm.map h.bar)ᵀ * (Vmᵀ * G * Vm) * Xm) * Vi := by simp only [Matrix.mul_assoc]
    _ = Viᵀ * G * Vi := by rw [hVG, hX]
    _ = G := hG'

theorem mul_self_eq_neg_one_of_involution (hp2 : p ≠ 2) {δ : h.fixedFieldˣ}
    (hδ : ¬ IsSquare (δ : h.fixedField)) (h2 : (2 : h.fixedField) ≠ 0) (P : GL (Fin 4) K)
    (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →* unitarySU p f K 4)
    (hy : ∀ g, ((y g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)))
    (hg : orderOf (thU p f K (y g)) = 2) : g * g = -1 := by
  classical
  have : Finite K := h.finite
  have : Fact (¬ IsSquare (δ : h.fixedField)) := ⟨hδ⟩
  have hodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  have hsq : thU p f K (y (g * g)) = 1 := by
    have h1 := pow_orderOf_eq_one (thU p f K (y g))
    rw [hg, pow_two] at h1
    rw [map_mul, map_mul]
    exact h1
  have hmem' : y (g * g) ∈ scal p f K := (QuotientGroup.eq_one_iff (N := scal p f K) _).mp hsq
  have hmem : ((y (g * g) : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K :=
    hmem'
  obtain ⟨c, hc⟩ := hmem
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hU : GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 (g * g)) =
      GeneralLinearGroup.scalar (Fin 4) c := by
    have h1 := hy (g * g)
    rw [← hc] at h1
    calc GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 (g * g))
        = P⁻¹ * (P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 (g * g)) * P⁻¹) *
            P := by group
      _ = P⁻¹ * GeneralLinearGroup.scalar (Fin 4) c * P := by rw [h1]
      _ = GeneralLinearGroup.scalar (Fin 4) c * P⁻¹ * P := by
          rw [Subgroup.mem_center_iff.mp hcen P⁻¹]
      _ = _ := by group
  have hentry : ∀ i j, ((Umat δ h2 (g * g) : Matrix (Fin 4) (Fin 4) h.fixedField) i j : K) =
      if i = j then (c : K) else 0 := by
    intro i j
    have h1 := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K) i j) hU
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at h1
    exact h1
  set c₀ := (Umat δ h2 (g * g) : Matrix (Fin 4) (Fin 4) h.fixedField) 0 0 with hc₀
  have hc₀K : (c₀ : K) = c := by rw [hc₀, hentry]; simp
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    have : (c : K) = 0 := by rw [← hc₀K, h0]; rfl
    exact c.ne_zero this
  have hscal : rowOHom δ (hermitianCoordinates (δ : h.fixedField) h2) (g * g) =
      GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c₀ hc₀0) := by
    apply Units.ext
    refine Matrix.ext fun i j => Subtype.ext ?_
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Units.val_mk0]
    change ((Umat δ h2 (g * g) : Matrix (Fin 4) (Fin 4) h.fixedField) i j : K) =
      ((if i = j then c₀ else 0 : h.fixedField) : K)
    rw [hentry]
    split_ifs <;> simp [hc₀K]
  rcases eq_one_or_neg_one_of_rowOHom_scalar hodd hδ _ _ _ hscal with h1 | h1
  · exfalso
    have hgpm : g = 1 ∨ g = -1 := by
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · right
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
        exact CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq
          (OIL.two_ne_zero_ext (δ : h.fixedField) h2) g (by rw [pow_two, h1]) hg1
    have hy1 : y g = 1 := by
      have hU1 : Umat δ h2 g = 1 :=
        (rowOHom_eq_one_iff h2 hδ (hermitianCoordinates (δ : h.fixedField) h2) g).mpr hgpm
      apply Subtype.ext
      rw [hy, hU1, map_one, mul_one, mul_inv_cancel]
      rfl
    rw [hy1, map_one, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · exact h1

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
