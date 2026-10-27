module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4E
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Fix

variable {K : Type} [Field K] {d : ℕ}

theorem exists_hom_fix (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) (hd : 0 < d)
    {G : Type*} [Group G] (ψ : G →* ((Fin d → K) ≃ₗ[K] (Fin d → K)))
    (hψ : ∀ z, ψ z ∈ orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val)) :
    ∃ φ : G →* matrixProjectiveDerived Q,
      (∀ z, φ z ∈ fixedSubgroup (matrixProjectiveConjugationHom Q g)) ∧
        ∀ z, φ z = 1 ↔ ∃ c : K, ∀ v, ψ z v = c • v := by
  classical
  have hJi := derivedLinear_injective Q
  have hR : ∀ z, ψ z ∈ (derivedLinear Q).range := fun z => by
    rw [range_derivedLinear]
    exact (hψ z).1
  set φ₀ : G →* matrixDerived Q := (MonoidHom.ofInjective hJi).symm.toMonoidHom.comp
    (ψ.codRestrict _ hR) with hφ₀def
  have hφ₀ : ∀ z, derivedLinear Q (φ₀ z) = ψ z := fun z =>
    congrArg Subtype.val ((MonoidHom.ofInjective hJi).apply_symm_apply (ψ.codRestrict _ hR z))
  refine ⟨(matrixProjectiveProjection Q).comp φ₀, fun z => ?_, fun z => ?_⟩
  · have hc : derivedLinear Q (φ₀ z) ∈ commutant (coordinateSemilinearMap g.val) := by
      rw [hφ₀]
      exact (hψ z).2
    have hfa := (derivedConj_eq_iff Q g (φ₀ z)).mpr hc
    show matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (φ₀ z)) =
      matrixProjectiveProjection Q (φ₀ z)
    rw [← matrixProjective_comm, hfa]
  · change matrixProjectiveProjection Q (φ₀ z) = 1 ↔ _
    rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hmem
      obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp hmem
      refine ⟨c, fun v => ?_⟩
      rw [← hφ₀, derivedLinear_apply, ← hc,
        LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        have h0 := hc (Pi.single ⟨0, hd⟩ 1)
        rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h0
        simpa using congrFun h0 ⟨0, hd⟩
      refine (mem_matrixDerivedScalars_iff Q _).mpr ⟨Units.mk0 c hc0, ?_⟩
      apply matrixLinearIso.injective
      refine LinearEquiv.ext fun v => ?_
      change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v =
        matrixLinearEquiv (φ₀ z).val v
      rw [LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar,
        ← derivedLinear_apply, hφ₀, hc, Units.val_mk0]

end Fix

section Pair

variable {E : Type} [Field E]

theorem center_of_mul_eq_smul {a b : Matrix.SpecialLinearGroup (Fin 2) E} {r : E}
    (h : ∀ X : Matrix (Fin 2) (Fin 2) E, a.val * X * b.val = r • X) :
    a ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) ∧
      b ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hab : a.val * b.val = r • 1 := by simpa using h 1
  have hbb : b.val * (b⁻¹).val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hbb' : (b⁻¹).val * b.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have ha : a.val = r • (b⁻¹).val := by
    calc a.val = a.val * b.val * (b⁻¹).val := by rw [Matrix.mul_assoc, hbb, Matrix.mul_one]
      _ = r • (b⁻¹).val := by rw [hab, Matrix.smul_mul, Matrix.one_mul]
  have hr : r ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hab
    rw [Matrix.det_mul, a.2, b.2, zero_smul, Matrix.det_zero, one_mul] at h1
    exact one_ne_zero h1
  have hbc : ∀ X : Matrix (Fin 2) (Fin 2) E, X * b.val = b.val * X := by
    intro X
    have h1 := h X
    rw [ha, Matrix.smul_mul, Matrix.smul_mul] at h1
    have h2 : (b⁻¹).val * X * b.val = X := smul_right_injective _ hr h1
    calc X * b.val = b.val * ((b⁻¹).val * X * b.val) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hbb, Matrix.one_mul]
      _ = b.val * X := by rw [h2]
  have hbi : ∀ X : Matrix (Fin 2) (Fin 2) E, X * (b⁻¹).val = (b⁻¹).val * X := by
    intro X
    calc X * (b⁻¹).val = (b⁻¹).val * (b.val * X) * (b⁻¹).val := by
          rw [← Matrix.mul_assoc, hbb', Matrix.one_mul]
      _ = (b⁻¹).val * (X * b.val) * (b⁻¹).val := by rw [hbc]
      _ = (b⁻¹).val * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hbb, Matrix.mul_one]
  refine ⟨Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_,
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_⟩
  · change x.val * a.val = a.val * x.val
    rw [ha, Matrix.mul_smul, Matrix.smul_mul, hbi]
  · change x.val * b.val = b.val * x.val
    exact hbc x.val

variable [Finite E]

theorem exists_elemTwo_of_pair (h2 : (2 : E) ≠ 0) (hodd : Odd (Nat.card E)) {P : Type*}
    [Group P] [Finite P]
    (φ : Matrix.SpecialLinearGroup (Fin 2) E × Matrix.SpecialLinearGroup (Fin 2) E →* P)
    (hker : ∀ a b, φ (a, b) = 1 ↔ a ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) ∧
      b ∈ center (Matrix.SpecialLinearGroup (Fin 2) E)) :
    ∃ E' : Subgroup P, E' ≤ φ.range ∧ ElemTwo E' ∧ 16 ≤ Nat.card E' := by
  set φL := φ.comp (MonoidHom.inl _ _) with hφL
  set φR := φ.comp (MonoidHom.inr _ _) with hφR
  have hkL : φL.ker = center _ := by
    ext a
    rw [MonoidHom.mem_ker, hφL, MonoidHom.comp_apply, MonoidHom.inl_apply, hker]
    exact ⟨fun h => h.1, fun h => ⟨h, one_mem _⟩⟩
  have hkR : φR.ker = center _ := by
    ext b
    rw [MonoidHom.mem_ker, hφR, MonoidHom.comp_apply, MonoidHom.inr_apply, hker]
    exact ⟨fun h => h.2, fun h => ⟨one_mem _, h⟩⟩
  obtain ⟨EL, hEL, hEL2, hEL4⟩ := exists_E4_of_hom h2 hodd φL hkL
  obtain ⟨ER, hER, hER2, hER4⟩ := exists_E4_of_hom h2 hodd φR hkR
  have hcomm : ∀ x ∈ EL, ∀ y ∈ ER, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hEL hx
    obtain ⟨b, rfl⟩ := hER hy
    simp only [hφL, hφR, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hinf : EL ⊓ ER = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hy⟩
    rw [mem_bot]
    obtain ⟨a, rfl⟩ := hEL hx
    obtain ⟨b, hb⟩ := hER hy
    have h1 : φ (a, b⁻¹) = 1 := by
      have : (a, b⁻¹) = ((a, 1) : _ × _) * ((1, b) : _ × _)⁻¹ := by simp
      rw [this, map_mul, map_inv]
      change φL a * (φR b)⁻¹ = 1
      rw [hb, mul_inv_cancel]
    exact (hker a 1).mpr ⟨((hker a b⁻¹).mp h1).1, one_mem _⟩
  obtain ⟨hE, hcard⟩ := elemTwo_sup hEL2 hER2 hcomm hinf
  refine ⟨EL ⊔ ER, sup_le ?_ ?_, hE, (Nat.mul_le_mul hEL4 hER4).trans hcard⟩
  · exact hEL.trans (by rw [hφL, MonoidHom.range_comp]; exact map_le_range _ _)
  · exact hER.trans (by rw [hφR, MonoidHom.range_comp]; exact map_le_range _ _)

end Pair

section Plus

theorem map_mem_commutator_of_perfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) {O : Subgroup H} (hf : ∀ z, f z ∈ O) (z : G) : f z ∈ ⁅O, O⁆ := by
  have h := Subgroup.mem_map_of_mem f (Group.IsPerfect.mem_commutator (g := z))
  rw [commutator_def, Subgroup.map_commutator] at h
  have hle : (⊤ : Subgroup G).map f ≤ O := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  exact Subgroup.commutator_mono hle hle h

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_elemTwo_of_split_model (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (hd : 0 < d) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hτ : ∀ v, coordinateSemilinearMap g.val v = A v) {E : Type} [Field E] [Finite E]
    [Algebra K E] [Module E (Fin d → K)] [IsScalarTower K E (Fin d → K)] (h2E : (2 : E) ≠ 0)
    (hoddE : Odd (Nat.card E)) (hE2 : Nat.card E ≠ 2) (hE3 : Nat.card E ≠ 3)
    {QE : QuadraticForm E (Fin d → K)}
    (eO : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup QE)
    (heO2 : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x, (eO.symm g).val.val x = g.val x)
    (ψ : (Fin d → K) ≃ₗ[E] Matrix (Fin 2) (Fin 2) E)
    (eD : TauCeti.QuadraticMap.orthogonalGroup QE ≃* DeterminantIsometries E)
    (heD : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) (X : Matrix (Fin 2) (Fin 2) E),
      (eD g).val X = ψ (g.val (ψ.symm X))) :
    ∃ E' : Subgroup (matrixProjectiveDerived Q),
      E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧
        16 ≤ Nat.card E' := by
  classical
  set T : Matrix.SpecialLinearGroup (Fin 2) E × Matrix.SpecialLinearGroup (Fin 2) E →*
      ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
      ((orthogonalOperatorCentralizer Q A.toLinearMap).subtype.comp
        (eO.symm.toMonoidHom.comp (eD.symm.toMonoidHom.comp specialRho))) with hTdef
  have hTapp : ∀ z x, T z x = ψ.symm (z.1.val * ψ x * (z.2⁻¹).val) := by
    intro z x
    change (eO.symm (eD.symm (specialRho z))).val.val x = _
    rw [heO2]
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply, ← specialRho_apply z (ψ x)]
    have h1 := heD (eD.symm (specialRho z)) (ψ x)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1.symm
  have hTO : ∀ z, T z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun z =>
    (eO.symm (eD.symm (specialRho z))).val.2
  have hTA : ∀ z x, T z (A x) = A (T z x) := fun z x => (eO.symm (eD.symm (specialRho z))).2 x
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) E) :=
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 E le_rfl (Or.inr hE2) (Or.inr hE3)).1
  have hTΩ : ∀ z, T z ∈ orthogonalOmega Q := by
    intro z
    have hz : z = (z.1, 1) * (1, z.2) := by ext <;> simp
    rw [hz, map_mul]
    exact mul_mem (map_mem_commutator_of_perfect (T.comp (MonoidHom.inl _ _)) (fun w => hTO _) _)
      (map_mem_commutator_of_perfect (T.comp (MonoidHom.inr _ _)) (fun w => hTO _) _)
  obtain ⟨φ, hφfix, hφker⟩ := exists_hom_fix Q g hd T fun z =>
    ⟨hTΩ z, mem_commutant.mpr fun x => by rw [hτ, hτ]; exact hTA z x⟩
  have hscal : ∀ a b, (∃ r : K, ∀ v, T (a, b) v = r • v) ↔
      a ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) ∧
        b ∈ center (Matrix.SpecialLinearGroup (Fin 2) E) := by
    intro a b
    constructor
    · rintro ⟨r, hr⟩
      have hX : ∀ X, a.val * X * (b⁻¹).val = (algebraMap K E r) • X := by
        intro X
        have h1 := hr (ψ.symm X)
        rw [hTapp, LinearEquiv.apply_symm_apply, ← algebraMap_smul E r] at h1
        have h3 := congrArg ψ h1
        rwa [LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply] at h3
      obtain ⟨ha, hb⟩ := center_of_mul_eq_smul hX
      exact ⟨ha, by simpa using inv_mem hb⟩
    · rintro ⟨ha, hb⟩
      obtain ⟨r, hra⟩ := eq_smul_of_mem_center ha
      obtain ⟨s, hsb⟩ := eq_smul_of_mem_center (inv_mem hb)
      have hdet : ∀ (y : Matrix.SpecialLinearGroup (Fin 2) E) (t : E), y.val = t • 1 →
          t * t = 1 := by
        intro y t hy
        have h1 := y.2
        rw [hy, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, _root_.sq] at h1
        exact h1
      have hrs : (r * s) * (r * s) = 1 := by
        rw [mul_mul_mul_comm, hdet a r hra, hdet b⁻¹ s hsb, one_mul]
      have hact : ∀ v, T (a, b) v = ψ.symm ((r * s) • ψ v) := by
        intro v
        rw [hTapp]
        change ψ.symm (a.val * ψ v * (b⁻¹).val) = _
        rw [hra, hsb, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_one, smul_smul]
      rcases mul_self_eq_one_iff.mp hrs with h | h
      · refine ⟨1, fun v => ?_⟩
        rw [hact, h, one_smul, LinearEquiv.symm_apply_apply, one_smul]
      · refine ⟨-1, fun v => ?_⟩
        rw [hact, h, neg_one_smul, map_neg, LinearEquiv.symm_apply_apply, neg_one_smul]
  obtain ⟨E', hE'φ, hE'2, hE'16⟩ := exists_elemTwo_of_pair h2E hoddE φ fun a b => by
    rw [hφker, hscal]
  refine ⟨E', hE'φ.trans ?_, hE'2, hE'16⟩
  rintro _ ⟨z, rfl⟩
  exact hφfix z

end Plus

end CFSG.ComponentClassification.HarrisLit.Hin
