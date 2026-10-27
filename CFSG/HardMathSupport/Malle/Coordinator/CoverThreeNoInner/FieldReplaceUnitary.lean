module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitaryYLevel
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.CoverIsoSU
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldReplace
public import CFSG.HardMathSupport.Malle.Proving.CoverThreeField

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField suConj suField coe_suConj coe_suField
  psuConj_mk psuField_mk conj_mk_eq_psuConj unitaryIsom3 mem_unitaryIsom3 unitarySU_le_unitaryIsom3 psuField_mul_psuConj_mul_inv eq_one_of_psuConj_mul_psuField_eq_one unitary_order_three_field_descent stdPinnedPSU3_stable)
open CFSG.HardMathSupport.Foote.ModuleExclusions (diagGL coe_diagGL dvec Dsl toGL_Dsl Dsl_pow
  SplitDataU false_of_split_unitary_field_cube)

theorem exists_su3_equiv_of_cover
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h9 : 9 ∣ ℓ ^ f + 1)
    (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ ψ : unitarySU ℓ f F 3 ≃* K, ∀ g, e (QuotientGroup.mk (ψ g)) = unitaryProj h 3 g := by
  have := h.finite
  set e₁ := unitaryPSUEquiv h (n := 3) (by norm_num) with he₁
  set ρ :=
    e₁.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) with hρ
  have hρs : Function.Surjective ρ :=
    e₁.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    simp only [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h5 : 5 ≤ ℓ ^ f := by
    have := Nat.le_of_dvd (by positivity) h9
    omega
  obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_mulEquiv_su3_of_cover_compat
    hGA h.prime h5 h.card_eq_sq h9 ρ hρs hρk hz
  refine ⟨ψ, fun g => e₁.injective ?_⟩
  rw [unitaryPSUEquiv_unitaryProj]
  exact hψ g

section Action

variable {Y : Type*} [Group Y] {K : Subgroup Y} [hKn : K.Normal] {ℓ f : ℕ} {F : Type} [Field F]
  {h : UnitaryFieldData ℓ f F}

@[expose] noncomputable def suAct (ψ : unitarySU ℓ f F 3 ≃* K) (y : Y) :
    unitarySU ℓ f F 3 →* unitarySU ℓ f F 3 :=
  ψ.symm.toMonoidHom.comp ((MulAut.conjNormal y : MulAut K).toMonoidHom.comp ψ.toMonoidHom)

theorem coe_psi_suAct (ψ : unitarySU ℓ f F 3 ≃* K) (y : Y) (g : unitarySU ℓ f F 3) :
    ((ψ (suAct ψ y g) : K) : Y) = y * (ψ g : Y) * y⁻¹ := by
  simp [suAct, MulAut.conjNormal_apply]

theorem proj_suAct (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3) (ψ : unitarySU ℓ f F 3 ≃* K)
    (hψ : ∀ g, e (QuotientGroup.mk (ψ g)) = unitaryProj h 3 g) (y : Y)
    (g : unitarySU ℓ f F 3) :
    unitaryProj h 3 (suAct ψ y g) = modelAct K e y (unitaryProj h 3 g) := by
  have h2 : ψ (suAct ψ y g) = ⟨y * ψ g * y⁻¹, hKn.conj_mem _ (ψ g).2 y⟩ :=
    Subtype.ext (coe_psi_suAct ψ y g)
  rw [← hψ, h2, ← hψ g, modelAct_apply_mk]

@[expose] noncomputable def suTwist (h : UnitaryFieldData ℓ f F) (H : unitaryIsom3 h)
    (σ : F ≃+* F) : MulAut (unitarySU ℓ f F 3) :=
  suConj h H * suField h σ * (suConj h H)⁻¹

theorem proj_suTwist (H : unitaryIsom3 h) (σ : F ≃+* F) (g : unitarySU ℓ f F 3) :
    unitaryProj h 3 (suTwist h H σ g) =
      (psuConj h H * psuField h σ * (psuConj h H)⁻¹) (unitaryProj h 3 g) := by
  set g' := (suConj h H)⁻¹ g with hg'
  have hg : g = suConj h H g' := by rw [hg', MulAut.apply_inv_self]
  have hp : unitaryProj h 3 g = psuConj h H (unitaryProj h 3 g') := by
    conv_lhs => rw [hg]
    rfl
  have hp' : (psuConj h H)⁻¹ (unitaryProj h 3 g) = unitaryProj h 3 g' := by
    rw [hp, MulAut.inv_apply_self]
  rw [MulAut.mul_apply, MulAut.mul_apply, hp']
  rfl

theorem suAct_eq_suTwist [Group.IsPerfect (unitarySU ℓ f F 3)]
    (e : K ⧸ Subgroup.center K ≃* unitaryPSU h 3) (ψ : unitarySU ℓ f F 3 ≃* K)
    (hψ : ∀ g, e (QuotientGroup.mk (ψ g)) = unitaryProj h 3 g) {y : Y} {H : unitaryIsom3 h}
    {σ : F ≃+* F}
    (hy : modelAct K e y = psuConj h H * psuField h σ * (psuConj h H)⁻¹)
    (g : unitarySU ℓ f F 3) : suAct ψ y g = suTwist h H σ g := by
  set hh : unitarySU ℓ f F 3 →* unitarySU ℓ f F 3 :=
    ((suTwist h H σ)⁻¹ : MulAut (unitarySU ℓ f F 3)).toMonoidHom.comp (suAct ψ y) with hhh
  have hproj : ∀ x, unitaryProj h 3 (hh x) = unitaryProj h 3 x := by
    intro x
    have h1 := proj_suTwist H σ ((suTwist h H σ)⁻¹ (suAct ψ y x))
    rw [MulAut.apply_inv_self, proj_suAct e ψ hψ, hy] at h1
    change unitaryProj h 3 ((suTwist h H σ)⁻¹ (suAct ψ y x)) = _
    have h2 := congrArg (fun a => (psuConj h H * psuField h σ * (psuConj h H)⁻¹)⁻¹ a) h1
    simp only [MulAut.inv_apply_self] at h2
    exact h2.symm
  have hc : ∀ x : unitarySU ℓ f F 3, x⁻¹ * hh x ∈ Subgroup.center (unitarySU ℓ f F 3) := by
    intro x
    refine unitaryScalars_le_center h 3 ?_
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hproj x, inv_mul_cancel]
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    hh hc
  have hg : (suTwist h H σ)⁻¹ (suAct ψ y g) = g := by
    have := congrArg (fun f : unitarySU ℓ f F 3 →* unitarySU ℓ f F 3 => f g) hid
    exact this
  have h2 := congrArg (suTwist h H σ) hg
  rwa [MulAut.apply_inv_self] at h2

end Action

section Diag

variable {ℓ f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem norm_eq_one_of_pow_three_eq_one (h : UnitaryFieldData ℓ f F) (h3 : 3 ∣ ℓ ^ f + 1)
    {ω : F} (hω : ω ^ 3 = 1) : h.norm ω = 1 := by
  obtain ⟨k, hk⟩ := h3
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', hk, pow_mul, hω, one_pow]

end Diag

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem coverThreeNoInnerFieldUnitary_holds
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    CoverThreeNoInnerFieldUnitary := by
  intro Y _ _ Rb Y₀ hRN K _ hK hC _ hZ3 ℓ f F _ h hq h3 h8 e E hER hEN hEa hEc hEKC hout
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.finite
  set φ := modelAct K e with hφ
  obtain ⟨y, hyE, hyout⟩ : ∃ y ∈ E, φ y ∉ (psuConj h).range := by
    by_contra hcon
    push Not at hcon
    exact hout (by rintro _ ⟨y, hy, rfl⟩; exact hcon y hy)
  have hy3 : y ^ 3 = 1 := hEa.2 y hyE
  have hφy3 : φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq (φ y) hφy3 hyout
  have h9 : 9 ∣ ℓ ^ f + 1 := nine_dvd_add_one_of_orderOf_three h hσ h3
  have hF9 : 9 ∣ Nat.card F - 1 := by
    have hc : Nat.card F = (ℓ ^ f) ^ 2 := h.card_eq_sq
    obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by have := Nat.one_le_pow f ℓ h.prime.pos; omega⟩
    have hsub : Nat.card F - 1 = (ℓ ^ f + 1) * m := by
      rw [hc, hm]
      have : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
      omega
    rw [hsub]
    exact Dvd.dvd.mul_right h9 m
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hz3 : 3 ∣ Nat.card (Subgroup.center K) := by
    have hpos : Nat.card (Subgroup.center K) ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hpos).2 (by rw [hZ3])
  obtain ⟨ψ, hψ'⟩ := exists_su3_equiv_of_cover hGA h h9 e hz3
  have : Group.IsPerfect (unitarySU ℓ f F 3) :=
    Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  have hact := fun g => suAct_eq_suTwist e ψ hψ' (y := y) hH g
  obtain ⟨ζ, hζ⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_primitiveRoot_nine
    (F := F) hF9
  have hω : IsPrimitiveRoot (ζ ^ 3) 3 := by
    simpa using hζ.pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : 3 ∣ 9)
  have hω0 : ζ ^ 3 ≠ 0 := hω.ne_zero (by norm_num)
  set ωu : Fˣ := Units.mk0 (ζ ^ 3) hω0 with hωu
  have hωu3 : ωu ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hωu, Units.val_mk0, Units.val_one]
    exact hω.pow_eq_one
  have hωu1 : ωu ≠ 1 := by
    intro h1
    apply hω.ne_one (by norm_num)
    have := congrArg Units.val h1
    rwa [hωu, Units.val_mk0, Units.val_one] at this
  have hσω : σ (ζ ^ 3) = ζ ^ 3 := apply_eq_of_pow_three_eq_one hσ hω.pow_eq_one
  have hσωu : σ (ωu : F) = ωu := by rw [hωu, Units.val_mk0, hσω]
  have hσωi : σ ((ωu⁻¹ : Fˣ) : F) = ((ωu⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσωu]
  have hnorm : ∀ u : Fˣ, u ^ 3 = 1 → h.norm (u : F) = 1 := by
    intro u hu
    refine norm_eq_one_of_pow_three_eq_one h h3 ?_
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  set d0 : Fin 3 → Fˣ := dvec 1 0 ωu with hd0
  have hd0n : ∀ i, h.norm (d0 i : F) = 1 := by
    intro i
    apply hnorm
    rw [hd0]
    unfold dvec
    split_ifs
    · exact hωu3
    · exact one_pow 3
    · rw [inv_pow, hωu3, inv_one]
  have hσd0 : ∀ i, σ (d0 i : F) = (d0 i : F) := by
    intro i
    rw [hd0]
    unfold dvec
    split_ifs
    · exact hσωu
    · exact map_one σ
    · exact hσωi
  have hdiag : diagGL d0 ∈ unitaryIsom3 (h := h) :=
    CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL_mem_unitaryIsom3 d0 fun c => by
      rw [mul_comm]; exact hd0n c
  have hdet : ((diagGL d0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [coe_diagGL, Matrix.det_diagonal]
    exact CFSG.HardMathSupport.Foote.ModuleExclusions.prod_dvec (by norm_num) ωu
  set Δ : unitaryIsom3 h := ⟨diagGL d0, hdiag⟩ with hΔ
  set D₀ : unitarySU ℓ f F 3 := ⟨diagGL d0, (mem_unitarySU_iff h).mpr ⟨hdet, hdiag⟩⟩ with hD₀
  set D : unitarySU ℓ f F 3 := suConj h H D₀ with hD
  set Z : unitarySU ℓ f F 3 :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ωu,
      scalar_mem_unitarySU h (by norm_num) (hnorm ωu hωu3) hωu3⟩ with hZ
  set z : Y := ((ψ Z : K) : Y) with hz
  set d : Y := ((ψ D : K) : Y) with hd
  have hfD₀ : suField h σ D₀ = D₀ := by
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut, hD₀]
    change ((diagGL d0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ = _
    rw [coe_diagGL, Matrix.diagonal_map (map_zero σ)]
    simp only [hσd0]
  have hfZ : suField h σ Z = Z := by
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut, hZ]
    change ((Matrix.GeneralLinearGroup.scalar (Fin 3) ωu : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).map σ = _
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
    simp only [hσωu]
  have hcZ : ∀ C : unitaryIsom3 h, suConj h C Z = Z := by
    intro C
    apply Subtype.ext
    rw [coe_suConj, hZ]
    change (C : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) ωu *
      (C : GL (Fin 3) F)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ωu
    have hcomm : (C : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) ωu =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ωu * (C : GL (Fin 3) F) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute (ωu : F) (fun r' => Commute.all _ r')
        (C : GL (Fin 3) F).1).symm.eq
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hTD : suTwist h H σ D = D := by
    simp only [suTwist, MulAut.mul_apply, hD, MulAut.inv_apply_self, hfD₀]
  have hTZ : suTwist h H σ Z = Z := by
    have hinv : (suConj h H)⁻¹ Z = Z := by
      rw [← map_inv]
      exact hcZ H⁻¹
    simp only [suTwist, MulAut.mul_apply, hinv, hfZ, hcZ H]
  have hdy : d * y = y * d := by
    have h1 := coe_psi_suAct ψ y D
    rw [hact D, hTD] at h1
    rw [hd]
    nth_rewrite 1 [h1]
    group
  have hzy : z * y = y * z := by
    have h1 := coe_psi_suAct ψ y Z
    rw [hact Z, hTZ] at h1
    rw [hz]
    nth_rewrite 1 [h1]
    group
  have hZsc : Z ∈ unitaryScalars h 3 := ⟨ωu, hnorm ωu hωu3, hωu3, rfl⟩
  have hZc : Z ∈ Subgroup.center (unitarySU ℓ f F 3) := unitaryScalars_le_center h 3 hZsc
  have hzd : z * d = d * z := by
    have h1 : Z * D = D * Z := (Subgroup.mem_center_iff.1 hZc D).symm
    have h2 := congrArg (fun g => ((ψ g : K) : Y)) h1
    simpa [hz, hd] using h2
  have hZ3' : Z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hZ]
    change (Matrix.GeneralLinearGroup.scalar (Fin 3) ωu) ^ 3 = 1
    rw [← map_pow, hωu3, map_one]
  have hz3' : z ^ 3 = 1 := by
    rw [hz, ← Subgroup.coe_pow, ← map_pow, hZ3', map_one, Subgroup.coe_one]
  have hΔ3 : Δ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hΔ]
    change (diagGL d0) ^ 3 = 1
    rw [hd0, ← toGL_Dsl (F := F) (i := 1) (j := 0) (by norm_num), ← map_pow,
      Dsl_pow _ ωu 3 hωu3, map_one]
  have hD₀3 : D₀ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hD₀]
    change (diagGL d0) ^ 3 = 1
    rw [hd0, ← toGL_Dsl (F := F) (i := 1) (j := 0) (by norm_num), ← map_pow,
      Dsl_pow _ ωu 3 hωu3, map_one]
  have hd3' : d ^ 3 = 1 := by
    have : D ^ 3 = 1 := by rw [hD, ← map_pow, hD₀3, map_one]
    rw [hd, ← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hφψ : ∀ g : unitarySU ℓ f F 3,
      φ ((ψ g : K) : Y) = MulAut.conj (unitaryProj h 3 g) := by
    intro g
    rw [hφ, modelAct_coe K e (ψ g), hψ' g]
  have hφz : φ z = 1 := by
    have : unitaryProj h 3 Z = 1 := by
      rw [← MonoidHom.mem_ker, ker_unitaryProj]
      exact hZsc
    rw [hz, hφψ, this, map_one]
  set cD : MulAut (unitaryPSU h 3) := psuConj h Δ with hcD
  have hφd : φ d = psuConj h H * cD * (psuConj h H)⁻¹ := by
    rw [hd, hφψ, hD]
    have h1 : unitaryProj h 3 (suConj h H D₀) = psuConj h H (unitaryProj h 3 D₀) := rfl
    have h2 : MulAut.conj (unitaryProj h 3 D₀) = cD := by
      rw [hcD]
      exact conj_mk_eq_psuConj D₀
    rw [h1, ← h2]
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hcD1 : cD ≠ 1 := by
    intro h1
    have h2 : psuConj h Δ * psuField h (1 : F ≃+* F) = 1 := by rw [map_one, mul_one]; exact h1
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one Δ 1 h2
    have h00 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 0) hc
    have h11 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 1 1) hc
    simp [hΔ, coe_diagGL, hd0, dvec] at h00 h11
    apply hωu1
    apply Units.ext
    rw [Units.val_one, h11, ← h00]
  have hcD3 : cD ^ 3 = 1 := by rw [hcD, ← map_pow, hΔ3, map_one]
  have hφd1 : φ d ≠ 1 := by
    rw [hφd]
    intro h1
    apply hcD1
    have : cD = (psuConj h H)⁻¹ * (psuConj h H * cD * (psuConj h H)⁻¹) * psuConj h H := by
      group
    rw [this, h1]
    group
  have hφdL : φ d ∈ (psuConj h).range := by
    rw [hφd]
    exact mul_mem (mul_mem ⟨H, rfl⟩ ⟨Δ, rfl⟩) (inv_mem ⟨H, rfl⟩)
  have hz1 : z ≠ 1 := by
    intro h1
    apply hωu1
    have hZ1 : Z = 1 := by
      apply ψ.injective
      rw [map_one]
      exact Subtype.ext (by rw [← hz, h1]; rfl)
    have := congrArg (fun M : unitarySU ℓ f F 3 => ((M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0)
      hZ1
    simp [hZ] at this
    exact this
  have hd1 : d ≠ 1 := fun h1 => hφd1 (by rw [h1, map_one])
  have hy1 : y ≠ 1 := fun h1 => hyout (by rw [h1, map_one]; exact one_mem _)
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3' hz1
  have hod : orderOf d = 3 := orderOf_eq_prime hd3' hd1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  set E₁ : Subgroup Y :=
    (Subgroup.zpowers z ⊔ Subgroup.zpowers d) ⊔ Subgroup.zpowers y with hE₁
  have hE₁a : IsElemAbelian 3 E₁ :=
    isElemAbelian_sup_zpowers hzd hzy hdy hz3' hd3' hy3
  have hzdL : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ (psuConj h).range.comap φ := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · change φ z ∈ (psuConj h).range
      rw [hφz]
      exact one_mem _
    · exact hφdL
  have hdisj₁ : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hφx : φ (d ^ k) = 1 := by rw [← hm, map_zpow, hφz, _root_.one_zpow]
    rw [map_zpow] at hφx
    have hoφd : orderOf (φ d) = 3 := orderOf_eq_prime (by rw [← map_pow, hd3', map_one]) hφd1
    have h3k : ((orderOf (φ d) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hφx
    rw [hoφd] at h3k
    exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hod]; exact_mod_cast h3k)
  have hdisj₂ : Disjoint (Subgroup.zpowers z ⊔ Subgroup.zpowers d) (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro x hxzd hxy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxy
    by_cases h3k : (3 : ℤ) ∣ k
    · exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hoy]; exact_mod_cast h3k)
    · exfalso
      apply hyout
      have hk : φ y ^ k ∈ (psuConj h).range := by
        rw [← map_zpow]
        exact hzdL hxzd
      exact mem_of_zpow_mem_of_pow_three hφy3 h3k hk
  have hcomm₁ : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers d, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hzd i j)
  have hcomm₂ : ∀ a ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers d, ∀ b ∈ Subgroup.zpowers y,
      Commute a b := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer {y} := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzy
      · exact Subgroup.mem_centralizer_singleton_iff.2 hdy
    have hay : Commute a y := Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
    exact hay.zpow_right j
  have hE₁c : Nat.card E₁ = 3 ^ 3 := by
    rw [hE₁, card_sup_of_commute_disjoint _ _ hcomm₂ hdisj₂,
      card_sup_of_commute_disjoint _ _ hcomm₁ hdisj₁, Nat.card_zpowers, Nat.card_zpowers,
      Nat.card_zpowers, hoz, hod, hoy]
    norm_num
  have hyE₁ : y ∈ E₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hE₁N : E₁ ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
    have hKN : K ≤ (K ⊔ (Rb : Subgroup Y)).normalCore :=
      Subgroup.normal_le_normalCore.2 le_sup_left
    refine sup_le (sup_le (Subgroup.zpowers_le.2 (hKN (ψ Z).2))
      (Subgroup.zpowers_le.2 (hKN (ψ D).2))) (Subgroup.zpowers_le.2 (hEN hyE))
  obtain ⟨l, hl⟩ := exists_conj_le_sylow Rb hE₁a.2
  set E' : Subgroup Y := E₁.map (MulAut.conj l).toMonoidHom with hE'
  have hE'a : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE₁a _
  have hE'c : Nat.card E' = 3 ^ 3 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj l).injective, hE₁c]
  have hE'N : E' ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.normalCore_normal _).conj_mem a (hE₁N ha) l
  have hKCL : K ⊔ Subgroup.centralizer (K : Set Y) ≤ (psuConj h).range.comap φ := by
    refine sup_le (fun k hk => ?_) (fun c hc => ?_)
    · change φ k ∈ (psuConj h).range
      have : φ k = MulAut.conj (e (QuotientGroup.mk (⟨k, hk⟩ : K))) := modelAct_coe K e ⟨k, hk⟩
      rw [this]
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk (⟨k, hk⟩ : K)))
      rw [← hg, conj_mk_eq_psuConj]
      exact ⟨_, rfl⟩
    · change φ c ∈ (psuConj h).range
      have hck : c ∈ φ.ker := by rw [hφ, modelAct_ker hK e]; exact hc
      rw [MonoidHom.mem_ker.1 hck]
      exact one_mem _
  have hLn : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq).normal
  have hE'KC : ¬ E' ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    intro hle
    apply hyout
    have h1 : l * y * l⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set Y) := hle ⟨y, hyE₁, rfl⟩
    have h2 : φ l * φ y * (φ l)⁻¹ ∈ (psuConj h).range := by
      have := hKCL h1
      rwa [Subgroup.mem_comap, map_mul, map_mul, map_inv] at this
    have h3' := hLn.conj_mem _ h2 (φ l)⁻¹
    have he : (φ l)⁻¹ * (φ l * φ y * (φ l)⁻¹) * (φ l)⁻¹⁻¹ = φ y := by group
    rwa [he] at h3'
  set Θ : Y →* MulAut (unitaryPSU h 3) :=
    (MulAut.conj (psuConj h H)⁻¹).toMonoidHom.comp φ with hΘ
  set α : MulAut (unitaryPSU h 3) := (φ l * psuConj h H)⁻¹ with hα
  have hmap : (E'.map φ).map (MulAut.conj α).toMonoidHom = E₁.map Θ := by
    rw [hE', Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    change (MulAut.conj α) (φ ((MulAut.conj l) x)) = (MulAut.conj (psuConj h H)⁻¹) (φ x)
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hα]
    group
  have hΘz : Θ z = 1 := by
    simp only [hΘ, MonoidHom.comp_apply, hφz, map_one]
  have hΘd : Θ d = cD := by
    simp only [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφd, MulAut.conj_apply]
    group
  have hΘy : Θ y = psuField h σ := by
    simp only [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hH, MulAut.conj_apply]
    group
  have hE₁Θ : E₁.map Θ = (Subgroup.zpowers (1 : MulAut (unitaryPSU h 3)) ⊔
      Subgroup.zpowers cD) ⊔ Subgroup.zpowers (psuField h σ) := by
    rw [hE₁, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, hΘz, hΘd, hΘy]
  have hglΔ : (⟨glAut σ (Δ : GL (Fin 3) F),
      CFSG.RankThree.PartTwo.KFacts.glAut_mem_unitaryIsom3 σ Δ.2⟩ : unitaryIsom3 h) = Δ := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_glAut]
    change ((diagGL d0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ = _
    rw [coe_diagGL, Matrix.diagonal_map (map_zero σ)]
    simp only [hσd0]
  have hfc : Commute (psuField h σ) cD := by
    have h1 := psuField_mul_psuConj_mul_inv σ Δ
    rw [hglΔ] at h1
    change psuField h σ * cD = cD * psuField h σ
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hf3 : psuField h σ ^ 3 = 1 := by
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    rw [← map_pow, hσ3, map_one]
  set A' : Subgroup (MulAut (unitaryPSU h 3)) := Subgroup.zpowers cD with hA'
  have hA'f : ∀ a ∈ A', ∀ k : ℕ, Commute a (psuField h σ ^ k) := by
    intro a ha k
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (hfc.symm.zpow_left i).pow_right k
  let S : Subgroup (MulAut (unitaryPSU h 3)) :=
    { carrier := {b | ∃ k : ℕ, ∃ a ∈ A', b = psuField h σ ^ k * a}
      mul_mem' := by
        rintro _ _ ⟨k, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
        refine ⟨k + m, a * b, A'.mul_mem ha hb, ?_⟩
        rw [pow_add, mul_assoc, ← mul_assoc a, (hA'f a ha m).eq]
        group
      one_mem' := ⟨0, 1, A'.one_mem, by rw [pow_zero, mul_one]⟩
      inv_mem' := by
        rintro _ ⟨k, a, ha, rfl⟩
        refine ⟨2 * k, a⁻¹, A'.inv_mem ha, ?_⟩
        have hk : (psuField h σ ^ k)⁻¹ = psuField h σ ^ (2 * k) := by
          rw [inv_eq_of_mul_eq_one_right]
          rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hf3, one_pow]
        rw [_root_.mul_inv_rev, ← hk, ((hA'f a ha k).inv_left).inv_right.eq] }
  have hsplit : SplitDataU h σ A' (E₁.map Θ) := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hcD3, _root_.one_zpow]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hcoe : diagGL (d0 ^ i) = ((Δ ^ i : unitaryIsom3 h) : GL (Fin 3) F) := by
        rw [Subgroup.coe_zpow]
        exact (map_zpow (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagHom F) d0 i)
      have hd : diagGL (d0 ^ i) ∈ unitaryIsom3 h := hcoe ▸ (Δ ^ i).2
      refine ⟨d0 ^ i, hd, ?_⟩
      rw [hcD, ← map_zpow]
      congr 1
      exact Subtype.ext hcoe.symm
    · have hle : E₁.map Θ ≤ S := by
        rw [hE₁Θ]
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [Subgroup.zpowers_one_eq_bot]
          exact bot_le
        · rw [Subgroup.zpowers_le]
          exact ⟨0, cD, Subgroup.mem_zpowers cD, by rw [pow_zero, one_mul]⟩
        · rw [Subgroup.zpowers_le]
          exact ⟨1, 1, A'.one_mem, by rw [pow_one, mul_one]⟩
      exact hle hb
  exact false_of_split_unitary_field_cube hRN hK hl hE'N hE'a hE'c hE'KC h h3 h8 e
    ⟨α, σ, A', hσ, hmap ▸ hsplit⟩

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
