module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3InvType
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Desc

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU3Lift

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.GH74.KGroups.L3Eps.Uni CFSG.GH74.Generic.S45.Uni CFSG.RankThree.PartTwo.KFacts CFSG.LinearGroups

variable {p f : ℕ} {F : Type} [Field F] {J : Type} [Group J]

@[expose] def IsLift (θ : ↥(unitarySU p f F 3) →* J) (A : GL (Fin 3) F) (ψ : F ≃+* F) (x : MulAut J) : Prop :=
  ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
    (g' : GL (Fin 3) F) = A * glAut ψ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = x (θ g)

variable {θ : ↥(unitarySU p f F 3) →* J} {A B : GL (Fin 3) F} {ψ χ : F ≃+* F} {x y : MulAut J}

theorem IsLift.mem (hl : IsLift θ A ψ x) (g : ↥(unitarySU p f F 3)) :
    A * glAut ψ (g : GL (Fin 3) F) * A⁻¹ ∈ unitarySU p f F 3 := by
  obtain ⟨g', h1, -⟩ := hl g
  rw [← h1]; exact g'.2

theorem IsLift.theta_conjHom (hl : IsLift θ A ψ x) (g : ↥(unitarySU p f F 3)) :
    θ (unitaryConjHom A ψ hl.mem g) = x (θ g) := by
  obtain ⟨g', h1, h2⟩ := hl g
  have : unitaryConjHom A ψ hl.mem g = g' := Subtype.ext (by rw [coe_unitaryConjHom, h1])
  rw [this, h2]

theorem IsLift.mul (hx : IsLift θ A ψ x) (hy : IsLift θ B χ y) :
    IsLift θ (A * glAut ψ B) (ψ * χ) (x * y) := by
  intro g
  obtain ⟨gy, h1, h2⟩ := hy g
  obtain ⟨gx, h3, h4⟩ := hx gy
  refine ⟨gx, ?_, ?_⟩
  · rw [h3, h1]
    simp only [map_mul, map_inv, MulAut.mul_apply]
    group
  · rw [h4, h2, MulAut.mul_apply]

theorem isLift_conj {R : ↥(unitarySU p f F 3)} {e : J} (hR : θ R = e) :
    IsLift θ (R : GL (Fin 3) F) 1 (MulAut.conj e) := by
  intro g
  refine ⟨R * g * R⁻¹, ?_, ?_⟩
  · simp
  · rw [map_mul, map_mul, map_inv, hR, MulAut.conj_apply]

theorem eq_smul_one_of_centralizes (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    {X : Matrix (Fin 3) (Fin 3) F}
    (hX : ∀ g : ↥(unitarySU p f F 3), X * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * X) : ∃ c : F, X = c • 1 := by
  refine eq_smul_one_of_comm_rot h h2 (le_refl 3) fun i j hij => ?_
  have hx : ∀ i : Fin 3, stdHermForm h 3 (Pi.single i 1) (Pi.single i 1) = 1 := by
    intro i
    rw [stdHermForm_single]
    simp
  have hxy : stdHermForm h 3 (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [stdHermForm_single]
    simp [hij]
  exact hX (mkSU h (pairRot h (Pi.single i 1) (Pi.single j 1))
    (unitary_of_isometry h (pairRot_isometry h (hx i) (hx j) hxy))
    (pairRot_det h (hx i) (hx j) hxy))

theorem IsLift.unique (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3))
    {M N : GL (Fin 3) F} {ω : F ≃+* F} {z : MulAut J} (hM : IsLift θ M ω z) (hN : IsLift θ N ω z) :
    ∃ c : F, (M : Matrix (Fin 3) (Fin 3) F) = c • (N : Matrix (Fin 3) (Fin 3) F) := by
  have hab : unitaryConjHom M ω hM.mem = unitaryConjHom N ω hN.mem :=
    hom_eq_of_central_ker_perfect hker _ _ fun g => by rw [hM.theta_conjHom, hN.theta_conjHom]
  have key : ∀ g' : GL (Fin 3) F, g' ∈ unitarySU p f F 3 → M * g' * M⁻¹ = N * g' * N⁻¹ := by
    intro g' hg'
    have hg : glAut ω⁻¹ g' ∈ unitarySU p f F 3 := glAut_mem_unitarySU h ω⁻¹ hg'
    have h1 := congrArg (fun F' : ↥(unitarySU p f F 3) →* ↥(unitarySU p f F 3) =>
      ((F' ⟨glAut ω⁻¹ g', hg⟩ : ↥(unitarySU p f F 3)) : GL (Fin 3) F)) hab
    simp only [coe_unitaryConjHom] at h1
    have h3 : glAut ω (glAut ω⁻¹ g') = g' := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rwa [h3] at h1
  have hcomm : ∀ g : ↥(unitarySU p f F 3),
      ((N⁻¹ * M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((N⁻¹ * M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    have e : N⁻¹ * M * (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * (N⁻¹ * M) := by
      calc N⁻¹ * M * (g : GL (Fin 3) F) = N⁻¹ * (M * g * M⁻¹) * M := by group
        _ = N⁻¹ * (N * g * N⁻¹) * M := by rw [key g g.2]
        _ = g * (N⁻¹ * M) := by group
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) e
    simpa only [Units.val_mul] using this
  obtain ⟨c, hc⟩ := eq_smul_one_of_centralizes h h2 hcomm
  refine ⟨c, ?_⟩
  have : (M : Matrix (Fin 3) (Fin 3) F) = (N : Matrix (Fin 3) (Fin 3) F) *
      ((N⁻¹ * M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [this, hc, Matrix.mul_smul, Matrix.mul_one]

theorem IsLift.comm (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    (hPerf : Group.IsPerfect ↥(unitarySU p f F 3))
    (hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3))
    (hx : IsLift θ A ψ x) (hy : IsLift θ B χ y) (hψχ : ψ * χ = χ * ψ) (hxy : x * y = y * x) :
    ∃ c : F, (A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F).map ψ =
      c • ((B : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map χ) := by
  have h1 : IsLift θ (A * glAut ψ B) (ψ * χ) (x * y) := hx.mul hy
  have h2' : IsLift θ (B * glAut χ A) (χ * ψ) (y * x) := hy.mul hx
  rw [← hψχ, ← hxy] at h2'
  obtain ⟨c, hc⟩ := IsLift.unique h h2 hPerf hker h1 h2'
  exact ⟨c, by simpa only [Units.val_mul, coe_glAut] using hc⟩

theorem exists_typeII (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ f) (hθ : IsCover h θ)
    {x : MulAut J} (hxx : x * x = 1) (hx : ∀ y : J, MulAut.conj y ≠ x) :
    ∃ (φ : F ≃+* F) (A : GL (Fin 3) F), (∀ c, φ c = h.bar c) ∧
      ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1 ∧
      IsLift θ A φ x := by
  rcases CFSG.GH74.GLS.Stage2.Signalizer.Odd87.involution_type_of_three_le h hp2 hq hθ hxx with
    ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · obtain ⟨y, hy⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact absurd hy (hx y)
  · exact ⟨φ, A, hφ, hAu, hAA, hrel⟩

theorem exists_conj_mul (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hθ : IsCover h θ) {u x : MulAut J} (huxx : (u * x) * (u * x) = 1)
    {φ φ' : F ≃+* F} {A A' : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c) (hφ' : ∀ c, φ' c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAu' : ((A' : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A' : Matrix (Fin 3) (Fin 3) F) = 1)
    (hu : IsLift θ A φ u) (hx : IsLift θ A' φ' x) : ∃ y : J, MulAut.conj y = u * x := by
  have hφφ' : φ * φ' = 1 := RingEquiv.ext fun c => by
    change φ (φ' c) = c
    rw [hφ', hφ, h.bar_bar]
  have hl : IsLift θ (A * glAut φ A') 1 (u * x) := by
    have := hu.mul hx
    rwa [hφφ'] at this
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  have hPerf : Group.IsPerfect ↥(unitarySU p f F 3) :=
    (CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)).1
  have hMu : (((A * glAut φ A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((A * glAut φ A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    (mem_unitaryIsom3 (h := h)).1 (mul_mem ((mem_unitaryIsom3 (h := h)).2 hAu)
      (glAut_mem_unitaryIsom3 φ ((mem_unitaryIsom3 (h := h)).2 hAu')))
  have hσ : ∀ z : J, (u * x) ((u * x) z) = z := fun z => by
    have := congrArg (fun φ : MulAut J => φ z) huxx
    simpa using this
  have hcomp := lift_comp_self_eq_id (G := ↥(unitarySU p f F 3)) hker (σ := (u * x : MulAut J)) hσ
    (α := unitaryConjHom (A * glAut φ A') 1 hl.mem) (fun g => hl.theta_conjHom g)
  obtain ⟨μ, hμ⟩ := scalar_of_comp h (CFSG.GH74.Generic.BProg.B2.GenLocU3Desc.two_ne_zero' h hp2) (le_refl 3)
    (φ := 1) (mul_one 1) hl.mem hcomp
  refine exists_conj_of_typeI h hθ hMu ⟨μ, hμ⟩ ?_
  intro g
  obtain ⟨g', h1, h2'⟩ := hl g
  exact ⟨g', by rw [h1, map_one, MulAut.one_apply], h2'⟩

theorem isDiag_mul' {A B : Matrix (Fin 3) (Fin 3) F} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i = k
  · subst hk; rw [hB hij, mul_zero]
  · rw [hA hk, zero_mul]

@[expose] def FrameForm (h : UnitaryFieldData p f F) (θ : ↥(unitarySU p f F 3) →* J) (C : GL (Fin 3) F)
    (x : MulAut J) : Prop :=
  ∃ (A Δ : GL (Fin 3) F) (ψ : F ≃+* F), IsLift θ A ψ x ∧ (ψ = 1 ∨ ∀ c, ψ c = h.bar c) ∧
    ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
    ((Δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag ∧ A * glAut ψ C = C * Δ

theorem frameForm_of_eq (h : UnitaryFieldData p f F) {C A : GL (Fin 3) F} {ψ : F ≃+* F}
    (hl : IsLift θ A ψ x) (hψ : ψ = 1 ∨ ∀ c, ψ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    {Dm : Matrix (Fin 3) (Fin 3) F} (hDm : Dm.IsDiag)
    (hAC : (A : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F).map ψ =
      (C : Matrix (Fin 3) (Fin 3) F) * Dm) : FrameForm h θ C x := by
  refine ⟨A, C⁻¹ * A * glAut ψ C, ψ, hl, hψ, hAu, ?_, by group⟩
  have hCinv : ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (C : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have : ((C⁻¹ * A * glAut ψ C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Dm := by
    rw [Units.val_mul, Units.val_mul, coe_glAut, Matrix.mul_assoc, hAC, ← Matrix.mul_assoc, hCinv,
      Matrix.one_mul]
  rw [this]; exact hDm

theorem scalar_eq_one_of_twisted (h : UnitaryFieldData p f F) {Am Rm : Matrix (Fin 3) (Fin 3) F} {c : F}
    (hc : Am * Rm.map h.bar = c • (Rm * Am)) (hRR : Rm * Rm = 1) (hRdet : Rm.det = 1)
    (hAdet : Am.det ≠ 0) : c = 1 := by
  have hRb : Rm.map h.bar * Rm.map h.bar = 1 := by
    rw [← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hdetRb : (Rm.map h.bar).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hRdet, map_one]
  have e1 : Am * Rm.map h.bar * Rm.map h.bar = c • (Rm * Am * Rm.map h.bar) := by
    rw [hc, Matrix.smul_mul]
  have e2 : Rm * Am * Rm.map h.bar = c • Am := by
    rw [Matrix.mul_assoc, hc, Matrix.mul_smul, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have e3 : (c * c) • Am = (1 : F) • Am := by
    rw [one_smul, ← smul_smul, ← e2, ← e1, Matrix.mul_assoc, hRb, Matrix.mul_one]
  have hA0 : Am ≠ 0 := fun h0 => hAdet (by rw [h0, Matrix.det_zero])
  have hcc : c * c = 1 := smul_left_injective F hA0 e3
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [Matrix.det_mul, hdetRb, mul_one, Matrix.det_smul, Matrix.det_mul, hRdet, one_mul,
      Fintype.card_fin] at h1
    have h2 : (1 - c ^ 3) * Am.det = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linear_combination -h3
    · exact absurd h3 hAdet
  calc c = c * (c * c) := by rw [hcc, mul_one]
    _ = c ^ 3 := by ring
    _ = 1 := hc3

end CFSG.GH74.Generic.BProg.B2.GenLocU3Lift
