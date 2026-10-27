module

import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Linear

variable (F : Type) [Field F]

theorem conjAut_mem_commutator [Finite F] (A : GL (Fin 3) F) :
    conjAut 3 F A ∈ commutator (MulAut (projectiveSL 3 F)) := by
  set H := commutator (MulAut (projectiveSL 3 F)) with hH
  set N : Subgroup (GL (Fin 3) F) := H.comap (conjAut 3 F) with hN
  have hcomm : ∀ a b : GL (Fin 3) F, ⁅a, b⁆ ∈ N := fun a b => by
    rw [hN, Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hSL : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL s ∈ N := by
    have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    set T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
      N.comap Matrix.SpecialLinearGroup.toGL with hT
    have h1 : commutator (Matrix.SpecialLinearGroup (Fin 3) F) ≤ T := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [hT, Subgroup.mem_comap, map_commutatorElement]
      exact hcomm _ _
    intro s
    have : s ∈ T := h1 (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top s)
    exact this
  have hsc : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ N := by
    intro c
    have hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have h1 : conjAut 3 F (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
      ext x
      obtain ⟨s, rfl⟩ := proj_surjective 3 F x
      rw [conjAut_proj, MulAut.one_apply]
      congr 1
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
        ← Subgroup.mem_center_iff.1 hc (Matrix.SpecialLinearGroup.toGL s)]
      group
    rw [hN, Subgroup.mem_comap, h1]
    exact Subgroup.one_mem _
  have hX : ∀ A : GL (Fin 3) F, A * Matrix.GeneralLinearGroup.inverseTranspose A⁻¹ ∈ N := by
    intro A
    obtain ⟨-, -, -, hδδ, hδc, -⟩ := standard_automorphism_transport (K := F) (n := 3)
    have hinv : (dualAut 3 F)⁻¹ = dualAut 3 F := inv_eq_of_mul_eq_one_right hδδ
    rw [hN, Subgroup.mem_comap, map_mul, ← hδc A⁻¹, map_inv]
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top (conjAut 3 F A))
      (Subgroup.mem_top (dualAut 3 F))
    rw [commutatorElement_def, hinv] at h
    rw [hH, commutator_def]
    simpa [mul_assoc] using h
  have hdet3 : ∀ c : Fˣ, Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) = c ^ 3 := fun c => by
    apply Units.ext
    simp
  have hdetX : ∀ A : GL (Fin 3) F, Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.inverseTranspose A⁻¹) = Matrix.GeneralLinearGroup.det A := by
    intro A
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.coe_inverseTranspose]
  have hmain : A ∈ N := by
    set d := Matrix.GeneralLinearGroup.det A with hd
    set B : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) d *
      (A * Matrix.GeneralLinearGroup.inverseTranspose A⁻¹)⁻¹ with hB
    have hBN : B ∈ N := N.mul_mem (hsc d) (N.inv_mem (hX A))
    have hdetAB : Matrix.GeneralLinearGroup.det (A * B⁻¹) = 1 := by
      rw [map_mul, map_inv, hB, map_mul, map_inv, map_mul, hdetX, hdet3, ← hd]
      group
    have hsl : (A * B⁻¹ : GL (Fin 3) F) ∈ StatedSL 3 F := by
      rw [mem_statedSL_iff]
      have := congrArg Units.val hdetAB
      simpa using this
    rw [statedSL_eq_range_toGL] at hsl
    obtain ⟨s, hs⟩ := hsl
    have := N.mul_mem (hSL s) hBN
    rwa [hs, inv_mul_cancel_right] at this
  exact hmain

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (hF : UnitaryFieldData p f K)

theorem scalar_mem_unitaryIsom3 {c : Kˣ} (hc : (c : K) * hF.bar (c : K) = 1) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) ∈ unitaryIsom3 hF :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm hc

theorem det_pow_succ_eq_one {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 hF) :
    Matrix.GeneralLinearGroup.det A ^ (p ^ f + 1) = 1 := by
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : hF.bar (A : Matrix (Fin 3) (Fin 3) K).det =
      ((A : Matrix (Fin 3) (Fin 3) K).map hF.bar).det := (RingHom.map_det hF.bar _)
  rw [← h2, UnitaryFieldData.bar_apply] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_succ]
  simpa using h1

theorem det_glAut (σ : K ≃+* K) (g : GL (Fin 3) K) :
    Matrix.GeneralLinearGroup.det (glAut σ g) = Units.map (σ : K →* K) (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_glAut, Units.coe_map]
  exact (RingEquiv.map_det σ _).symm

theorem psuConj_mem_commutator (hq : 2 < p ^ f) (A : unitaryIsom3 hF) :
    psuConj hF A ∈ commutator (MulAut (unitaryPSU hF 3)) := by
  have := hF.finite
  have : Fact p.Prime := ⟨hF.prime⟩
  set H := commutator (MulAut (unitaryPSU hF 3)) with hH
  set N : Subgroup (unitaryIsom3 hF) := H.comap (psuConj hF) with hN
  have hcomm : ∀ a b : unitaryIsom3 hF, ⁅a, b⁆ ∈ N := fun a b => by
    rw [hN, Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hSU : ∀ g : unitarySU p f K 3, Subgroup.inclusion unitarySU_le_unitaryIsom3 g ∈ N := by
    have hperf : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three hF hq
    set T : Subgroup (unitarySU p f K 3) :=
      N.comap (Subgroup.inclusion unitarySU_le_unitaryIsom3) with hT
    have h1 : commutator (unitarySU p f K 3) ≤ T := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [hT, Subgroup.mem_comap, map_commutatorElement]
      exact hcomm _ _
    intro g
    have : g ∈ T := h1 (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top g)
    exact this
  have hsc : ∀ (c : Kˣ) (hc : (c : K) * hF.bar (c : K) = 1),
      (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, scalar_mem_unitaryIsom3 hF hc⟩ :
        unitaryIsom3 hF) ∈ N := by
    intro c hc
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have h1 : psuConj hF ⟨_, scalar_mem_unitaryIsom3 hF hc⟩ = 1 := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [psuConj_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [coe_suConj]
        simp only [Subgroup.coe_inv]
        rw [← Subgroup.mem_center_iff.1 hcen (g : GL (Fin 3) K), mul_inv_cancel_right]
    rw [hN, Subgroup.mem_comap, h1]
    exact Subgroup.one_mem _
  obtain ⟨σ, hσ, -⟩ := CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
    p (2 * f) hF.prime (by have := hF.one_le; omega) K hF.card
  have hX : ∀ B : unitaryIsom3 hF,
      B * ⟨glAut σ (↑B⁻¹), glAut_mem_unitaryIsom3 σ (B⁻¹).2⟩ ∈ N := by
    intro B
    rw [hN, Subgroup.mem_comap, map_mul, ← psuField_mul_psuConj_mul_inv (h := hF) σ B⁻¹, map_inv]
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top (psuConj hF B))
      (Subgroup.mem_top (psuField hF σ))
    rw [hH, commutator_def]
    simpa [commutatorElement_def, mul_assoc] using h
  set dG : unitaryIsom3 hF →* Kˣ :=
    Matrix.GeneralLinearGroup.det.comp (unitaryIsom3 hF).subtype with hdG
  set u : Kˣ := dG A with hu
  have hu1 : u ^ (p ^ f + 1) = 1 := det_pow_succ_eq_one hF A.2
  have hnorm : (u : K) * hF.bar (u : K) = 1 := by
    rw [UnitaryFieldData.bar_apply]
    have := congrArg Units.val hu1
    simpa [pow_succ, mul_comm] using this
  have hmapp : ∀ w : Kˣ, Units.map (σ : K →* K) w = w ^ p := fun w => by
    apply Units.ext
    simp [hσ]
  have hdX : ∀ B : unitaryIsom3 hF,
      dG (B * ⟨glAut σ (↑B⁻¹), glAut_mem_unitaryIsom3 σ (B⁻¹).2⟩) = dG B * (dG B ^ p)⁻¹ := by
    intro B
    rw [map_mul]
    congr 1
    change Matrix.GeneralLinearGroup.det (glAut σ ((B⁻¹ : unitaryIsom3 hF) : GL (Fin 3) K)) = _
    rw [det_glAut, Subgroup.coe_inv, map_inv, hmapp]
    rfl
  have hdS : ∀ (c : Kˣ) (hc : (c : K) * hF.bar (c : K) = 1),
      dG ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, scalar_mem_unitaryIsom3 hF hc⟩ = c ^ 3 :=
    fun c hc => by
      apply Units.ext
      simp [hdG]
  have finish : ∀ B : unitaryIsom3 hF, B ∈ N → dG B = u → A ∈ N := by
    intro B hBN hB
    have hdet : dG (A * B⁻¹) = 1 := by rw [map_mul, map_inv, hB, mul_inv_cancel]
    have hmem : ((A * B⁻¹ : unitaryIsom3 hF) : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
      refine (mem_unitarySU_iff hF).2 ⟨?_, mem_unitaryIsom3.1 (A * B⁻¹).2⟩
      have := congrArg Units.val hdet
      simpa [hdG] using this
    have h1 := hSU ⟨_, hmem⟩
    have h2 : Subgroup.inclusion unitarySU_le_unitaryIsom3 ⟨_, hmem⟩ = A * B⁻¹ := rfl
    rw [h2] at h1
    have := N.mul_mem h1 hBN
    rwa [inv_mul_cancel_right] at this
  by_cases hp3 : p % 3 = 1
  ·
    have hq3 : p ^ f % 3 = 1 := by rw [Nat.pow_mod, hp3]; simp
    set S : unitaryIsom3 hF :=
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_unitaryIsom3 hF hnorm⟩ with hS
    apply finish (S ^ ((p ^ f + 2) / 3)) (N.pow_mem (hsc u hnorm) _)
    rw [map_pow, hS, hdS u hnorm, ← pow_mul]
    have : 3 * ((p ^ f + 2) / 3) = (p ^ f + 1) + 1 := by omega
    rw [this, pow_succ, hu1, one_mul]
  ·
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, (1 - (p : ℤ)) * x + 3 * y = 1 := by
      have : p % 3 = 0 ∨ p % 3 = 2 := by omega
      rcases this with h | h
      · exact ⟨1, (p / 3 : ℕ), by omega⟩
      · exact ⟨-1, -(p / 3 : ℕ), by omega⟩
    set S : unitaryIsom3 hF :=
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_unitaryIsom3 hF hnorm⟩ with hS
    set X : unitaryIsom3 hF := A * ⟨glAut σ (↑A⁻¹), glAut_mem_unitaryIsom3 σ (A⁻¹).2⟩ with hXdef
    apply finish (X ^ x * S ^ y) (N.mul_mem (N.zpow_mem (hX A) x) (N.zpow_mem (hsc u hnorm) y))
    rw [map_mul, map_zpow, map_zpow, hXdef, hdX, hS, hdS u hnorm, ← hu]
    have e1 : u * (u ^ p)⁻¹ = u ^ (1 - (p : ℤ)) := by
      rw [zpow_sub, zpow_one, zpow_natCast]
    rw [e1, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    have : (1 - (p : ℤ)) * x + ((3 : ℕ) : ℤ) * y = 1 := by push_cast; exact hxy
    rw [this, zpow_one]

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator
