module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Fix
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUClassify
public import CFSG.GH74.GLS.Stage4.T2F1LocH90
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three (liftGL exists_liftGL mapσ mapσ_scalar
  mapσ_cube coe_liftGL liftGL_injective)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (scal sc mem_sc_iff scal_mem_sc)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU
  (scal_mem_unitaryIsom3_iff invol_apply)

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F}
  (h₀ : UnitaryFieldData ℓ (f / 3) (fixF σ))
  (hbar : ∀ c : fixF σ, (h₀.bar c : F) = h.bar c)

@[expose] noncomputable def liftU : unitaryIsom3 h₀ →* unitaryIsom3 h :=
  ((liftGL σ).comp (unitaryIsom3 h₀).subtype).codRestrict (unitaryIsom3 h)
    fun M => (liftGL_mem_unitaryIsom3_iff h h₀ hbar M).2 M.2

theorem coe_liftU (M : unitaryIsom3 h₀) :
    ((liftU h h₀ hbar M : unitaryIsom3 h) : GL (Fin 3) F) = liftGL σ (M : GL (Fin 3) (fixF σ)) :=
  rfl

@[expose] noncomputable def phi : unitaryIsom3 h₀ →* MulAut (unitaryPSU h 3) :=
  (psuConj h).comp (liftU h h₀ hbar)

theorem phi_apply (M : unitaryIsom3 h₀) : phi h h₀ hbar M = psuConj h (liftU h h₀ hbar M) := rfl

theorem glAut_eq_mapσ (g : GL (Fin 3) F) : glAut σ g = mapσ σ g := Units.ext rfl

theorem glAut_liftGL [Finite F] (M : GL (Fin 3) (fixF σ)) : glAut σ (liftGL σ M) = liftGL σ M := by
  rw [glAut_eq_mapσ]
  exact CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.mapσ_liftGL σ M

theorem phi_commute (M : unitaryIsom3 h₀) :
    psuField h σ * phi h h₀ hbar M = phi h h₀ hbar M * psuField h σ := by
  have := h.finite
  have h1 := psuField_mul_psuConj_mul_inv σ (liftU h h₀ hbar M)
  have h2 : (⟨glAut σ ((liftU h h₀ hbar M : unitaryIsom3 h) : GL (Fin 3) F),
      glAut_mem_unitaryIsom3 σ (liftU h h₀ hbar M).2⟩ : unitaryIsom3 h) = liftU h h₀ hbar M :=
    Subtype.ext (glAut_liftGL _)
  rw [h2] at h1
  rw [phi_apply]
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem liftGL_scal (c : (fixF σ)ˣ) :
    liftGL σ (scal c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (fixF σ).subtype.toMonoidHom c) := by
  apply Units.ext
  ext i j
  simp [liftGL, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, scal]
  split_ifs <;> rfl

include hbar in
theorem phi_eq_one_iff (M : unitaryIsom3 h₀) :
    phi h h₀ hbar M = 1 ↔ (M : GL (Fin 3) (fixF σ)) ∈ sc (fixF σ) := by
  have := h.finite
  constructor
  · intro h1
    obtain ⟨c, hc⟩ :=
      CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.exists_scalar_of_psuConj_eq_one
        (h := h) (A := liftU h h₀ hbar M) h1
    have hc' : liftGL σ (M : GL (Fin 3) (fixF σ)) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hc
    have h00 : ((((M : GL (Fin 3) (fixF σ)) : Matrix (Fin 3) (Fin 3) (fixF σ)) 0 0 : fixF σ) : F) =
        (c : F) := by
      have := congrArg (fun K : GL (Fin 3) F => (K : Matrix (Fin 3) (Fin 3) F) 0 0) hc'
      change ((((M : GL (Fin 3) (fixF σ)) : Matrix (Fin 3) (Fin 3) (fixF σ)) 0 0 : fixF σ) : F) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 0 at this
      simpa [Matrix.GeneralLinearGroup.scalar] using this
    have hne : ((M : GL (Fin 3) (fixF σ)) : Matrix (Fin 3) (Fin 3) (fixF σ)) 0 0 ≠ 0 := by
      intro h0
      apply c.ne_zero
      rw [← h00, h0]
      rfl
    refine mem_sc_iff.2 ⟨Units.mk0 _ hne, liftGL_injective σ ?_⟩
    rw [liftGL_scal, hc']
    congr 1
    apply Units.ext
    simpa using h00.symm
  · intro hM
    obtain ⟨c, hc⟩ := mem_sc_iff.1 hM
    rw [phi_apply]
    refine psuConj_eq_one_of_coe_eq_scalar (c := Units.map (fixF σ).subtype.toMonoidHom c) ?_
    rw [coe_liftU, hc, liftGL_scal]

include hbar in
theorem exists_phi_eq_of_commute (hσ : orderOf σ = 3) {a : MulAut (unitaryPSU h 3)}
    (ha : a ∈ (psuConj h).range) (hc : psuField h σ * a = a * psuField h σ) :
    ∃ M : unitaryIsom3 h₀, phi h h₀ hbar M = a := by
  have hfin := h.finite
  obtain ⟨A₀, rfl⟩ := ha
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have h1 := psuField_mul_psuConj_mul_inv σ A₀
  have h2 : psuConj h ⟨glAut σ (A₀ : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ A₀.2⟩ =
      psuConj h A₀ := by
    rw [← h1, hc]
    group
  set A₁ : unitaryIsom3 h :=
    ⟨glAut σ (A₀ : GL (Fin 3) F), glAut_mem_unitaryIsom3 σ A₀.2⟩ * A₀⁻¹ with hA₁
  have h3 : psuConj h A₁ = 1 := by rw [hA₁, map_mul, map_inv, h2, mul_inv_cancel]
  obtain ⟨u, hu⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.exists_scalar_of_psuConj_eq_one h3
  have hσA : mapσ σ (A₀ : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A₀ : GL (Fin 3) F) := by
    have e : ((A₁ : unitaryIsom3 h) : GL (Fin 3) F) =
        glAut σ (A₀ : GL (Fin 3) F) * (A₀ : GL (Fin 3) F)⁻¹ := rfl
    rw [e] at hu
    rw [← glAut_eq_mapσ]
    exact mul_inv_eq_iff_eq_mul.1 hu
  have hu1 : h.bar (u : F) * u = 1 := by
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ unitaryIsom3 h := by
      rw [← hu]; exact A₁.2
    have := (scal_mem_unitaryIsom3_iff h).1 hmem
    rwa [invol_apply h] at this
  have hN : (u : F) * σ u * σ (σ u) = 1 := by
    have e1 : mapσ σ (mapσ σ (A₀ : GL (Fin 3) F)) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : F →* F) u) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A₀ : GL (Fin 3) F)) := by
      rw [hσA, map_mul, mapσ_scalar, hσA]
    have e2 : mapσ σ (mapσ σ (mapσ σ (A₀ : GL (Fin 3) F))) =
        Matrix.GeneralLinearGroup.scalar (Fin 3)
          (Units.map (σ : F →* F) (Units.map (σ : F →* F) u) * Units.map (σ : F →* F) u * u) *
            (A₀ : GL (Fin 3) F) := by
      rw [e1, map_mul, mapσ_scalar, map_mul, mapσ_scalar, hσA, map_mul, map_mul]
      simp only [mul_assoc]
    have h1' := mapσ_cube σ hσ3 (A₀ : GL (Fin 3) F)
    rw [e2] at h1'
    have h3' : Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (σ : F →* F) (Units.map (σ : F →* F) u) * Units.map (σ : F →* F) u * u) = 1 := by
      have := congrArg (· * (A₀ : GL (Fin 3) F)⁻¹) h1'
      simpa using this
    have h4 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 0) h3'
    simp [Matrix.GeneralLinearGroup.scalar] at h4
    linear_combination h4
  have hprod : ∏ i ∈ Finset.range 3, (σ ^ i) (u : F) = 1 := by
    simpa [Finset.prod_range_succ, pow_succ, RingAut.mul_apply] using hN
  obtain ⟨y, hy0, hy⟩ :=
    CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σ hσ (x := (u : F)) hprod
  set t : F := h.bar y * y with ht
  have hbart : h.bar t = t := by rw [ht, map_mul, UnitaryFieldData.bar_bar, mul_comm]
  have ht0 : t ≠ 0 := mul_ne_zero ((map_ne_zero h.bar).2 hy0) hy0
  have hσt : σ t = t := by
    have e1 : h.bar (u : F) * h.bar (σ y) = h.bar y := by rw [← map_mul, hy]
    calc σ t = (h.bar (u : F) * u) * σ t := by rw [hu1, one_mul]
      _ = (h.bar (u : F) * h.bar (σ y)) * ((u : F) * σ y) := by
          rw [ht, map_mul, map_bar_comm h σ]; ring
      _ = t := by rw [e1, hy]
  have htmem : t ∈ fixF σ := mem_fixF.2 hσt
  set t₀ : fixF σ := ⟨t, htmem⟩ with ht₀
  have ht₀bar : h₀.bar t₀ = t₀ := Subtype.ext (by rw [hbar]; exact hbart)
  obtain ⟨s, hs⟩ := UnitaryFieldData.normHom_surjective h₀
    ⟨t₀, (UnitaryFieldData.mem_fixedField h₀).2 ht₀bar⟩
  have hsF : (s : F) * h.bar (s : F) = t := by
    have := congrArg Subtype.val hs
    rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
    have := congrArg Subtype.val this
    rw [Subfield.coe_mul, hbar] at this
    exact this
  have hs0 : (s : F) ≠ 0 := by
    intro h0
    apply ht0
    rw [← hsF, h0, zero_mul]
  have hσs : σ (s : F) = (s : F) := mem_fixF.1 s.2
  have hμ0 : y / (s : F) ≠ 0 := div_ne_zero hy0 hs0
  set μu : Fˣ := Units.mk0 (y / (s : F)) hμ0 with hμu
  have hμn : h.bar ((μu : Fˣ) : F) * (μu : F) = 1 := by
    rw [hμu, Units.val_mk0, map_div₀, div_mul_div_comm]
    have : h.bar (s : F) * (s : F) = t := by rw [mul_comm]; exact hsF
    rw [this]
    exact div_self ht0
  have hscal : Matrix.GeneralLinearGroup.scalar (Fin 3) μu ∈ unitaryIsom3 h :=
    (scal_mem_unitaryIsom3_iff h).2 (by rw [invol_apply h]; exact hμn)
  have hM'U : Matrix.GeneralLinearGroup.scalar (Fin 3) μu * (A₀ : GL (Fin 3) F) ∈ unitaryIsom3 h :=
    mul_mem hscal A₀.2
  have hM'fix : mapσ σ (Matrix.GeneralLinearGroup.scalar (Fin 3) μu * (A₀ : GL (Fin 3) F)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μu * (A₀ : GL (Fin 3) F) := by
    rw [map_mul, mapσ_scalar, hσA, ← mul_assoc, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, hμu, Units.val_mk0]
    rw [map_div₀, hσs, div_mul_eq_mul_div, mul_comm (σ y) (u : F), hy]
  obtain ⟨M₀, hM₀⟩ := exists_liftGL σ hM'fix
  have hM₀U : M₀ ∈ unitaryIsom3 h₀ := (liftGL_mem_unitaryIsom3_iff h h₀ hbar M₀).1 (hM₀ ▸ hM'U)
  refine ⟨⟨M₀, hM₀U⟩, ?_⟩
  rw [phi_apply]
  have e : liftU h h₀ hbar ⟨M₀, hM₀U⟩ =
      (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) μu, hscal⟩ : unitaryIsom3 h) * A₀ :=
    Subtype.ext (by rw [coe_liftU]; exact hM₀)
  rw [e, map_mul, psuConj_scalar hscal, one_mul]

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF
