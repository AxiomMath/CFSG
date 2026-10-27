module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Interface
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.ModelF4
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

open CFSG.Fischer Matrix
open CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

namespace CFSG.GF2Type.Smith1979.W4Swap.Model

variable {E : Type} [Field E] [Algebra (ZMod 2) E]
variable (P : EvenNormPlane (ZMod 2) E)

noncomputable def slEquiv (ρ : E ≃+* F4) : SL(2, E) ≃* SL(2, F4) where
  toFun := Matrix.SpecialLinearGroup.map ρ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ρ.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map ρ.toRingHom).map_mul

@[simp] theorem coe_slEquiv (ρ : E ≃+* F4) (g : SL(2, E)) :
    (slEquiv ρ g).1 = g.1.map ρ := by
  ext i j
  simp [slEquiv, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem sigma_eq_sq (z : E) : P.σ z = z ^ 2 := by
  rw [P.sigma_eq_pow, show Nat.card (ZMod 2) = 2 by simp [Nat.card_eq_fintype_card, ZMod.card]]

theorem rho_sigma_sq (ρ : E ≃+* F4) (z : E) : ρ (P.σ z) = (ρ z) ^ 2 := by
  rw [sigma_eq_sq P z, map_pow]

theorem map_injective (ρ : E ≃+* F4) :
    Function.Injective (fun M : Matrix (Fin 2) (Fin 2) E => M.map ρ) := by
  intro M N h
  ext i j
  exact ρ.injective (by simpa using congrFun (congrFun h i) j)

theorem map_herm (ρ : E ≃+* F4) (Y : hermFourSpace P.σ) :
    ((Y.1.map ρ).map frob)ᵀ = Y.1.map ρ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, frob_apply]
  rw [← rho_sigma_sq P ρ (Y.1 j i), mem_hermFourSpace.mp Y.2 i j]

theorem map_hermFourRho (ρ : E ≃+* F4) (g : SL(2, E)) (Y : hermFourSpace P.σ) :
    (hermFourRho P g Y).1.map ρ = Act (slEquiv ρ g).1 (Y.1.map ρ) := by
  rw [coe_hermFourRho]
  simp only [Act, coe_slEquiv]
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  rw [Matrix.transpose_map]
  congr 1
  have hcomp : (⇑ρ ∘ ⇑P.σ) = (⇑frob ∘ ⇑ρ) := by
    funext z
    exact rho_sigma_sq P ρ z
  rw [Matrix.map_map, Matrix.map_map, hcomp]

theorem map_det (ρ : E ≃+* F4) (M : Matrix (Fin 2) (Fin 2) E) :
    (M.map ρ).det = ρ M.det := by
  simpa [RingHom.mapMatrix_apply] using (RingHom.map_det ρ.toRingHom M).symm

noncomputable def JE : hermFourSpace P.σ :=
  ⟨hermFourMat P.σ 0 0 1, hermFourMat_mem P 0 0 1⟩

@[simp] theorem map_JE (ρ : E ≃+* F4) : (JE P).1.map ρ = J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [JE, J, hermFourMat]

theorem exists_conj (ρ : E ≃+* F4) (X : hermFourSpace P.σ) (hX : hermFourForm P X = 1) :
    ∃ h0 : SL(2, E), hermFourRho P h0 (JE P) = X := by
  have hdet : X.1.det = 1 := by
    have h := algebraMap_hermFourForm P X
    rw [hX, map_one] at h
    exact h.symm
  let X4 : F4Mat := X.1.map ρ
  have hX4 : (X4.map frob)ᵀ = X4 := map_herm P ρ X
  have hdet4 : X4.det = 1 := by
    change (X.1.map ρ).det = 1
    rw [map_det ρ X.1, hdet, map_one]
  obtain ⟨g0, hg0SL, hg0J⟩ := exists_isSL_act_J_eq X4 hX4 hdet4
  let g0SL : SL(2, F4) := mkSL g0 hg0SL
  let h0 : SL(2, E) := (slEquiv ρ).symm g0SL
  have hh0 : slEquiv ρ h0 = g0SL := (slEquiv ρ).apply_symm_apply g0SL
  have hg0J' : ActG g0SL J = X4 := by
    simpa only [g0SL, mkSL, ActG] using hg0J
  have hXeq : X = hermFourRho P h0 (JE P) := by
    apply Subtype.ext
    apply map_injective ρ
    calc
      X.1.map ρ = ActG g0SL J := hg0J'.symm
      _ = ActG (slEquiv ρ h0) ((JE P).1.map ρ) := by
        rw [hh0]
        simp
      _ = (hermFourRho P h0 (JE P)).1.map ρ := (map_hermFourRho P ρ h0 (JE P)).symm
  refine ⟨h0, hXeq.symm⟩

end CFSG.GF2Type.Smith1979.W4Swap.Model

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.GF2Type.Smith1979.W4Swap.Model

theorem hermStabFacts : HermStabFacts := by
  intro E _ _ P hE X hX
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card F4 := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hE]
  let ρ : E ≃+* F4 := FiniteField.ringEquivOfCardEq hcard
  obtain ⟨h0, hXeq⟩ := exists_conj P ρ X hX
  let g0SL : SL(2, F4) := slEquiv ρ h0
  let e4 : SL(2, E) ≃* SL(2, F4) := (slEquiv ρ).trans (MulAut.conj g0SL⁻¹)
  have hstab_iff (h : SL(2, E)) : stabJ (e4 h).1 ↔ hermFourRho P h X = X := by
    have hX4 : X.1.map ρ = ActG g0SL Model.J := by
      rw [← hXeq, map_hermFourRho P ρ h0 (JE P)]
      simp only [g0SL, map_JE, ActG]
    have hconj : ActG (e4 h) Model.J =
        ActG g0SL⁻¹ (ActG (slEquiv ρ h) (X.1.map ρ)) := by
      rw [show e4 h = g0SL⁻¹ * slEquiv ρ h * g0SL by
        simp only [e4, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]]
      rw [ActG_mul, ActG_mul, hX4]
    have hiff : ActG (e4 h) Model.J = Model.J ↔
        ActG (slEquiv ρ h) (X.1.map ρ) = X.1.map ρ := by
      rw [hconj]
      constructor
      · intro hh
        have hcong := congrArg (ActG g0SL) hh
        have hL : ActG g0SL (ActG g0SL⁻¹ (ActG (slEquiv ρ h) (X.1.map ρ))) =
            ActG (slEquiv ρ h) (X.1.map ρ) := by
          rw [← ActG_mul, mul_inv_cancel, ActG_one]
        rw [hL] at hcong
        rwa [← hX4] at hcong
      · intro hh
        have hcong := congrArg (ActG g0SL⁻¹) hh
        have hR : ActG g0SL⁻¹ (X.1.map ρ) = Model.J := by
          rw [hX4, ← ActG_mul, inv_mul_cancel, ActG_one]
        exact hcong.trans hR
    have hstab : stabJ (e4 h).1 ↔ ActG (e4 h) Model.J = Model.J := by
      constructor
      · intro hs; exact hs.2
      · intro hs; exact ⟨(e4 h).2, hs⟩
    rw [hstab, hiff]
    constructor
    · intro hh
      apply Subtype.ext
      apply map_injective ρ
      calc
        (hermFourRho P h X).1.map ρ = Act (slEquiv ρ h).1 (X.1.map ρ) :=
          map_hermFourRho P ρ h X
        _ = ActG (slEquiv ρ h) (X.1.map ρ) := rfl
        _ = X.1.map ρ := hh
    · intro hh
      change Act (slEquiv ρ h).1 (X.1.map ρ) = X.1.map ρ
      rw [← map_hermFourRho P ρ h X]
      exact congrArg (fun Z : hermFourSpace P.σ => Z.1.map ρ) hh
  have hcardX : Nat.card {h : SL(2, E) // hermFourRho P h X = X} = 6 := by
    have e : {h : SL(2, E) // hermFourRho P h X = X} ≃
        {g : SL(2, F4) // StabJ g} :=
      Equiv.subtypeEquiv e4.toEquiv (fun h => (hstab_iff h).symm)
    rw [Nat.card_congr e, card_stabJ_SL]
  exact ⟨hcardX, by
    intro Y hY
    let Y' : hermFourSpace P.σ := hermFourRho P h0⁻¹ Y
    have hYeq : Y = hermFourRho P h0 Y' := by
      change Y = hermFourRho P h0 (hermFourRho P h0⁻¹ Y)
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hY'val : Y'.1.map ρ = ActG g0SL⁻¹ (Y.1.map ρ) := by
      change (hermFourRho P h0⁻¹ Y).1.map ρ = ActG g0SL⁻¹ (Y.1.map ρ)
      rw [map_hermFourRho P ρ h0⁻¹ Y]
      rw [show slEquiv ρ h0⁻¹ = g0SL⁻¹ by rw [MulEquiv.map_inv]]
      rfl
    have hY' : ∀ g : SL(2, F4), StabJ g → Act g.1 (Y'.1.map ρ) = Y'.1.map ρ := by
      intro g hg
      have hXg : hermFourRho P (e4.symm g) X = X :=
        (hstab_iff (e4.symm g)).mp (by simpa [StabJ] using hg)
      have hYg : hermFourRho P (e4.symm g) Y = Y := hY _ hXg
      have h1 : ActG (slEquiv ρ (e4.symm g)) (Y.1.map ρ) = Y.1.map ρ := by
        change Act (slEquiv ρ (e4.symm g)).1 (Y.1.map ρ) = Y.1.map ρ
        rw [← map_hermFourRho P ρ (e4.symm g) Y]
        exact congrArg (fun Z : hermFourSpace P.σ => Z.1.map ρ) hYg
      have hsymm : slEquiv ρ (e4.symm g) = g0SL * g * g0SL⁻¹ := by
        have h := (e4).apply_symm_apply g
        rw [show e4 (e4.symm g) = g0SL⁻¹ * slEquiv ρ (e4.symm g) * g0SL by
          simp only [e4, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]] at h
        calc
          slEquiv ρ (e4.symm g) =
              g0SL * (g0SL⁻¹ * slEquiv ρ (e4.symm g) * g0SL) * g0SL⁻¹ := by group
          _ = g0SL * g * g0SL⁻¹ := by rw [h]
      have h1' : ActG (g0SL * g * g0SL⁻¹) (Y.1.map ρ) = Y.1.map ρ := by
        rw [← hsymm]
        exact h1
      have h2 := congrArg (ActG g0SL⁻¹) h1'
      rw [← ActG_mul] at h2
      have h3 : g0SL⁻¹ * (g0SL * g * g0SL⁻¹) = g * g0SL⁻¹ := by group
      rw [h3] at h2
      rw [hY'val]
      change ActG g (ActG g0SL⁻¹ (Y.1.map ρ)) = ActG g0SL⁻¹ (Y.1.map ρ)
      rw [← ActG_mul]
      exact h2
    have hM2 := eq_zero_or_eq_J_of_forall_StabJ (Y'.1.map ρ) (map_herm P ρ Y') hY'
    rcases hM2 with hzero | hJ
    · left
      have hY'0 : Y' = 0 := by
        apply Subtype.ext
        apply map_injective ρ
        simpa using hzero
      rw [hYeq, hY'0, map_zero]
    · right
      have hY'J : Y' = JE P := by
        apply Subtype.ext
        apply map_injective ρ
        simpa using hJ
      rw [hYeq, hY'J, hXeq], by
    intro c hc
    let c4 : SL(2, F4) := e4 c
    have hcent : ∀ g : SL(2, F4), StabJ g → c4 * g = g * c4 := by
      intro g hg
      have hX : hermFourRho P (e4.symm g) X = X :=
        (hstab_iff (e4.symm g)).mp (by simpa [StabJ] using hg)
      have hcomm := hc (e4.symm g) hX
      have hcong := congrArg (fun z => e4 z) hcomm
      simpa [c4] using hcong
    have hc4 : c4 = 1 := eq_one_of_forall_StabJ_commute c4 hcent
    have hc4' : e4 c = 1 := hc4
    exact e4.injective (hc4'.trans (map_one e4).symm), by
    intro c hc
    let c4 : SL(2, F4) := e4 c
    have hnorm : ∀ g : SL(2, F4), StabJ g → StabJ (c4 * g * c4⁻¹) := by
      intro g hg
      have hX : hermFourRho P (e4.symm g) X = X :=
        (hstab_iff (e4.symm g)).mp (by simpa [StabJ] using hg)
      have hmem : hermFourRho P (c * (e4.symm g) * c⁻¹) X = X := hc (e4.symm g) hX
      have hthis := (hstab_iff (c * (e4.symm g) * c⁻¹)).mpr hmem
      have heq : e4 (c * (e4.symm g) * c⁻¹) = c4 * g * c4⁻¹ := by
        simp [c4, map_mul]
      rwa [heq] at hthis
    have hc4 : StabJ c4 := StabJ_of_forall_StabJ_conj c4 hnorm
    exact (hstab_iff c).mp (by simpa [c4] using hc4)⟩

end CFSG.GF2Type.Smith1979.W4Swap
