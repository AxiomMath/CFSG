module

public import CFSG.ClassicalInvolution.Q3.Q3WASPat

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply det_blockMat blockMat_mul blockMat_one
  blockMat_comm)
open scoped MatrixGroups Matrix

section Chart

variable {F : Type} [Field F]

theorem partner_chart_three3 [Finite F] (hF3 : Nat.card F = 3)
    {X : Type} [Group X] (θ : SL(3 + 1, F) →* X)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : X ≃* X) (hσ : ∀ x, σ (σ x) = x)
    (g : GL (Fin (3 + 1)) F) (hg : ∀ x, σ (θ x) = θ (slConjugation (3 + 1) F g x))
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨2, by omega⟩ A)) =
      θ (blockSL2 F 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F 3 ⟨0, by omega⟩ A)) :
    ∃ h : GL (Fin (3 + 1)) F,
      (blockSL2 F 3 ⟨0, by omega⟩).range.map (slConjugation (3 + 1) F h).toMonoidHom =
        (blockSL2 F 3 ⟨0, by omega⟩).range ∧
      (∀ A : SL(2, F), slConjugation (3 + 1) F h (blockSL2 F 3 ⟨2, by omega⟩ A) =
        blockSL2 F 3 ⟨2, by omega⟩ A) ∧
      ∀ x, σ (θ (slConjugation (3 + 1) F h x)) =
        θ (slConjugation (3 + 1) F h (slConjugation (3 + 1) F (partnerDiag 3 1) x)) := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP3 : ∀ l : SL(2, F), l ^ 3 ∈ ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ := fun l =>
    pow_three_mem_commutator_of_equiv hF3 (Subgroup.topEquiv (G := SL(2, F))) l trivial
  have hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x := ker_orderOf_not_dvd_three hF3 (by omega) hker
  have hPn : Group.IsPerfect SL(3 + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hfixed : ∀ A : SL(2, F), slConjugation (3 + 1) F g (blockSL2 F 3 ⟨2, by omega⟩ A) =
      blockSL2 F 3 ⟨2, by omega⟩ A := by
    intro A
    have := hom_eq_of_central_ker3 θ hker hcop hP3
      ((slConjugation (3 + 1) F g).toMonoidHom.comp (blockSL2 F 3 ⟨2, by omega⟩))
      (blockSL2 F 3 ⟨2, by omega⟩)
      (fun A => by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hg, hfix A])
    exact DFunLike.congr_fun this A
  obtain ⟨c1, c2⟩ := commute_of_fixes_block g ⟨2, by omega⟩ hfixed
  obtain ⟨e1, e2, e3, e4, e5⟩ := block_of_commute_single _ c1 c2
  have eC : (⟨2, by omega⟩ : Fin 3).castSucc = (2 : Fin (3 + 1)) := rfl
  have eS : (⟨2, by omega⟩ : Fin 3).succ = (3 : Fin (3 + 1)) := rfl
  simp only [eC, eS] at e1 e2 e3 e4 e5
  set G : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) with hG
  have z02 : G 0 2 = 0 := e2 0 (by decide)
  have z12 : G 1 2 = 0 := e2 1 (by decide)
  have z32 : G 3 2 = 0 := e2 3 (by decide)
  have z03 : G 0 3 = 0 := e3 0 (by decide)
  have z13 : G 1 3 = 0 := e3 1 (by decide)
  have z23 : G 2 3 = 0 := e3 2 (by decide)
  have z20 : G 2 0 = 0 := e4 0 (by decide)
  have z21 : G 2 1 = 0 := e4 1 (by decide)
  have z30 : G 3 0 = 0 := e5 0 (by decide)
  have z31 : G 3 1 = 0 := e5 1 (by decide)
  have h33 : G 3 3 = G 2 2 := e1.symm
  have hlam : G 2 2 ≠ 0 := by
    intro h0
    apply det_ne_zero_of_gl g
    refine Matrix.det_eq_zero_of_row_eq_zero (2 : Fin 4) fun j => ?_
    by_cases hj : j = 2
    · rw [hj]; exact h0
    · exact e4 j hj
  have hsq : ∀ x, slConjugation (3 + 1) F g (slConjugation (3 + 1) F g x) = x := by
    have := hom_eq_of_central_ker θ hker (L := SL(3 + 1, F))
      ((slConjugation (3 + 1) F g).toMonoidHom.comp (slConjugation (3 + 1) F g).toMonoidHom)
      (MonoidHom.id _)
      (fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [← hg, ← hg, hσ])
    intro x
    exact DFunLike.congr_fun this x
  have hgg : ∀ x, slConjugation (3 + 1) F (g * g) x = x := fun x => by
    rw [map_mul, MulAut.mul_apply]; exact hsq x
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_single ((g * g : GL (Fin (3 + 1)) F) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) (by omega)
    (fun i j hij => commute_single_of_conj_fixed (g * g) hij (hgg _))
  have hGG : G * G = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [hG, ← Units.val_mul]; exact hc
  have hscal : G 0 1 = 0 → G 1 0 = 0 → G 0 0 = G 1 1 → False := by
    intro hb hc' hd
    have hoff : ∀ i j : Fin (3 + 1), i ≠ j →
        (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
    obtain ⟨u, hu⟩ := exists_diagGL_of_offdiag_zero g hoff
    have hu01 : u ⟨0, by omega⟩ = u ⟨1, by omega⟩ := by
      have h1 : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 0 0 = u ⟨0, by omega⟩ := by
        rw [hu, coe_diagGL]; simp
      have h2 : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 1 1 = u ⟨1, by omega⟩ := by
        rw [hu, coe_diagGL]; simp
      exact Units.ext (by rw [← h1, ← h2]; exact hd)
    obtain ⟨A, hA⟩ := hmove
    apply hA
    rw [hg, hu, slConjugation_diagGL_blockSL2 u ⟨0, by omega⟩ hu01 A]
  obtain ⟨P, hPdet, hid⟩ := exists_block_diagonalizer_three h2 G z02 z03 z12 z13 z20 z21 z30 z31
    z23 z32 h33 hlam c hGG hscal
  set lamU : Fˣ := Units.mk0 (G 2 2) hlam with hlamU
  have hD : g * blockGL P hPdet = blockGL P hPdet * diagGL (fun i => lamU * partnerEnt 3 1 i) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_blockGL]
    show G * blockMat 4 0 P = blockMat 4 0 P * _
    have hdiag : (![-G 2 2, G 2 2, G 2 2, G 2 2] : Fin 4 → F) =
        fun i => ((lamU * partnerEnt 3 1 i : Fˣ) : F) := by
      funext i
      fin_cases i <;> simp [partnerEnt, hlamU]
    rw [hid, hdiag]
  refine ⟨blockGL P hPdet, map_range_conj_blockGL P hPdet, conj_blockGL_two P hPdet, ?_⟩
  intro x
  rw [hg, ← MulAut.mul_apply, ← map_mul, hD, map_mul, MulAut.mul_apply]
  congr 2
  exact slConjugation_diagGL_congr (fun i => lamU * partnerEnt 3 1 i) (partnerEnt 3 1) lamU
    (fun i => rfl) x

theorem partner_chart_three_amb3 [Finite F] (hF3 : Nat.card F = 3)
    (hcl : LinearAutClassification F (3 + 1)) {Y : Type} [Group Y] (θ : SL(3 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨2, by omega⟩ A)) =
      θ (blockSL2 F 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F 3 ⟨0, by omega⟩ A)) :
    ∃ h : GL (Fin (3 + 1)) F,
      (blockSL2 F 3 ⟨0, by omega⟩).range.map (slConjugation (3 + 1) F h).toMonoidHom =
        (blockSL2 F 3 ⟨0, by omega⟩).range ∧
      (∀ A : SL(2, F), slConjugation (3 + 1) F h (blockSL2 F 3 ⟨2, by omega⟩ A) =
        blockSL2 F 3 ⟨2, by omega⟩ A) ∧
      ∀ x, σ (θ (slConjugation (3 + 1) F h x)) =
        θ (slConjugation (3 + 1) F h (slConjugation (3 + 1) F (partnerDiag 3 1) x)) := by
  obtain ⟨g, hg⟩ := innerDiag_of_partner_blocks_amb3 hF3 (m := 3) (by omega) hcl θ hker σ hσ
    hstab (fun a ha A => by
      have : a = ⟨2, by omega⟩ := by
        rcases ha with ha | ⟨ha1, ha2⟩
        · exact Fin.ext (by simp only; omega)
        · omega
      subst this
      exact hfix A) hmove
  exact partner_chart_three3 hF3 θ hker σ hσ g hg hfix hmove

end Chart

end CFSG.ClassicalInvolution.Q3.Q3W
