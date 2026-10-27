module

public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Matrix Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.ComponentClassification.CatalogueBOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups commutatorElement

theorem dvd_card_sl2_of_dvd_succ {F : Type} [Field F] [Finite F] {ℓ : ℕ}
    (hdvd : ℓ ∣ Nat.card F + 1) : ℓ ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h1 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    rw [← one_pow 2 (M := ℕ), Nat.sq_sub_sq]
    simp
  rw [h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hdvd _) _

theorem exists_orderOf_traceZeroSpecialImage {F : Type} [Field F] [Finite F] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card F + 1) :
    ∃ y ∈ traceZeroSpecialImage F, orderOf y = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨B, hB⟩ := exists_prime_orderOf_dvd_card' ℓ (dvd_card_sl2_of_dvd_succ hdvd)
  refine ⟨traceZeroOrthogonalAction (SpecialLinearGroup.toGL B), ⟨B, rfl⟩, ?_⟩
  have hdvd' : orderOf (traceZeroOrthogonalAction (SpecialLinearGroup.toGL B)) ∣ ℓ := by
    rw [← hB]
    exact orderOf_map_dvd
      (traceZeroOrthogonalAction.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)) B
  rcases (Nat.dvd_prime hℓ).1 hdvd' with h | h
  · exfalso
    rw [orderOf_eq_one_iff, traceZeroOrthogonalAction_eq_one_iff] at h
    obtain ⟨c, hc⟩ := h
    have hBc : (B : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (c : F) := by
      have := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hc
      simpa using this.symm
    have hdet : (c : F) ^ 2 = 1 := by
      have := B.2
      rw [hBc, Matrix.det_fin_two] at this
      simpa [Matrix.scalar_apply, sq] using this
    have hB2 : B ^ 2 = 1 := by
      have h1 : ((B ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_pow, hBc, ← map_pow, hdet, map_one]
      exact Subtype.ext h1
    have : ℓ ∣ 2 := hB ▸ orderOf_dvd_of_pow_eq_one hB2
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  · exact h

theorem lin_graph_centralizer_ell {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (h3 : Nat.card F ≠ 3) {A : GL (Fin 3) F} (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card F + 1) :
    ∃ N : Subgroup (projectiveSL 3 F), CFSG.IsQuasisimple ↥N ∧
      (∀ n ∈ N, (conjAut 3 F A * dualAut 3 F) n = n) ∧
      (∀ x, (conjAut 3 F A * dualAut 3 F) x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      (∀ x y, (conjAut 3 F A * dualAut 3 F) x = x → (conjAut 3 F A * dualAut 3 F) y = y →
        ⁅x, y⁆ ∈ N) ∧
      ∃ g : SL(3, F), proj 3 F g ∈ N ∧ orderOf g = ℓ := by
  classical
  set R : GL (Fin 3) F := A⁻¹ with hR
  have hRsymm : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R := transpose_inv_of_symm A hA
  set I := CatalogueBGraphForm.isometryGroup 3 F R with hI
  set Ω := ⁅I, I⁆ with hΩ
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hF
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hF R hRsymm
  have hdim : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  obtain ⟨d, ψ, e, -, -, hcomm0, hq0, -⟩ := orthogonal_three_derived hodd h3
    (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
  have hq : CFSG.IsQuasisimple Ω := by
    have := isQuasisimple_trans (isoOrthGL hF R hRsymm) hq0
    rwa [trans_commutator] at this
  set ΩS : Subgroup SL(3, F) := Ω.comap SpecialLinearGroup.toGL with hΩS
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hqS : CFSG.IsQuasisimple ΩS :=
    LocalCores.isQuasisimple_of_mulEquiv ((ΩS.equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmapΩ)).symm hq
  have hell : ∃ g : SL(3, F), g ∈ ΩS ∧ orderOf g = ℓ := by
    obtain ⟨y, hy, hyord⟩ := exists_orderOf_traceZeroSpecialImage (F := F) hℓ hℓ2 hdvd
    have hz : e.symm y ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R)) := by
      rw [hcomm0]
      exact ⟨y, hy, rfl⟩
    have hzord : orderOf (e.symm y) = ℓ := by
      rw [MulEquiv.orderOf_eq]
      exact hyord
    have hwΩ : ((isoOrthGL hF R hRsymm (e.symm y) : ↥I) : GL (Fin 3) F) ∈ Ω := by
      rw [hΩ, ← trans_commutator (isoOrthGL hF R hRsymm)]
      exact ⟨isoOrthGL hF R hRsymm (e.symm y), ⟨e.symm y, hz, rfl⟩, rfl⟩
    have hword : orderOf ((isoOrthGL hF R hRsymm (e.symm y) : ↥I) : GL (Fin 3) F) = ℓ := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hzord
    have hwmem : ((isoOrthGL hF R hRsymm (e.symm y) : ↥I) : GL (Fin 3) F) ∈
        ΩS.map SpecialLinearGroup.toGL := hmapΩ ▸ hwΩ
    obtain ⟨g, hg, hgw⟩ := hwmem
    refine ⟨g, hg, ?_⟩
    rw [← hword, ← hgw]
    exact (orderOf_injective _ SpecialLinearGroup.toGL_injective g).symm
  have hrep : ∀ x : projectiveSL 3 F, (conjAut 3 F A * dualAut 3 F) x = x →
      ∃ g : SL(3, F), g ∈ isometrySL 3 A⁻¹ ∧ proj 3 F g = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_mul_dualAut_proj] at hx
    exact exists_isometrySL_rep hA hx
  refine ⟨ΩS.map (proj 3 F), ?_, ?_, ?_, ?_, ?_⟩
  · refine LocalCores.isQuasisimple_map hqS (proj 3 F) fun hker => ?_
    have hab : ∀ a ∈ ΩS, ∀ b ∈ ΩS, a * b = b * a := by
      intro a ha b hb
      have ha' : a ∈ scalars 3 F := by
        have h1 : proj 3 F a = 1 := hker ha
        exact proj_eq_one_iff.1 h1
      exact (mem_center_iff.1 (scalars_le_center 3 F ha') b).symm
    have : Nontrivial ΩS := LocalCores.isQuasisimple_nontrivial hqS
    have hcomm : commutator ΩS = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hab a a.2 b b.2)
    have hperfF := hqS.1.commutator_eq_top
    rw [hcomm] at hperfF
    exact bot_ne_top hperfF
  · rintro _ ⟨h, hh, rfl⟩
    rw [conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff A h).2 (commutator_le_self I hh)
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨h, hh, rfl⟩ := hn
    refine ⟨g * h * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    change SpecialLinearGroup.toGL (g * h * g⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    have hg' : graphLiftGL A (SpecialLinearGroup.toGL g) = SpecialLinearGroup.toGL g *
        GeneralLinearGroup.scalar (Fin 3) 1 := by
      rw [map_one, mul_one]
      exact (graphLiftGL_eq_iff A _).2 hg
    exact conj_mem_commutator_isometryGroup hg' hh
  · intro x y hx hy
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨k, hk, rfl⟩ := hrep y hy
    refine ⟨⁅g, k⁆, ?_, by simp only [map_commutatorElement]⟩
    change SpecialLinearGroup.toGL ⁅g, k⁆ ∈ Ω
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hg hk
  · obtain ⟨g, hg, hgord⟩ := hell
    exact ⟨g, ⟨g, hg, rfl⟩, hgord⟩

end CFSG.GH74.GLS.IVK.GHInv
