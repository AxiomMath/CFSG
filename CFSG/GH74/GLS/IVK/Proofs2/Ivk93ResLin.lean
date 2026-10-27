module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResSL2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups

section Lin

variable {F : Type} [Field F]

@[expose] def linAm : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem linAm_sq : (linAm : Matrix (Fin 4) (Fin 4) F) * linAm = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linAm, Matrix.mul_apply, Fin.sum_univ_four]

theorem linAm_det : (linAm : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [linAm, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]

@[expose] def linA : GL (Fin 4) F :=
  ⟨linAm, -linAm, by rw [Matrix.mul_neg, linAm_sq, neg_neg], by rw [Matrix.neg_mul, linAm_sq, neg_neg]⟩

theorem coe_linA : ((linA : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = linAm := rfl

theorem linA_sq : (linA : GL (Fin 4) F) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 4) (-1) := by
  apply Units.ext
  rw [pow_two, Units.val_mul, coe_linA, linAm_sq]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  · simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]

theorem ivk93res_sl2_lin [Finite F] (hq : Nat.card F % 4 = 3) :
    Ivk93ResSL2 (StatedProj (StatedSL 4 F)) (Nat.card F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hns : ¬ IsSquare (-1 : F) := by
    intro hsq
    rw [Nat.card_eq_fintype_card] at hq
    exact (FiniteField.isSquare_neg_one_iff.1 hsq) hq
  have hns' : ¬ IsSquare (((-1 : Fˣ) : F)) := by simpa using hns
  have : Fact (¬ IsSquare (((-1 : Fˣ) : F))) := ⟨hns'⟩
  have hsq : (linA : GL (Fin 4) F) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 4) (-1) := linA_sq
  have hfinE : Finite (extension (((-1 : Fˣ) : F))) :=
    CatalogueBProjectiveInvolution.quadraticExtension_finite _
  have hm2 : matrixDimension (linA : GL (Fin 4) F) (-1) hsq = 2 := by
    have h := matrixDimension_twice (linA : GL (Fin 4) F) (-1) hsq
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨m, hm, ⟨e⟩⟩ : ∃ m : ℕ, m = 2 ∧
      Nonempty (↥(Subgroup.centralizer {(linA : GL (Fin 4) F)}) ≃*
        GL (Fin m) (extension (((-1 : Fˣ) : F)))) :=
    ⟨_, hm2, ⟨matrixCentralizerQuadraticEquiv linA (-1) hsq⟩⟩
  subst hm
  set E := extension (((-1 : Fˣ) : F)) with hE
  have hcardE : Nat.card E = Nat.card F ^ 2 := by
    let : Fintype E := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
      extension_finrank]
  have hF3 : 3 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hE4 : 4 ≤ Nat.card E := by
    rw [hcardE]
    nlinarith
  have hQ : CFSG.IsQuasisimple SL(2, E) := GHInv.isQuasisimple_sl2 hE4
  have hperf : commutator SL(2, E) = ⊤ := hQ.1.commutator_eq_top
  let ψ₀ : SL(2, E) →* GL (Fin 4) F :=
    (Subgroup.centralizer {(linA : GL (Fin 4) F)}).subtype.comp
      (e.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL)
  have hψ₀c : ∀ g, ψ₀ g * linA = linA * ψ₀ g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (e.symm (Matrix.SpecialLinearGroup.toGL g)).2
  have hdet : ∀ g, ((ψ₀ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    have hker : commutator SL(2, E) ≤ (Matrix.GeneralLinearGroup.det.comp ψ₀).ker :=
      Abelianization.commutator_subset_ker _
    intro g
    have hg : g ∈ (Matrix.GeneralLinearGroup.det.comp ψ₀).ker := hker (hperf ▸ Subgroup.mem_top g)
    have h1 : Matrix.GeneralLinearGroup.det (ψ₀ g) = 1 := hg
    have h2 := congrArg (fun u : Fˣ => (u : F)) h1
    simpa using h2
  have hmem : ∀ g, ψ₀ g ∈ StatedSL 4 F := fun g => Subgroup.subset_closure (hdet g)
  have hAmem : (linA : GL (Fin 4) F) ∈ StatedSL 4 F :=
    Subgroup.subset_closure (show ((linA : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 from
      by rw [coe_linA]; exact linAm_det)
  let ψ₁ : SL(2, E) →* ↥(StatedSL 4 F) := ψ₀.codRestrict (StatedSL 4 F) hmem
  let ψ : SL(2, E) →* StatedProj (StatedSL 4 F) := (QuotientGroup.mk' _).comp ψ₁
  let y : StatedProj (StatedSL 4 F) := QuotientGroup.mk ⟨linA, hAmem⟩
  have hy2 : y ^ 2 = 1 := by
    show (QuotientGroup.mk (⟨linA, hAmem⟩ : ↥(StatedSL 4 F)) : StatedProj (StatedSL 4 F)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨-1, linA_sq.symm⟩
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_subgroupOf] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 1) hc
    simp [coe_linA, linAm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
  refine ⟨y, E, inferInstance, hfinE, ψ, orderOf_eq_prime hy2 hy1, hcardE, ?_, fun g => ?_⟩
  · intro h1
    have hsc : ∀ g, ψ₀ g ∈ StatedScalars (Fin 4) F := by
      intro g
      have h2 : ψ g = 1 := by rw [h1]; rfl
      have h3 := (QuotientGroup.eq_one_iff _).1 h2
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    have hcomm : ∀ g g', ψ₀ g * ψ₀ g' = ψ₀ g' * ψ₀ g := by
      intro g g'
      obtain ⟨c, hc⟩ := hsc g
      have hcen : ψ₀ g ∈ Subgroup.center (GL (Fin 4) F) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨c, hc⟩
      exact (Subgroup.mem_center_iff.1 hcen (ψ₀ g')).symm
    have hker : commutator SL(2, E) ≤ ψ₀.ker := by
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b)
    let g₀ : SL(2, E) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hg₀ : ψ₀ g₀ = 1 := hker (hperf ▸ Subgroup.mem_top g₀)
    have h4 : e.symm (Matrix.SpecialLinearGroup.toGL g₀) = 1 := Subtype.ext hg₀
    have h5 : Matrix.SpecialLinearGroup.toGL g₀ = 1 := by
      have := congrArg e h4
      simpa using this
    have h6 := congrArg (fun u : GL (Fin 2) E => (u : Matrix (Fin 2) (Fin 2) E) 0 1) h5
    change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) E) 0 1 = (1 : Matrix (Fin 2) (Fin 2) E) 0 1 at h6
    simp at h6
  · show ψ g * y = y * ψ g
    show (QuotientGroup.mk (ψ₁ g) : StatedProj (StatedSL 4 F)) * QuotientGroup.mk ⟨linA, hAmem⟩ =
      QuotientGroup.mk ⟨linA, hAmem⟩ * QuotientGroup.mk (ψ₁ g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hψ₀c g)

end Lin

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
