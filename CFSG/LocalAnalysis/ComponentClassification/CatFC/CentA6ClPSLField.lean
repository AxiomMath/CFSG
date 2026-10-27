module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField (pslFieldAut pslFieldAut_mk fixedField
  fixedField_coe fixedField_card_square)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)

namespace PSLA6

theorem exists_a6Hyp_of_conj {S : Type} [Group S] [Finite S] (σ σ' : MulAut S) (e : S ≃* S)
    (hσ : σ = MulAut.congr e σ') {D : Subgroup ↥(fixedSubgroup σ)} (h : A6Hyp σ D) :
    ∃ D' : Subgroup ↥(fixedSubgroup σ'), A6Hyp σ' D' := by
  have h1 : MulAut.congr e.symm σ = σ' := by
    rw [hσ]
    ext x
    simp [MulAut.congr_apply]
  subst h1
  exact ⟨_, a6Hyp_congr e.symm σ D h⟩

section Field

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem a6_psl_field_witness (τ : K ≃+* K) {D : Subgroup ↥(fixedSubgroup (pslFieldAut (Fin n) K τ))}
    (h : A6Hyp (pslFieldAut (Fin n) K τ) D) (hn : 1 ≤ n)
    (hperf : commutator (SpecialLinearGroup (Fin n) (fixedField K τ)) = ⊤) :
    Nat.card (SpecialLinearGroup (Fin n) (fixedField K τ)) ≤ 360 * n := by
  let ψ : SpecialLinearGroup (Fin n) (fixedField K τ) →* SpecialLinearGroup (Fin n) K :=
    SpecialLinearGroup.map (fixedField K τ).subtype
  have hinj : Function.Injective ψ := by
    intro g g' hgg
    ext i j
    have := congrFun (congrFun (congrArg (fun x : SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K)) hgg) i) j
    simpa [ψ] using this
  refine h.psl_witness hperf ψ (fun g => ?_) (ker_card_le_of_injective ψ hinj hn)
  change pslFieldAut (Fin n) K τ (QuotientGroup.mk (ψ g)) = QuotientGroup.mk (ψ g)
  rw [pslFieldAut_mk]
  congr 1
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, ψ]
  exact fixedField_coe K τ _

end Field

end PSLA6

open PSLA6

section FieldMain

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem a6_psl_field (hO : LieOrderFormulasInput) {f : ℕ} (hK : Nat.card K = 3 ^ f)
    (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f) (A : GL (Fin n) K)
    (τ : K ≃+* K) (hτ : τ ≠ 1) (hσ : orderOf (semilinearAction n K A τ) = 2)
    {D : Subgroup ↥(fixedSubgroup (semilinearAction n K A τ))}
    (hD : A6Hyp (semilinearAction n K A τ) D) : n = 2 ∧ f = 4 := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hsq : semilinearAction n K A τ ^ 2 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hq : Nat.card K = 3 ∨ 9 ≤ Nat.card K := by rw [hK]; exact three_pow_cases hf
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      rcases hq with h | h
      · exfalso
        exact hadm.2.2.2.2 (by rw [hn2, hK] at *; simp [h] at *)
      · omega
    · exact Or.inl h3
  obtain ⟨heven, hτc, H, hconj⟩ :=
    CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy n K 3 f Nat.prime_three
      (by decide) hf hK hn hparameter A τ hτ hsq
  have hτ2 : τ ^ 2 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [sq, RingAut.mul_apply, hτc, hτc, ← pow_mul, ← sq, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hcongr : semilinearAction n K A τ =
      MulAut.congr (innerDiagonalAction n K H) (pslFieldAut (Fin n) K τ) :=
    ((MulEquiv.ext fun _ => rfl : MulAut.congr (innerDiagonalAction n K H)
      (pslFieldAut (Fin n) K τ) = _).trans hconj.symm).symm
  obtain ⟨D', hD'⟩ := exists_a6Hyp_of_conj _ _ (innerDiagonalAction n K H) hcongr hD
  obtain ⟨g, hfg⟩ : ∃ g, f = 2 * g := by obtain ⟨r, hr⟩ := heven; exact ⟨r, by omega⟩
  have hg1 : 1 ≤ g := by omega
  have hq₀ : Nat.card (fixedField K τ) = 3 ^ g := by
    have h : (3 ^ g) ^ 2 = Nat.card (fixedField K τ) ^ 2 := by
      rw [← pow_mul', ← hfg, ← hK]
      exact fixedField_card_square K τ hτ2 hτ
    exact (Nat.pow_left_injective two_ne_zero h).symm
  have hq₀3 : 3 ≤ Nat.card (fixedField K τ) := by
    rw [hq₀]
    exact Nat.le_self_pow (by omega) 3
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    rcases (by omega : g = 1 ∨ g = 2 ∨ 3 ≤ g) with rfl | rfl | hg3
    · exfalso
      have hf2 : f = 2 := by omega
      subst hn2 hf2
      exact hD.false_psl_two_two hσ hO hadm hm
    · exact ⟨hn2, by omega⟩
    · exfalso
      have h27 : 27 ≤ Nat.card (fixedField K τ) := by
        rw [hq₀]
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ g := Nat.pow_le_pow_right (by norm_num) hg3
      subst hn2
      haveI := CatalogueBGeneralLinear.specialLinear_perfect 2 (fixedField K τ) le_rfl
        (Or.inr (by omega)) (Or.inr (by omega))
      have hb := a6_psl_field_witness τ hD' (by omega) Group.IsPerfect.commutator_eq_top
      rw [card_SL_two] at hb
      have h1 : 27 * 728 ≤ Nat.card (fixedField K τ) * (Nat.card (fixedField K τ) ^ 2 - 1) := by
        refine Nat.mul_le_mul h27 ?_
        have : 729 ≤ Nat.card (fixedField K τ) ^ 2 := by nlinarith
        omega
      omega
  · exfalso
    haveI := CatalogueBGeneralLinear.specialLinear_perfect n (fixedField K τ) hn
      (Or.inl (by omega)) (Or.inl (by omega))
    have hb := a6_psl_field_witness τ hD' (by omega) Group.IsPerfect.commutator_eq_top
    have h2 := lt_card_SL_of_three_le hn3 hq₀3
    omega

end FieldMain

end CFSG.ComponentClassification.CatFC
