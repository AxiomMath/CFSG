module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLInner
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField (pslFieldAut pslFieldAut_mk
  fixedField fixedField_coe fixedField_card_square fixedPGL fixedPSL fixedT fixedPSLEquivT
  subfieldPGLEquivFixed)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)

theorem u42_scalar_injective {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Fˣ →* GL (Fin n) F) := by
  intro c d h
  have h1 := congrArg (fun B : GL (Fin n) F =>
    (B.val : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) h
  apply Units.ext
  simpa using h1

theorem u42_card_PGL_mul {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F] :
    Nat.card (ProjGenLinGroup (Fin n) F) * (Nat.card F - 1) = Nat.card (GL (Fin n) F) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (GL (Fin n) F))
  have h2 : Nat.card (Subgroup.center (GL (Fin n) F)) = Nat.card F - 1 := by
    rw [GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective (u42_scalar_injective hn (F := F))).toEquiv,
      Nat.card_units]
  rw [h1, h2]
  rfl

theorem u42_psl_field_eq {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (τ : K ≃+* K) :
    ∃ e : ℕ, e ∣ Nat.gcd n (Nat.card K - 1) ∧
      Nat.card ↥(fixedSubgroup (pslFieldAut (Fin n) K τ)) * e *
          (Nat.card (fixedField K τ) - 1) = Nat.card (GL (Fin n) (fixedField K τ)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Finite (fixedField K τ) := Finite.of_injective (fixedField K τ).subtype
    (fixedField K τ).subtype_injective
  refine ⟨(fixedT n K τ).index, ?_, ?_⟩
  · have h1 : (fixedT n K τ).index ∣ (pslRange n K).index :=
      Subgroup.relIndex_dvd_index_of_normal (pslRange n K) _
    exact h1.trans (u42_psl_index_dvd n K)
  · have h1 : Nat.card ↥(fixedSubgroup (pslFieldAut (Fin n) K τ)) = Nat.card (fixedT n K τ) :=
      Nat.card_congr (fixedPSLEquivT n K τ).toEquiv
    have h2 : Nat.card (fixedPGL (Fin n) K τ) = Nat.card (fixedT n K τ) * (fixedT n K τ).index :=
      (Subgroup.card_mul_index (fixedT n K τ)).symm
    have h3 : Nat.card (fixedPGL (Fin n) K τ) =
        Nat.card (ProjGenLinGroup (Fin n) (fixedField K τ)) :=
      (Nat.card_congr (subfieldPGLEquivFixed (Fin n) K τ).toEquiv).symm
    rw [h1, ← h2, h3]
    exact u42_card_PGL_mul hn

theorem u42Hyp_of_conj {S : Type} [Group S] (σ σ' : MulAut S) (e : S ≃* S)
    (hσ : σ = MulAut.congr e σ') {J : Subgroup ↥(fixedSubgroup σ)} (h : U42Hyp σ J) :
    ∃ J' : Subgroup ↥(fixedSubgroup σ'), U42Hyp σ' J' := by
  have h1 : MulAut.congr e.symm σ = σ' := by
    rw [hσ]
    ext x
    simp [MulAut.congr_apply]
  subst h1
  exact ⟨_, h.congr e.symm σ J⟩

theorem u42_psl_field {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f)
    (hf : 1 ≤ f) (hadm : StatedLieAdmissible .PSL n 3 f) (A : GL (Fin n) K)
    (τ : K ≃+* K) (hτ : τ ≠ 1) (hσ : orderOf (semilinearAction n K A τ) = 2)
    {J : Subgroup ↥(fixedSubgroup (semilinearAction n K A τ))}
    (hJ : U42Hyp (semilinearAction n K A τ) J) : False := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hne3 : (n, 3 ^ f) ≠ (2, 3) := hadm.2.2.2.2
  have hsq : semilinearAction n K A τ ^ 2 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      rw [hK]
      by_cases hf1 : f = 1
      · exfalso
        subst hf1 hn2
        exact hne3 rfl
      · calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Or.inl h3
  obtain ⟨heven, hτc, H, hconj⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy
      n K 3 f Nat.prime_three (by decide) hf hK hn hparameter A τ hτ hsq
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
  obtain ⟨J', hJ'⟩ := u42Hyp_of_conj _ _ (innerDiagonalAction n K H) hcongr hJ
  obtain ⟨g, hfg⟩ : ∃ g, f = 2 * g := by obtain ⟨r, hr⟩ := heven; exact ⟨r, by omega⟩
  have hg1 : 1 ≤ g := by omega
  have hq₀ : Nat.card (fixedField K τ) = 3 ^ g := by
    have h : (3 ^ g) ^ 2 = Nat.card (fixedField K τ) ^ 2 := by
      rw [← pow_mul', ← hfg, ← hK]
      exact fixedField_card_square K τ hτ2 hτ
    exact (Nat.pow_left_injective two_ne_zero h).symm
  obtain ⟨e, he, heq⟩ := u42_psl_field_eq (by omega : 1 ≤ n) τ
  rw [hq₀, u42_card_GL, hq₀] at heq
  rw [hK, hfg] at he
  rcases hJ'.card_mem with h0 | h0
  · rw [h0] at heq
    exact u42_arith_psl_field hg1 hn (Or.inl rfl) he heq
  · rw [h0] at heq
    exact u42_arith_psl_field hg1 hn (Or.inr rfl) he heq

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
