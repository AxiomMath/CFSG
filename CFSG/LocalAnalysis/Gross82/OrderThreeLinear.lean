module
public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.LocalAnalysis.Gross82.OrderThreeArith
import CFSG.LocalAnalysis.Gross82.OrderThreeTools
import CFSG.LocalAnalysis.Gross82.OrderThreeDiagonal
import CFSG.LocalAnalysis.Gross82.FieldOrder

public section

namespace CFSG.LocalAnalysis.Gross82.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.HardMathSupport.Lang.Coordinator
  (card_fixedSubgroup_congr card_fixedSubgroup_eq_of_intertwine congr_mem_inner_iff)

theorem projectiveSpecialLinearEquivProjectiveSL_pslFieldAut {F : Type} [Field F] (n : ℕ)
    (σ : F ≃+* F) (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n F
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.pslFieldAut (Fin n) F σ x) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n F σ
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          n F x) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin n) F)) x
  rw [show (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) A :
      Matrix.ProjectiveSpecialLinearGroup (Fin n) F) = QuotientGroup.mk A from rfl]
  rw [pslFieldAut_mk]
  change (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)
      (QuotientGroup.mk (SpecialLinearGroup.map σ.toRingHom A)) =
    fieldAut n F σ (proj n F A)
  rw [fieldAut_proj]
  rfl

theorem card_fixedSubgroup_fieldAut_dvd {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (σ : F ≃+* F) :
    Nat.card (fixedSubgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n F σ)) ∣
      lieOrderNumerator .PSL n
        (Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ)) := by
  have h1 : Nat.card (fixedSubgroup (pslFieldAut (Fin n) F σ)) =
      Nat.card (fixedSubgroup (fieldAut n F σ)) :=
    card_fixedSubgroup_eq_of_intertwine (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)
      (pslFieldAut (Fin n) F σ) (fieldAut n F σ)
      (fun x => (projectiveSpecialLinearEquivProjectiveSL_pslFieldAut n σ x).symm)
  have h2 : Nat.card (fixedSubgroup (pslFieldAut (Fin n) F σ)) ∣
      Nat.card (fixedSubgroup (pglFieldAut (Fin n) F σ)) :=
    card_fixedSubgroup_dvd_of_injective_intertwine ProjectiveSpecialLinearGroup.toPGL
      ProjectiveSpecialLinearGroup.toPGL_injective (pslFieldAut (Fin n) F σ)
      (pglFieldAut (Fin n) F σ) (toPGL_pslFieldAut (Fin n) F σ)
  rw [← h1, ← card_fixedSubgroup_pglFieldAut hn σ]
  exact h2

private theorem mem_inner_of_mem_linearAutGroup {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) (h3n : 3 ∣ n) (h3q : 3 ∣ Nat.card F - 1)
    (P : Sylow 3 (projectiveSL n F)) {β : MulAut (projectiveSL n F)}
    (hβp : β ^ 3 = 1) (hfix : ∀ x ∈ (P : Subgroup (projectiveSL n F)), β x = x)
    (hD : β ∈ linearAutGroup n F) : β ∈ inner (projectiveSL n F) :=
  mem_inner_of_mem_range_conjAut_of_fix_sylow (p := 3) (by norm_num) hn h3n h3q P β
    (by rwa [linearAutGroup_eq_range] at hD) ⟨1, by simpa using hβp⟩ hfix

private theorem dvd_numerator_of_field_descent {K : Type} [Group K]
    {F : Type} [Field F] [Finite F] {n ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hn : 3 ≤ n) (hFcard : Nat.card F = ℓ ^ f) (θ : K ≃* projectiveSL n F)
    (α : MulAut K) (hβp : (MulAut.congr θ α) ^ 3 = 1)
    (hβord : orderOf (MulAut.congr θ α) = 3)
    (hD : MulAut.congr θ α ∉ linearAutGroup n F) :
    ∃ d : ℕ, f = 3 * d ∧
      Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .PSL n (ℓ ^ d) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card, hFcard]
  have : CharP F ℓ := charP_of_card_eq_prime_pow hcard
  obtain ⟨hpf, σ, -, ⟨h, hh, hβh⟩, hcardk⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf hn hFcard Nat.prime_three (MulAut.congr θ α)
      (ProjectivePlane.mem_semilinearAutGroup_of_pow hn (by norm_num) hβp) hD hβord
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
  have hcard1 : Nat.card (fixedSubgroup (MulAut.congr θ α)) =
      Nat.card (fixedSubgroup (fieldAut n F σ)) := by
    refine (card_fixedSubgroup_eq_of_intertwine (conjAut n F H) (fieldAut n F σ)
      (MulAut.congr θ α) ?_).symm
    intro x
    rw [hβh]
    simp [MulAut.mul_apply]
  refine ⟨f / 3, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [← card_fixedSubgroup_congr θ α, hcard1, ← hcardk,
    ← card_fixedField_eq_card_semilinearFixedSubfield]
  exact card_fixedSubgroup_fieldAut_dvd (by omega) σ

private theorem exists_field_model_PSL {K : Type} [Group K] {n ℓ f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel K .PSL n ℓ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_θ : K ≃* projectiveSL n F),
      Nat.card F = ℓ ^ f := by
  have hcl : StatedClassicalModel K .PSL n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  exact ⟨F, hF, hFin,
    e.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv n F), hFcard⟩

private theorem false_of_not_inner_PSL (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .PSL n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .PSL n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .PSL n (ℓ ^ f)) {α : MulAut K} (hα : α ^ 3 = 1)
    {P : Sylow 3 K} (hfix : ∀ x ∈ (P : Subgroup K), α x = x)
    (hαin : α ∉ inner K) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAdm : StatedLieAdmissible .PSL n ℓ f := hadm
  obtain ⟨hℓ, hf, hn2, -, -⟩ := hAdm
  obtain ⟨F, hF, hFin, θ, hFcard⟩ := exists_field_model_PSL hmodel
  letI := hF
  letI := hFin
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype F := Fintype.ofFinite F
  have h3' : 3 ∣ Nat.gcd n (ℓ ^ f - 1) := h3
  have h3n : 3 ∣ n := h3'.trans (Nat.gcd_dvd_left n (ℓ ^ f - 1))
  have h3q : 3 ∣ ℓ ^ f - 1 := h3'.trans (Nat.gcd_dvd_right n (ℓ ^ f - 1))
  have hn : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
  have hβp : (MulAut.congr θ α) ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hβout : MulAut.congr θ α ∉ inner (projectiveSL n F) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  obtain ⟨P', hfix'⟩ := exists_sylow_fix_congr θ P hfix
  by_cases hD : MulAut.congr θ α ∈ linearAutGroup n F
  · exact hβout (mem_inner_of_mem_linearAutGroup hn h3n (by rwa [hFcard]) P' hβp hfix' hD)
  · have hβ1 : MulAut.congr θ α ≠ 1 :=
      fun h1 => hβout (h1 ▸
        (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
    have hβord : orderOf (MulAut.congr θ α) = 3 := orderOf_eq_prime hβp hβ1
    obtain ⟨d, hfd, hdvd⟩ :=
      dvd_numerator_of_field_descent hℓ hf hn hFcard θ α hβp hβord hD
    have hs : ℓ ^ f = (ℓ ^ d) ^ 3 := by rw [hfd, Nat.mul_comm 3 d, pow_mul]
    have hd1 : d ≠ 0 := by omega
    have hs2 : 2 ≤ ℓ ^ d := hℓ.two_le.trans (Nat.le_self_pow hd1 ℓ)
    have ha : lieOrderNumerator .PSL n (ℓ ^ d) ≠ 0 :=
      CFSG.AGLEmbedding.OuterSylow.lieOrderNumerator_ne_zero (by decide)
        (CFSG.AGLEmbedding.OuterSylow.one_le_lieSylowExponent hadm) hs2
    exact false_of_card_fixedSubgroup_dvd hLie hadm hmodel P hfix hs ha hdvd
      (CFSG.LocalAnalysis.Gross82.FieldOrder.padicValNat_three_lieOrder_psl_cube_lt hs2 hn2)

end CFSG.LocalAnalysis.Gross82.OrderThree

namespace CFSG.LocalAnalysis.Gross82

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor LieOrderFormulasInput)

theorem grossThreeInnerOrderThree_PSL (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .PSL n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .PSL n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .PSL n (ℓ ^ f)) : GrossThreeInnerOrderThree K := by
  intro α hα P hfix
  by_contra hαin
  exact OrderThree.false_of_not_inner_PSL hLie hadm hmodel h3 hα hfix hαin

end CFSG.LocalAnalysis.Gross82
