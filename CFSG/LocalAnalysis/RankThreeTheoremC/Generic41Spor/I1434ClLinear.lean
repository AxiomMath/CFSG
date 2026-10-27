module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSetup
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClNum
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

section Arith

theorem five_ne_zero_of_card {F : Type} [Field F] [Finite F] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hcard : Nat.card F = ℓ ^ f) (h5 : ℓ ≠ 5) : (5 : F) ≠ 0 := by
  intro h0
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  exact h5 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1
    ((CharP.cast_eq_zero_iff F ℓ 5).1 (by exact_mod_cast h0)))

theorem five_eq_zero_of_card_five {F E : Type} [Field F] [Field E] [Algebra F E] [Finite E]
    (h : Nat.card E = 5) : (5 : F) = 0 := by
  haveI : Fintype E := Fintype.ofFinite E
  have h5 : ((5 : ℕ) : E) = 0 := by
    have := FiniteField.cast_card_eq_zero E
    rwa [← Nat.card_eq_fintype_card, h] at this
  apply (algebraMap F E).injective
  rw [map_zero, map_ofNat]
  exact_mod_cast h5

theorem eq_X_sub_C_of_card_four {F : Type} [Field F] {h : F[X]} (hirr : Irreducible h)
    (hm : h.Monic) {c : F} (hdvd : h ∣ X ^ 5 - C c) (hc : c ≠ 0)
    (hE : Nat.card (AdjoinRoot h) = 4) : h = X - C (c ^ 2) := by
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  haveI : Finite (AdjoinRoot h) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  set r : AdjoinRoot h := AdjoinRoot.root h with hr
  have h5 : r ^ 5 = algebraMap F (AdjoinRoot h) c := by
    have := AdjoinRoot.mk_eq_zero.2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at this
    exact this
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num), eq_comm, map_eq_zero_iff _ (algebraMap F _).injective] at h5
    exact hc h5
  have hr3 : r ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [← Nat.card_eq_fintype_card, hE] at this
  have hr10 : r = algebraMap F (AdjoinRoot h) (c ^ 2) := by
    calc r = (r ^ 3) ^ 3 * r := by rw [hr3]; simp
      _ = (r ^ 5) ^ 2 := by ring
      _ = algebraMap F (AdjoinRoot h) (c ^ 2) := by rw [h5, map_pow]
  have hdiv : h ∣ X - C (c ^ 2) := by
    refine AdjoinRoot.mk_eq_zero.1 ?_
    rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero]
    exact hr10
  exact eq_of_monic_of_associated hm (monic_X_sub_C _)
    (hirr.associated_of_dvd (irreducible_X_sub_C _) hdiv)

end Arith

section Linear

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem aeval_glA_eq_zero {A : GL (Fin n) F} {c : Fˣ}
    (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Polynomial.aeval (glA A : Module.End F (Fin n → F)) (X ^ 5 - C (c : F)) = 0 := by
  have h1 : ((glA A : LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) =
      Matrix.toLin' (A : Matrix (Fin n) (Fin n) F) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hA]
  ext v i
  by_cases hi : i = v <;> simp [hi]

theorem exists_central_surjection {G : Type*} [Group G]
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)} (e : G ≃* S) :
    ∃ f : G →* ↥(S.map (LinearFlag.proj n F)), Function.Surjective f ∧
      f.ker ≤ Subgroup.center G := by
  refine ⟨((LinearFlag.proj n F).subgroupMap S).comp e.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ S).comp e.surjective, fun g hg => ?_⟩
  have h1 : LinearFlag.proj n F (e g : Matrix.SpecialLinearGroup (Fin n) F) = 1 :=
    congrArg Subtype.val hg
  have h2 : (e g : Matrix.SpecialLinearGroup (Fin n) F) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) :=
    LinearFlag.scalars_le_center n F (LinearFlag.proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y))

theorem factor_eq_of_component (hF5 : (5 : F) ≠ 0) {A : GL (Fin n) F} {c : Fˣ}
    (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (J' : Subgroup (LinearFlag.projectiveSL n F))
    (hJ' : IsComponentOf J' (fixSubgroup (LinearFlag.conjAut n F A)))
    (hcard : Nat.card (↥J' ⧸ Subgroup.center ↥J') = 60) :
    J' = (specialFactor A (X - C ((c : F) ^ 2))).map (LinearFlag.proj n F) := by
  have hpk : ((5 : ℕ) : F) ≠ 0 := by exact_mod_cast hF5
  obtain ⟨h, hJ⟩ := linear_inner_components hpk hA J' hJ'
  have hsq := squarefree_minpoly_glA hpk hA
  have hmem : h.1.1 ∈ primaryFactors (glA A : Module.End F (Fin n → F)) := h.1.2
  haveI : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite F
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq hmem
  obtain ⟨ψ, hψ, hψk⟩ := exists_central_surjection e
  have hgood := h.2
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End F (Fin n → F)) h.1.1 := by
    rcases hgood with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hperf : commutator (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA A : Module.End F (Fin n → F)) h.1.1)) (AdjoinRoot h.1.1)) = ⊤ := by
    by_cases h3 : 3 ≤ primaryMultiplicity (glA A : Module.End F (Fin n → F)) h.1.1
    · exact (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le h3).commutator_eq_top
    · have h2 : primaryMultiplicity (glA A : Module.End F (Fin n → F)) h.1.1 = 2 := by omega
      have h4 : 4 ≤ Nat.card (AdjoinRoot h.1.1) := by
        rcases hgood with h3' | ⟨-, h4⟩
        · omega
        · exact h4
      rw [h2]
      exact (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top
  subst hJ
  obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hperf ψ hψ hψk
  have hcardSL := (Nat.card_congr eq.toEquiv).trans hcard
  obtain ⟨-, hE⟩ := sl_a5 hm2 hcardSL
  have hE4 : Nat.card (AdjoinRoot h.1.1) = 4 :=
    hE.resolve_right fun h5 => hF5 (five_eq_zero_of_card_five (F := F) h5)
  have hdvd : h.1.1 ∣ X ^ 5 - C (c : F) :=
    ((mem_primaryFactors.1 hmem).2.2).trans (minpoly.dvd F _ (aeval_glA_eq_zero hA))
  have hh : h.1.1 = X - C ((c : F) ^ 2) :=
    eq_X_sub_C_of_card_four (irreducible_of_mem_primaryFactors hmem)
      (monic_of_mem_primaryFactors hmem) hdvd c.ne_zero hE4
  rw [hh]

theorem false_of_linear (hF5 : (5 : F) ≠ 0) {K : Type} [Group K] [Finite K]
    (φ : K ≃* LinearFlag.projectiveSL n F) {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K}
    (D : I1434.Data K Q x J₁ J₂) : False := by
  obtain ⟨g, hg⟩ := LinearFlag.proj_surjective n F (φ x)
  have hg5 : g ^ 5 ∈ LinearFlag.scalars n F := by
    rw [← LinearFlag.proj_eq_one_iff, map_pow, hg, ← map_pow, D.pow_five, map_one]
  obtain ⟨c, -, hc⟩ := hg5
  have hA : (Matrix.SpecialLinearGroup.toGL g) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    ext1
    rw [← map_pow]
    exact hc
  have hβ : LinearFlag.conjAut n F (Matrix.SpecialLinearGroup.toGL g) =
      MulAut.congr φ (MulAut.conj x) := by
    rw [congr_conj_eq, ← hg, LinearFlag.conjAut_toGL]
  have hpk : ((5 : ℕ) : F) ≠ 0 := by exact_mod_cast hF5
  have hlayer : PerfectInLayer (MulAut.congr φ (MulAut.conj x)) := by
    rw [← hβ]
    exact LieSemisimple.perfectInLayer_conjAut hpk hA
  obtain ⟨hc₁, h₁⟩ := five_component_data φ hlayer D.five.comp₁ D.five.quot₁
  obtain ⟨hc₂, h₂⟩ := five_component_data φ hlayer D.five.comp₂ D.five.quot₂
  rw [← hβ] at hc₁ hc₂
  have e₁ := factor_eq_of_component hF5 hA _ hc₁ h₁
  have e₂ := factor_eq_of_component hF5 hA _ hc₂ h₂
  exact D.five.ne (Subgroup.map_injective φ.injective (e₁.trans e₂.symm))

theorem i1434Cl_PSL {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSL n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂) : False := by
  obtain ⟨hℓp, -, -, F, _, _, hcard, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_projectiveSL_of_statedClassicalModel_PSL hm
  exact false_of_linear (five_ne_zero_of_card hℓp hcard hℓ) φ D

end Linear

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
