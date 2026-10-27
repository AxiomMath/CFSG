module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIClassicalConfig
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelectorSymmetry
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaHigherRank

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoHypIIY CFSG.ComponentClassification.RankTwoHypIIClassical
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

section Generic

variable {W : Type*} [Group W] [Finite W] {X E M : Subgroup W}

theorem config_le_centralizer_of_perfect (h : HypIIConfig X E M) {α : W} (hαE : α ∈ E)
    (hα1 : α ≠ 1) {N : Subgroup W} (hNX : N ≤ X ⊓ centralizer ({α} : Set W))
    (hNp : ⁅N, N⁆ = N) (hN : TwoNilpotentCentral N) (hEN : E ≤ normalizer (N : Set W)) :
    E ≤ centralizer (N : Set W) := by
  have hNΓ : N ≤ gammaE X E := by
    have hND : N ≤ centDer X α :=
      calc N = ⁅N, N⁆ := hNp.symm
        _ ≤ centDer X α := commutator_mono hNX hNX
    exact hND.trans (le_iSup₂_of_le α hαE (le_iSup_of_le hα1 le_rfl))
  exact le_centralizer_of_isTwoNilpotent_nE h.isTwoNilpotent_nE hNΓ hEN hNp hN

theorem config_not_le_zpowers (h : HypIIConfig X E M) {α : W} (hα : α ^ 2 = 1) :
    ¬ E ≤ zpowers α := by
  intro hle
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  have := orderOf_le_of_pow_eq_one two_pos hα
  have := h.four_le_card
  omega

end Generic

variable {K : Type} [Field K] [Finite K] {n : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}

theorem finite_mulAut_PQ : Finite (MulAut (matrixProjectiveDerived Q)) :=
  OmegaRadical.finite_mulAut_matrixProjectiveDerived Q

theorem isometryGroup_simple {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate) {f r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hr : 3 ≤ r) (hdim : Module.finrank K V = 2 * r) :
    IsSimpleGroup (CatalogueBAlternatingIsometry.isometryGroup B) ∧
      Even (Nat.card (CatalogueBAlternatingIsometry.isometryGroup B)) := by
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdim
  have hk2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK; omega
    · exact h0
  have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    by_cases hf1 : f = 1
    · exact Or.inr (Or.inr ⟨by rw [hK, hf1]; norm_num, hr⟩)
    · left; right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsP : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega) hcond
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := CFSG.Assembly.LowTwoRank.StatedSp r K) hK (by omega) ⟨MulEquiv.refl _⟩
  have hsSp : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedSp r K) := eProj.symm.isSimpleGroup
  refine ⟨eSp.isSimpleGroup, ?_⟩
  rw [Nat.card_congr eSp.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  refine Even.mul_right ?_ _
  rw [hK, ← pow_mul]
  exact (Nat.even_pow' (by positivity)).mpr even_two

variable [CharP K 2]

section Regular

variable (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)
include hQ hT hE

omit [Finite K] in
theorem right_eq_one_of_mem_inner (hn : 1 ≤ n) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q)
    (hSX : matrixProjectiveConjugationHom Q S ∈ inner (matrixProjectiveDerived Q)) :
    S.val.right = 1 := by
  obtain ⟨y, hy⟩ := hSX
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have hκ := kappa_derived_eq_conj g
  have hmem : matrixDerivedInclusion Q g ∈ unitMultiplierPairs Q :=
    inclusion_mem_unitMultiplierPairs _
  have heq := kappa_eq_of_unit hQ hT hE (by omega) hS hmem (by rw [hκ, hy])
  rw [heq, matrixDerivedInclusion_val]
  rfl

omit [Finite K] in
theorem kappa_ne_one (hn : 1 ≤ n) {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hS1 : S ≠ 1) : matrixProjectiveConjugationHom Q S ≠ 1 := fun h1 =>
  hS1 (kappa_eq_of_unit hQ hT hE (by omega) hS (one_mem _) (by rw [h1, map_one]))

variable {M E : Subgroup (MulAut (matrixProjectiveDerived Q))}

theorem false_of_field {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hSE : matrixProjectiveConjugationHom Q S ∈ E) (hright : S.val.right ≠ 1) : False := by
  have := finite_mulAut_PQ (Q := Q)
  set α := matrixProjectiveConjugationHom Q S with hα
  have hS1 : S ≠ 1 := fun h1 => hright (by rw [h1]; rfl)
  have hα1 : α ≠ 1 := kappa_ne_one hQ hT hE (by omega) hS hS1
  have hα2 : α ^ 2 = 1 := h.elemAbelian.2 α hSE
  have hord : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hαX : α ∉ inner (matrixProjectiveDerived Q) := fun hX =>
    hright (right_eq_one_of_mem_inner hQ hT hE (by omega) hS hX)
  obtain ⟨-, -, hsimp, heven, ext, -, -, hinj, hinner, hle, hnorm, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α (hEQ hSE) hord S hS rfl hright
  set N := (extKappa Q ext).range with hNdef
  have eN : pairDescentDerived hS ≃* N := MonoidHom.ofInjective hinj
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hNe : Even (Nat.card N) := by rw [← Nat.card_congr eN.toEquiv]; exact heven
  have hEC : E ≤ matrixProjectiveImage Q ⊓ centralizer {α} := fun e he =>
    ⟨hEQ he, mem_centralizer_singleton_iff.mpr (h.commute he hSE)⟩
  have hNnorm : matrixProjectiveImage Q ⊓ centralizer {α} ≤ normalizer (N : Set _) :=
    (normal_subgroupOf_iff_le_normalizer hle).mp hnorm
  have hnc : ¬ ∀ a b : N, a * b = b * a := by
    intro hcomm
    have hNC : N ≤ centralizer (N : Set _) := fun y hy =>
      mem_centralizer_iff.mpr fun z hz => congrArg Subtype.val (hcomm ⟨z, hz⟩ ⟨y, hy⟩)
    have hNz : N ≤ zpowers α := by
      rw [← hcent]
      exact le_inf hle hNC
    have hbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases eq_one_or_eq_of_mem_zpowers hα2 (hNz hy) with h1 | h1
      · exact (mem_bot).mpr h1
      · exact absurd (h1 ▸ hinner hy) hαX
    have h1 : Nat.card N = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1] at hNe
    exact absurd hNe (by decide)
  have hNp : ⁅N, N⁆ = N := commutator_eq_self_of_isSimpleGroup hNs hnc
  have hEN := config_le_centralizer_of_perfect h hSE hα1
    (le_inf hinner (hle.trans inf_le_right)) hNp
    (twoNilpotentCentral_of_isSimpleGroup hNs hNp hNe) (hEC.trans hNnorm)
  apply config_not_le_zpowers h hα2
  rw [← hcent]
  exact le_inf hEC hEN

theorem symmetryAut_not_mem_inner (hn : 1 ≤ n) {v : Fin (2 * n) → K} (hv : Q v = 1) :
    symmetryAut Q v ∉ inner (matrixProjectiveDerived Q) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [← kappa_derived_eq_conj] at hy
  have h1 := kappa_inclusion_injective hQ hT hE (by omega) (a₁ := Subgroup.inclusion
    (matrixDerived_le_isometries Q) g) (a₂ := symmetryIsometry Q v) hy
  apply EvenOrthSelector.symmetryGL_not_mem_matrixDerived hQ hT hE hv
  have h2 : ((Subgroup.inclusion (matrixDerived_le_isometries Q) g : matrixIsometries Q) :
      GL (Fin (2 * n)) K) = symmetryGL Q v := congrArg Subtype.val h1
  rw [← h2]
  exact g.2

theorem mem_zpowers_of_commute (hn : 2 ≤ n) {v : Fin (2 * n) → K} (hv : Q v = 1)
    {e : MulAut (matrixProjectiveDerived Q)} (heQ : e ∈ matrixProjectiveImage Q)
    (heα : e * symmetryAut Q v = symmetryAut Q v * e)
    (heN : e ∈ centralizer ((inner (matrixProjectiveDerived Q) ⊓
      centralizer {symmetryAut Q v} : Subgroup _) : Set (MulAut (matrixProjectiveDerived Q)))) :
    e ∈ zpowers (symmetryAut Q v) := by
  have hd : 1 ≤ 2 * n := by omega
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep heQ
  have hN : ∀ g : matrixIsometries Q, (g : GL (Fin (2 * n)) K) ∈ derivedSymmetryCentralizer Q v →
      Commute (matrixProjectiveConjugationHom Q S)
        (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g)) := by
    intro g hg
    have hmem : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) ∈
        inner (matrixProjectiveDerived Q) ⊓ centralizer {symmetryAut Q v} := by
      rw [← EvenOrthSelector.range_symKappa hQ hT hE hd v]
      exact ⟨⟨g, hg⟩, rfl⟩
    exact ((mem_centralizer_iff.mp heN) _ hmem).symm
  rcases eq_one_or_eq_of_commute hQ hT hE (by omega) hv hS heα hN with h1 | h1
  · rw [h1, map_one]
    exact one_mem _
  · rw [h1]
    exact mem_zpowers _

variable {M E : Subgroup (MulAut (matrixProjectiveDerived Q))} in
theorem false_of_symmetry {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (h : HypIIConfig (inner (matrixProjectiveDerived Q)) E M) (hEQ : E ≤ matrixProjectiveImage Q)
    {v : Fin (2 * n) → K} (hv : Q v = 1) (hvE : symmetryAut Q v ∈ E) : False := by
  have := finite_mulAut_PQ (Q := Q)
  have hd : 1 ≤ 2 * n := by omega
  set α := symmetryAut Q v with hαdef
  set N := inner (matrixProjectiveDerived Q) ⊓ centralizer {α} with hNdef
  have hα2 : α ^ 2 = 1 := symmetryAut_sq Q v
  have hαX : α ∉ inner (matrixProjectiveDerived Q) :=
    symmetryAut_not_mem_inner hQ hT hE (by omega) hv
  have hα1 : α ≠ 1 := fun h1 => hαX (h1 ▸ one_mem _)
  have hinj : Function.Injective (EvenOrthSelector.symKappa Q v) :=
    (kappa_inclusion_injective hQ hT hE hd).comp (Subgroup.inclusion_injective _)
  obtain ⟨eB⟩ := EvenOrthSelector.exists_derivedSymmetryEquiv hQ hT hE hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hdim : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by
    have := finrank_vQuot hQ hv
    omega
  obtain ⟨hsI, heI⟩ := isometryGroup_simple (vQuotForm_isAlt Q v)
    (vQuotForm_nondegenerate hQ hv0) hK (by omega : 3 ≤ n - 1) hdim
  have eN : CatalogueBAlternatingIsometry.isometryGroup (vQuotForm Q v) ≃* N :=
    ((eB.trans (bilinIsometryGroupEquiv _)).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr (EvenOrthSelector.range_symKappa hQ hT hE hd v))
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hNe : Even (Nat.card N) := by rw [← Nat.card_congr eN.toEquiv]; exact heI
  have hinnerQ := matrixProjective_inner_le_image Q
  have hnc : ¬ ∀ a b : N, a * b = b * a := by
    intro hcomm
    have hbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyN : y ∈ centralizer (N : Set _) :=
        mem_centralizer_iff.mpr fun z hz => congrArg Subtype.val (hcomm ⟨z, hz⟩ ⟨y, hy⟩)
      rcases eq_one_or_eq_of_mem_zpowers hα2 (mem_zpowers_of_commute hQ hT hE (by omega) hv
          (hinnerQ hy.1) (mem_centralizer_singleton_iff.mp hy.2) hyN) with h1 | h1
      · exact (mem_bot).mpr h1
      · exact absurd (h1 ▸ hy.1) hαX
    have := hNs.toNontrivial
    rw [hbot] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  have hNp : ⁅N, N⁆ = N := commutator_eq_self_of_isSimpleGroup hNs hnc
  have hEN : E ≤ normalizer (N : Set _) := by
    intro e he
    have heC : e ∈ centralizer ({α} : Set _) :=
      mem_centralizer_singleton_iff.mpr (h.commute he hvE)
    have hXn := OuterAutomorphisms.inner_normal (matrixProjectiveDerived Q)
    rw [mem_normalizer_iff]
    intro y
    set C := centralizer ({α} : Set (MulAut (matrixProjectiveDerived Q)))
    constructor
    · intro hy
      obtain ⟨hyX, hyα⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr ⟨hXn.conj_mem y hyX e, C.mul_mem (C.mul_mem heC hyα)
        (C.inv_mem heC)⟩
    · intro hy
      obtain ⟨hyX, hyα⟩ := Subgroup.mem_inf.mp hy
      have key : y = e⁻¹ * (e * y * e⁻¹) * e := by group
      rw [key]
      refine Subgroup.mem_inf.mpr ⟨?_, C.mul_mem (C.mul_mem (C.inv_mem heC) hyα) heC⟩
      have := hXn.conj_mem _ hyX e⁻¹
      simpa using this
  have hEC := config_le_centralizer_of_perfect h hvE hα1 le_rfl hNp
    (twoNilpotentCentral_of_isSimpleGroup hNs hNp hNe) hEN
  refine config_not_le_zpowers h hα2 fun e he => ?_
  exact mem_zpowers_of_commute hQ hT hE (by omega) hv (hEQ he) (h.commute he hvE) (hEC he)

end Regular

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal
