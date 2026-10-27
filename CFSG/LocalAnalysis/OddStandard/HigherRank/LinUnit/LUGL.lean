module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGL

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
  (ModelIn modelIn_of_component_equiv centralModel_GL_component_two_le)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel)

theorem glFactor_component_model {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {t : ℕ} (ht : 1 ≤ t) {M : Type}
    [Group M] (ρ : M →* GL (Fin t) K) (hρi : Function.Injective ρ)
    (hρc : IsComponent ρ.range) : 2 ≤ t ∧ CentralModel p .PSL t f M := by
  by_cases hsmall : t = 1 ∨ t = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable t K hsmall
    exact absurd hρc (OddInner.not_isComponent_of_isSolvable _)
  obtain ⟨ht2, -, h23⟩ := CatalogueBGeneralLinear.retained_parameters t K ht hsmall
  exact ⟨ht2, (centralModel_GL_component_two_le hp hp2 hf hK ht2 h23 hρc).of_mulEquiv
    (MonoidHom.ofInjective hρi)⟩

theorem glProd_component_model {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {M : Subgroup (GL (Fin r) K × GL (Fin s) K)} (hM : IsComponent M) :
    ∃ k, 2 ≤ k ∧ (k = r ∨ k = s) ∧ CentralModel p .PSL k f M := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hM with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hM h2
    obtain ⟨hk, hm⟩ := glFactor_component_model hp hp2 hf hK hr ρ hρi hρc
    exact ⟨r, hk, Or.inl rfl, hm⟩
  · have h1' : ∀ x ∈ M, (MulEquiv.prodComm x).2 = 1 := h1
    obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hM h1'
    obtain ⟨hk, hm⟩ := glFactor_component_model hp hp2 hf hK hs ρ hρi hρc
    exact ⟨s, hk, Or.inr rfl, hm⟩

theorem glCentralizer_modelIn {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (A : GL (Fin n) K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lambda)
    {M : Subgroup (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))} (hM : IsComponent M) :
    ModelIn p (luLinTuples n f) M := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, hrs, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda h2
        hne hsq hsquare
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    obtain ⟨k, hk, hkrs, hm⟩ := glProd_component_model hp hp2 hf hK hr hs hMe
    exact ⟨.PSL, k, f, Or.inl ⟨k, hk, by omega, rfl⟩,
      hm.of_mulEquiv (M.equivMapOfInjective e.toMonoidHom e.injective)⟩
  · let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hmd := CatalogueBProjectiveQuadratic.matrixDimension_twice A lambda hsq
    rw [Fintype.card_fin] at hmd
    set m := CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq
    have hE : Nat.card (CatalogueBProjectiveQuadratic.extension lambda.val) = p ^ (2 * f) := by
      rw [OddInner.card_extension, hK, ← pow_mul, mul_comm]
    refine modelIn_of_component_equiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq)
      (fun N hN => ?_) hM
    have hm2 : 2 ≤ m := by
      by_contra h1
      have := CatalogueBGeneralLinear.generalLinear_small_solvable m
        (CatalogueBProjectiveQuadratic.extension lambda.val) (Or.inl (by omega))
      exact OddInner.not_isComponent_of_isSolvable N hN
    have hE9 : 9 ≤ p ^ (2 * f) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left (OddInner.three_le_pow hp hp2 hf) 2
    exact ⟨.PSL, m, 2 * f, Or.inr ⟨⟨m, by omega⟩, by rw [show n / 2 = m by omega]⟩,
      centralModel_GL_component_two_le hp hp2 (by omega) hE hm2 (Or.inr (by omega)) hN⟩

end CFSG.OddStandard.HigherRank.LinUnit
