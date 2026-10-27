module

public import Mathlib
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRootInj
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

namespace TrialityDim

@[expose] def Av : Fin 4 → (Fin d4.rank → ℤ) :=
  ![![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1]]

@[expose] def Bv : Fin 4 → (Fin d4.rank → ℤ) :=
  ![![1, 1, 1, 1], ![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 0]]

@[expose] def topR : Fin d4.rank → ℤ := ![1, 1, 2, 1]

theorem isRoot_Av (i : Fin 4) : IsRoot d4 (Av i) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

theorem isRoot_Bv (i : Fin 4) : IsRoot d4 (Bv i) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

theorem isRoot_topR : IsRoot d4 topR := by
  rw [← mem_rootFinset]
  decide +kernel

theorem Av_add_Bv (i : Fin 4) : Av i + Bv i = topR := by
  revert i
  decide +kernel

theorem Av_add_Bv_ne (i j : Fin 4) (h : i ≠ j) : ¬ IsRoot d4 (Av i + Bv j) := by
  rw [← mem_rootFinset]
  revert i j
  decide +kernel

theorem Bv_ne_Av (i j : Fin 4) : Bv i ≠ Av j ∧ Bv i ≠ -Av j := by
  revert i j
  decide +kernel

theorem topR_add_Av (i : Fin 4) : ¬ IsRoot d4 (topR + Av i) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

theorem topR_add_Bv (i : Fin 4) : ¬ IsRoot d4 (topR + Bv i) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

theorem topR_ne_Av (i : Fin 4) : topR ≠ Av i ∧ topR ≠ -Av i := by
  revert i
  decide +kernel

theorem topR_ne_Bv (i : Fin 4) : topR ≠ Bv i ∧ topR ≠ -Bv i := by
  revert i
  decide +kernel

theorem Av0_add_Av_ne (j : Fin 4) (h : j ≠ 0) : ¬ IsRoot d4 (Av 0 + Av j) := by
  rw [← mem_rootFinset]
  revert j
  decide +kernel

theorem Av0_ne_Av (j : Fin 4) (h : j ≠ 0) : Av 0 ≠ Av j ∧ Av 0 ≠ -Av j := by
  revert j
  decide +kernel

theorem rho_Av1 : rho (Av 1) = Av 2 := by decide +kernel
theorem rho_Av2 : rho (Av 2) = Av 3 := by decide +kernel
theorem rho_Bv1 : rho (Bv 1) = Bv 2 := by decide +kernel
theorem rho_Bv2 : rho (Bv 2) = Bv 3 := by decide +kernel
theorem rho_Av0 : rho (Av 0) = Av 0 := by decide +kernel
theorem rho_Bv0 : rho (Bv 0) = Bv 0 := by decide +kernel
theorem rho_topR : rho topR = topR := by decide +kernel

section Algebra

variable {K : Type} {G : Type*} [Group G] (z : K → G)

theorem conj_mul_right [Add K] (hz : ∀ c d, z (c + d) = z c * z d) {h g₁ g₂ : G} {c d : K}
    (e₁ : h * g₁ * h⁻¹ = z c * g₁) (e₂ : h * g₂ * h⁻¹ = z d * g₂)
    (hc : g₁ * z d = z d * g₁) : h * (g₁ * g₂) * h⁻¹ = z (c + d) * (g₁ * g₂) := by
  calc h * (g₁ * g₂) * h⁻¹ = (h * g₁ * h⁻¹) * (h * g₂ * h⁻¹) := by group
    _ = z c * g₁ * (z d * g₂) := by rw [e₁, e₂]
    _ = z c * (g₁ * z d) * g₂ := by simp only [mul_assoc]
    _ = z c * (z d * g₁) * g₂ := by rw [hc]
    _ = z (c + d) * (g₁ * g₂) := by rw [hz]; simp only [mul_assoc]

theorem conj_mul_left [Add K] (hz : ∀ c d, z (c + d) = z c * z d) {h₁ h₂ g : G} {c d : K}
    (e₁ : h₁ * g * h₁⁻¹ = z c * g) (e₂ : h₂ * g * h₂⁻¹ = z d * g)
    (hc : h₁ * z d = z d * h₁) : (h₁ * h₂) * g * (h₁ * h₂)⁻¹ = z (d + c) * g := by
  calc (h₁ * h₂) * g * (h₁ * h₂)⁻¹ = h₁ * (h₂ * g * h₂⁻¹) * h₁⁻¹ := by group
    _ = h₁ * (z d * g) * h₁⁻¹ := by rw [e₂]
    _ = (h₁ * z d * h₁⁻¹) * (h₁ * g * h₁⁻¹) := by group
    _ = z d * (z c * g) := by
        rw [e₁, hc]
        simp only [mul_assoc, mul_inv_cancel_left]
    _ = z (d + c) * g := by rw [hz]; simp only [mul_assoc]

end Algebra

section Comm

variable {K : Type} [Field K]

theorem sign_mul {a b : K} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem xp_comm_unit {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hδ : IsRoot d4 δ) (hne : γ ≠ δ)
    (hne' : γ ≠ -δ) (hs : IsRoot d4 (γ + δ)) :
    ∃ η : K, (η = 1 ∨ η = -1) ∧ ∀ c d : K,
      ⁅xPar (rootOperatorFamily d4) γ c, xPar (rootOperatorFamily d4) δ d⁆ =
        xPar (rootOperatorFamily d4) (γ + δ) (η * c * d) := by
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit d4 (Or.inl rfl) hγ hδ hne hne').1 hs
  have hsg : ∀ θ : Fin d4.rank → ℤ,
      (((rootOperatorFamily d4).pinnedFamilySign θ : ℤ) : K) = 1 ∨
        (((rootOperatorFamily d4).pinnedFamilySign θ : ℤ) : K) = -1 := fun θ => by
    rcases (rootOperatorFamily d4).pinnedFamilySign_eq θ with h | h <;> rw [h] <;> simp
  have hsq : ∀ θ : Fin d4.rank → ℤ,
      (((rootOperatorFamily d4).pinnedFamilySign θ : ℤ) : K) *
        (((rootOperatorFamily d4).pinnedFamilySign θ : ℤ) : K) = 1 :=
    fun θ => (rootOperatorFamily d4).pinnedFamilySign_mul_self K θ
  have hε : ((commConst d4 γ δ (1, 1) : ℤ) : K) = 1 ∨ ((commConst d4 γ δ (1, 1) : ℤ) : K) = -1 := by
    rcases hC with h | h <;> rw [h] <;> simp
  refine ⟨(((rootOperatorFamily d4).pinnedFamilySign (γ + δ) : ℤ) : K) *
      ((commConst d4 γ δ (1, 1) : ℤ) : K) *
      (((rootOperatorFamily d4).pinnedFamilySign γ : ℤ) : K) *
      (((rootOperatorFamily d4).pinnedFamilySign δ : ℤ) : K),
    sign_mul (sign_mul (sign_mul (hsg _) hε) (hsg _)) (hsg _), fun c d => ?_⟩
  apply Subtype.ext
  have h : ((⁅xPar (rootOperatorFamily d4) γ c, xPar (rootOperatorFamily d4) δ d⁆ :
      adjointGroup d4 K) : ModGL d4 K) =
      ⁅((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K),
        ((xPar (rootOperatorFamily d4) δ d : adjointGroup d4 K) : ModGL d4 K)⁆ := rfl
  rw [h, CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ,
    CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hδ,
    CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hs, hF K]
  congr 1
  linear_combination (-(((commConst d4 γ δ (1, 1) : ℤ) : K) *
    (((rootOperatorFamily d4).pinnedFamilySign γ : ℤ) : K) *
    (((rootOperatorFamily d4).pinnedFamilySign δ : ℤ) : K) * c * d)) *
    hsq (γ + δ)

end Comm

section FixedField

variable {K : Type} [Field K] [Finite K]

theorem sigma_cube {q : ℕ} (hK : Nat.card K = q ^ 3) {σ : K →+* K} (hσq : ∀ c, σ c = c ^ q)
    (c : K) : σ (σ (σ c)) = c := by
  have := Fintype.ofFinite K
  rw [hσq, hσq, hσq, ← pow_mul, ← pow_mul]
  have h : q * (q * q) = Fintype.card K := by rw [← Nat.card_eq_fintype_card, hK]; ring
  rw [h]
  exact FiniteField.pow_card c

theorem exists_fixedField {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) {σ : K →+* K}
    (hσq : ∀ c, σ c = c ^ q) :
    ∃ k : Subfield K, Nat.card k = q ∧ ∀ x : K, x ∈ k ↔ σ x = x := by
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 σ.injective
  let σe : K ≃+* K := RingEquiv.ofBijective σ hbij
  have hσe : ∀ x, σe x = σ x := fun x => rfl
  have hmem : ∀ x : K, x ∈ FixedPoints.subfield (Subgroup.zpowers σe) K ↔ σ x = x := by
    intro x
    change x ∈ MulAction.fixedPoints (Subgroup.zpowers σe) K ↔ _
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      have := h ⟨σe, Subgroup.mem_zpowers σe⟩
      exact this
    · intro h g
      have hx : σe x = x := h
      have hst : Subgroup.zpowers σe ≤ MulAction.stabilizer (K ≃+* K) x :=
        (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hx)
      exact hst g.2
  refine ⟨FixedPoints.subfield (Subgroup.zpowers σe) K, ?_, hmem⟩
  have hcard := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf K σe
  have hcube : σe ^ 3 = 1 := by
    ext x
    show σ (σ (σ x)) = x
    exact sigma_cube hK hσq x
  have hord : orderOf σe ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  have hne : orderOf σe ≠ 1 := by
    intro h1
    have hid : σe = 1 := orderOf_eq_one_iff.1 h1
    have hall : ∀ x : K, x ^ q = x := fun x => by
      have := congrArg (fun f : K ≃+* K => f x) hid
      simpa [hσe, hσq] using this
    have := Fintype.ofFinite K
    open Polynomial in
    have hP : (X ^ q - X : K[X]) ≠ 0 := by
      intro h
      have := congrArg (fun P : K[X] => P.coeff q) h
      simp [coeff_X, show (1 : ℕ) ≠ q by omega] at this
    have hroots : ∀ x : K, x ∈ (X ^ q - X : K[X]).roots := fun x => by
      rw [mem_roots hP]
      simp [hall x]
    have hle : Fintype.card K ≤ (X ^ q - X : K[X]).roots.card := by
      have : (Finset.univ : Finset K).val ≤ (X ^ q - X : K[X]).roots :=
        (Multiset.le_iff_subset Finset.univ.nodup).2 fun x _ => hroots x
      simpa using Multiset.card_le_card this
    have hdeg : (X ^ q - X : K[X]).roots.card ≤ q := by
      refine (card_roots' _).trans ?_
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simp; omega)]
      simp
    rw [← Nat.card_eq_fintype_card, hK] at hle
    have hq3 : q ^ 3 ≤ q := hle.trans hdeg
    have h4 : 4 ≤ q * q := by nlinarith
    have h5 : q * 4 ≤ q * (q * q) := Nat.mul_le_mul_left q h4
    rw [show q ^ 3 = q * (q * q) by ring] at hq3
    omega
  have h3 : orderOf σe = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
    · exact absurd h hne
    · exact h
  rw [h3, hK] at hcard
  exact (Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcard).symm

theorem exists_nonroot {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) {l₁ l₂ l₃ : K}
    (h₁ : l₁ = 1 ∨ l₁ = -1) :
    ∃ x : K, l₁ * x + l₂ * x ^ q + l₃ * x ^ (q * q) ≠ 0 := by
  by_contra hcon0
  have hcon : ∀ x : K, l₁ * x + l₂ * x ^ q + l₃ * x ^ (q * q) = 0 := fun x => by
    by_contra h
    exact hcon0 ⟨x, h⟩
  have := Fintype.ofFinite K
  open Polynomial in
  let P : K[X] := C l₁ * X ^ 1 + C l₂ * X ^ q + C l₃ * X ^ (q * q)
  have hdeg : P.natDegree ≤ q * q := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · exact (natDegree_C_mul_X_pow_le l₁ 1).trans (by nlinarith)
    · exact (natDegree_C_mul_X_pow_le l₂ q).trans (by nlinarith)
    · exact natDegree_C_mul_X_pow_le l₃ (q * q)
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ
      (fun x _ => by simpa [P] using hcon x) ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
    nlinarith
  have hc1 : P.coeff 1 = l₁ := by
    have e1 : q ≠ 1 := by omega
    have e2 : q * q ≠ 1 := by nlinarith
    simp [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, e1.symm, e2.symm]
  rw [hP, Polynomial.coeff_zero] at hc1
  rcases h₁ with rfl | rfl <;> simp at hc1

end FixedField

section Structure

variable {K : Type} [Field K] (σ : K →+* K)

theorem commute_z_Av (i : Fin 4) (c c' : K) :
    Commute (xPar (rootOperatorFamily d4) topR c) (xPar (rootOperatorFamily d4) (Av i) c') :=
  commute_xPar isRoot_topR (isRoot_Av i) (topR_ne_Av i).1 (topR_ne_Av i).2 (topR_add_Av i) c c'

theorem commute_z_Bv (i : Fin 4) (c c' : K) :
    Commute (xPar (rootOperatorFamily d4) topR c) (xPar (rootOperatorFamily d4) (Bv i) c') :=
  commute_xPar isRoot_topR (isRoot_Bv i) (topR_ne_Bv i).1 (topR_ne_Bv i).2 (topR_add_Bv i) c c'

theorem conj_diag (i : Fin 4) : ∃ η : K, (η = 1 ∨ η = -1) ∧ ∀ c d : K,
    xPar (rootOperatorFamily d4) (Bv i) d * xPar (rootOperatorFamily d4) (Av i) c *
      (xPar (rootOperatorFamily d4) (Bv i) d)⁻¹ =
    xPar (rootOperatorFamily d4) topR (η * d * c) * xPar (rootOperatorFamily d4) (Av i) c := by
  have hsum : IsRoot d4 (Bv i + Av i) := by rw [add_comm, Av_add_Bv]; exact isRoot_topR
  obtain ⟨η, hη, h⟩ := xp_comm_unit (K := K) (isRoot_Bv i) (isRoot_Av i) (Bv_ne_Av i i).1
    (Bv_ne_Av i i).2 hsum
  refine ⟨η, hη, fun c d => ?_⟩
  have h1 := h d c
  rw [add_comm (Bv i) (Av i), Av_add_Bv, commutatorElement_def] at h1
  calc _ = (xPar (rootOperatorFamily d4) (Bv i) d * xPar (rootOperatorFamily d4) (Av i) c *
        (xPar (rootOperatorFamily d4) (Bv i) d)⁻¹ * (xPar (rootOperatorFamily d4) (Av i) c)⁻¹) *
        xPar (rootOperatorFamily d4) (Av i) c := by group
    _ = _ := by rw [h1]

theorem conj_off (i j : Fin 4) (hij : i ≠ j) (c d : K) :
    xPar (rootOperatorFamily d4) (Bv j) d * xPar (rootOperatorFamily d4) (Av i) c *
      (xPar (rootOperatorFamily d4) (Bv j) d)⁻¹ =
    xPar (rootOperatorFamily d4) topR (0 : K) * xPar (rootOperatorFamily d4) (Av i) c := by
  have hc : Commute (xPar (rootOperatorFamily d4) (Bv j) d)
      (xPar (rootOperatorFamily d4) (Av i) c) := by
    refine commute_xPar (isRoot_Bv j) (isRoot_Av i) (Bv_ne_Av j i).1 (Bv_ne_Av j i).2 ?_ d c
    rw [add_comm]
    exact Av_add_Bv_ne i j hij
  rw [xPar_zero, one_mul, hc.eq, mul_inv_cancel_right]

@[expose] noncomputable def Aelt (b s : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (Av 0) b * xOrbit σ (Av 1) s

@[expose] noncomputable def Belt (e t : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (Bv 0) e * xOrbit σ (Bv 1) t

theorem xOrbit_Av (s : K) : xOrbit σ (Av 1) s =
    xPar (rootOperatorFamily d4) (Av 1) s *
      xPar (rootOperatorFamily d4) (Av 2) (twistSign σ (Av 1) * σ s) *
      xPar (rootOperatorFamily d4) (Av 3)
        (twistSign σ (Av 1) * twistSign σ (Av 2) * σ (σ s)) := by
  rw [xOrbit, rho_Av1, rho_Av2]

theorem xOrbit_Bv (t : K) : xOrbit σ (Bv 1) t =
    xPar (rootOperatorFamily d4) (Bv 1) t *
      xPar (rootOperatorFamily d4) (Bv 2) (twistSign σ (Bv 1) * σ t) *
      xPar (rootOperatorFamily d4) (Bv 3)
        (twistSign σ (Bv 1) * twistSign σ (Bv 2) * σ (σ t)) := by
  rw [xOrbit, rho_Bv1, rho_Bv2]

theorem conj_Belt_Aelt : ∃ l₀ l₁ l₂ l₃ : K, (l₀ = 1 ∨ l₀ = -1) ∧ (l₁ = 1 ∨ l₁ = -1) ∧
    (l₂ = 1 ∨ l₂ = -1) ∧ (l₃ = 1 ∨ l₃ = -1) ∧ ∀ b s e t : K,
    Belt σ e t * Aelt σ b s * (Belt σ e t)⁻¹ =
      xPar (rootOperatorFamily d4) topR
        (l₀ * e * b + l₁ * t * s + l₂ * σ (t * s) + l₃ * σ (σ (t * s))) * Aelt σ b s := by
  choose eta heta hconj using fun i : Fin 4 => conj_diag (K := K) i
  have hz : ∀ c d : K, xPar (rootOperatorFamily d4) topR (c + d) =
      xPar (rootOperatorFamily d4) topR c * xPar (rootOperatorFamily d4) topR d :=
    fun c d => xPar_add _ c d
  have base : ∀ (i j : Fin 4) (c d : K),
      xPar (rootOperatorFamily d4) (Bv j) d * xPar (rootOperatorFamily d4) (Av i) c *
        (xPar (rootOperatorFamily d4) (Bv j) d)⁻¹ =
      xPar (rootOperatorFamily d4) topR (if i = j then eta i * d * c else 0) *
        xPar (rootOperatorFamily d4) (Av i) c := by
    intro i j c d
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte]
      exact hconj i c d
    · simp only [h, ↓reduceIte]
      exact conj_off i j h c d
  set e1 := twistSign σ (Av 1) with he1
  set e2 := twistSign σ (Av 2) with he2
  set f1 := twistSign σ (Bv 1) with hf1
  set f2 := twistSign σ (Bv 2) with hf2
  have hA : ∀ (j : Fin 4) (b s d : K),
      xPar (rootOperatorFamily d4) (Bv j) d * Aelt σ b s *
        (xPar (rootOperatorFamily d4) (Bv j) d)⁻¹ =
      xPar (rootOperatorFamily d4) topR
        ((if (0 : Fin 4) = j then eta 0 * d * b else 0) +
          (((if (1 : Fin 4) = j then eta 1 * d * s else 0) +
            (if (2 : Fin 4) = j then eta 2 * d * (e1 * σ s) else 0)) +
            (if (3 : Fin 4) = j then eta 3 * d * (e1 * e2 * σ (σ s)) else 0))) *
        Aelt σ b s := by
    intro j b s d
    rw [Aelt, xOrbit_Av]
    have h0 := base 0 j b d
    have h1 := base 1 j s d
    have h2 := base 2 j (e1 * σ s) d
    have h3 := base 3 j (e1 * e2 * σ (σ s)) d
    have c12 := conj_mul_right (z := xPar (rootOperatorFamily d4) topR) hz h1 h2
      (commute_z_Av 1 _ _).symm.eq
    have c123 := conj_mul_right (z := xPar (rootOperatorFamily d4) topR) hz c12 h3
      (Commute.mul_left (commute_z_Av 1 _ _).symm (commute_z_Av 2 _ _).symm).eq
    exact conj_mul_right (z := xPar (rootOperatorFamily d4) topR) hz h0 c123
      (commute_z_Av 0 _ _).symm.eq
  refine ⟨eta 0, eta 1, eta 2 * f1 * e1, eta 3 * f1 * f2 * e1 * e2, heta 0, heta 1,
    sign_mul (sign_mul (heta 2) (twistSign_eq_one_or σ _)) (twistSign_eq_one_or σ _),
    sign_mul (sign_mul (sign_mul (sign_mul (heta 3) (twistSign_eq_one_or σ _))
      (twistSign_eq_one_or σ _)) (twistSign_eq_one_or σ _)) (twistSign_eq_one_or σ _),
    fun b s e t => ?_⟩
  rw [Belt, xOrbit_Bv]
  have k0 := hA 0 b s e
  have k1 := hA 1 b s t
  have k2 := hA 2 b s (f1 * σ t)
  have k3 := hA 3 b s (f1 * f2 * σ (σ t))
  have d12 := conj_mul_left (z := xPar (rootOperatorFamily d4) topR) hz k1 k2
    (commute_z_Bv 1 _ _).symm.eq
  have d123 := conj_mul_left (z := xPar (rootOperatorFamily d4) topR) hz d12 k3
    (Commute.mul_left (commute_z_Bv 1 _ _).symm (commute_z_Bv 2 _ _).symm).eq
  have d0123 := conj_mul_left (z := xPar (rootOperatorFamily d4) topR) hz k0 d123
    (commute_z_Bv 0 _ _).symm.eq
  convert d0123 using 3
  simp only [Fin.isValue, map_mul, ↓reduceIte, Fin.reduceEq]
  ring

theorem rho_Av1_ne : rho (Av 1) ≠ Av 1 := by rw [rho_Av1]; decide +kernel

theorem rho_Bv1_ne : rho (Bv 1) ≠ Bv 1 := by rw [rho_Bv1]; decide +kernel

theorem commute_Av0_xOrbit (b' s : K) :
    Commute (xPar (rootOperatorFamily d4) (Av 0) b') (xOrbit σ (Av 1) s) := by
  rw [xOrbit_Av]
  have hc : ∀ j : Fin 4, j ≠ 0 → ∀ c : K,
      Commute (xPar (rootOperatorFamily d4) (Av 0) b') (xPar (rootOperatorFamily d4) (Av j) c) :=
    fun j hj c => commute_xPar (isRoot_Av 0) (isRoot_Av j) (Av0_ne_Av j hj).1 (Av0_ne_Av j hj).2
      (Av0_add_Av_ne j hj) b' c
  exact (((hc 1 (by decide) _).mul_right (hc 2 (by decide) _)).mul_right (hc 3 (by decide) _))

theorem Aelt_add (b b' s s' : K) :
    Aelt σ (b + b') (s + s') = Aelt σ b s * Aelt σ b' s' := by
  rw [Aelt, Aelt, Aelt, xPar_add, xOrbit_add σ (isRoot_Av 1) rho_Av1_ne]
  have hc := commute_Av0_xOrbit σ b' s
  calc _ = xPar (rootOperatorFamily d4) (Av 0) b *
        (xPar (rootOperatorFamily d4) (Av 0) b' * xOrbit σ (Av 1) s) * xOrbit σ (Av 1) s' := by
        simp only [mul_assoc]
    _ = xPar (rootOperatorFamily d4) (Av 0) b *
        (xOrbit σ (Av 1) s * xPar (rootOperatorFamily d4) (Av 0) b') * xOrbit σ (Av 1) s' := by
        rw [hc.eq]
    _ = _ := by simp only [mul_assoc]

variable {σ}

theorem Aelt_mem (hσ : ∀ c, σ (σ (σ c)) = c) {b : K} (hb : σ b = b) (s : K) :
    Aelt σ b s ∈ twistedGroup σ := by
  refine Subgroup.mul_mem _ ?_ ?_
  · exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_Av 0))
      (xPar_mem_of_fixed hσ (isRoot_Av 0) rho_Av0 hb)
  · exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_Av 1))
      (xOrbit_mem hσ (isRoot_Av 1) rho_Av1_ne s)

theorem Belt_mem (hσ : ∀ c, σ (σ (σ c)) = c) {e : K} (he : σ e = e) (t : K) :
    Belt σ e t ∈ twistedGroup σ := by
  refine Subgroup.mul_mem _ ?_ ?_
  · exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_Bv 0))
      (xPar_mem_of_fixed hσ (isRoot_Bv 0) rho_Bv0 he)
  · exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_Bv 1))
      (xOrbit_mem hσ (isRoot_Bv 1) rho_Bv1_ne t)

theorem z_mem (hσ : ∀ c, σ (σ (σ c)) = c) {c : K} (hc : σ c = c) :
    xPar (rootOperatorFamily d4) topR c ∈ twistedGroup σ :=
  twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj isRoot_topR)
    (xPar_mem_of_fixed hσ isRoot_topR rho_topR hc)

theorem fixed_of_z_mem (hσ : ∀ c, σ (σ (σ c)) = c) {c : K}
    (h : xPar (rootOperatorFamily d4) topR c ∈ twistedGroup σ) : σ c = c := by
  have h1 := twistedGroup_le_twistFixed σ h
  have h2 : twistC .D4 K σ (xPar (rootOperatorFamily d4) topR c) =
      xPar (rootOperatorFamily d4) topR c := h1
  rw [twistC_xPar σ isRoot_topR, rho_topR, twistSign_of_rho_eq σ hσ isRoot_topR rho_topR,
    one_mul] at h2
  exact xPar_injective isRoot_topR h2

theorem commute_z_Aelt (c b s : K) :
    Commute (xPar (rootOperatorFamily d4) topR c) (Aelt σ b s) := by
  rw [Aelt]
  refine Commute.mul_right (commute_z_Av 0 _ _) ?_
  rw [xOrbit_Av]
  exact ((commute_z_Av 1 _ _).mul_right (commute_z_Av 2 _ _)).mul_right (commute_z_Av 3 _ _)

theorem commute_z_Belt (c e t : K) :
    Commute (xPar (rootOperatorFamily d4) topR c) (Belt σ e t) := by
  rw [Belt]
  refine Commute.mul_right (commute_z_Bv 0 _ _) ?_
  rw [xOrbit_Bv]
  exact ((commute_z_Bv 1 _ _).mul_right (commute_z_Bv 2 _ _)).mul_right (commute_z_Bv 3 _ _)

theorem fixed_of_conj (hσ : ∀ c, σ (σ (σ c)) = c) {b s e t γ : K} (hb : σ b = b) (he : σ e = e)
    (h : Belt σ e t * Aelt σ b s * (Belt σ e t)⁻¹ =
      xPar (rootOperatorFamily d4) topR γ * Aelt σ b s) : σ γ = γ := by
  refine fixed_of_z_mem hσ ?_
  have e1 : xPar (rootOperatorFamily d4) topR γ =
      Belt σ e t * Aelt σ b s * (Belt σ e t)⁻¹ * (Aelt σ b s)⁻¹ := by
    rw [h, mul_inv_cancel_right]
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Belt_mem hσ he t)
    (Aelt_mem hσ hb s)) (Subgroup.inv_mem _ (Belt_mem hσ he t)))
    (Subgroup.inv_mem _ (Aelt_mem hσ hb s))

end Structure

end TrialityDim

open TrialityDim in
theorem two_pow_le_card_of_twistedGroupD4 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (σ : K →+* K)
    (hσq : ∀ c, σ c = c ^ q) {L : Subgroup (MulAut W)}
    (π : ↥L →* ↥(twistedGroup σ)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * (q ^ 4 / (p - 1))) ≤ Nat.card W := by
  have hσ3 := sigma_cube hK hσq
  obtain ⟨k, hkcard, hkmem⟩ := exists_fixedField hq hK hσq
  obtain ⟨l₀, l₁, l₂, l₃, hl₀, hl₁, hl₂, hl₃, hcomm⟩ := conj_Belt_Aelt σ
  have hmk : ∀ x : k, σ (x : K) = (x : K) := fun x => (hkmem x).1 x.2
  have hσc : ∀ (c : k) (x : K), σ ((c : K) * x) = (c : K) * σ x := fun c x => by
    rw [map_mul, hmk c]
  have hsm : ∀ (c : k) (x : K), c • x = (c : K) * x := fun c x => rfl
  let γ : k × K → k × K → K := fun u v =>
    l₀ * (v.1 : K) * (u.1 : K) + l₁ * v.2 * u.2 + l₂ * σ (v.2 * u.2) + l₃ * σ (σ (v.2 * u.2))
  have hγ : ∀ u v, σ (γ u v) = γ u v := fun u v =>
    fixed_of_conj hσ3 (hmk u.1) (hmk v.1) (hcomm (u.1 : K) u.2 (v.1 : K) v.2)
  let β : (k × K) →ₗ[k] (k × K) →ₗ[k] k :=
    LinearMap.mk₂ k (fun u v => (⟨γ u v, (hkmem _).2 (hγ u v)⟩ : k))
      (fun u u' v => by
        apply Subtype.ext
        simp only [γ, Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, mul_add, map_add]
        ring)
      (fun c u v => by
        apply Subtype.ext
        have e : v.2 * ((c : K) * u.2) = (c : K) * (v.2 * u.2) := by ring
        simp only [γ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hsm, Subfield.coe_mul, e, hσc]
        ring)
      (fun u v v' => by
        apply Subtype.ext
        simp only [γ, Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, add_mul, map_add]
        ring)
      (fun c u v => by
        apply Subtype.ext
        have e : ((c : K) * v.2) * u.2 = (c : K) * (v.2 * u.2) := by ring
        simp only [γ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hsm, Subfield.coe_mul, e, hσc]
        ring)
  have hne : ∀ l : K, (l = 1 ∨ l = -1) → l ≠ 0 := fun l hl => by
    rcases hl with rfl | rfl <;> simp
  have hβapp : ∀ u v, ((β u v : k) : K) = γ u v := fun u v => rfl
  have hnr : ∃ x : K, l₁ * x + l₂ * σ x + l₃ * σ (σ x) ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_nonroot hq hK (l₂ := l₂) (l₃ := l₃) hl₁
    exact ⟨x, by simp only [hσq, ← pow_mul]; exact hx⟩
  have hβ : ∀ v : k × K, v ≠ 0 → ∃ u, β u v ≠ 0 := by
    intro v hv
    by_cases h1 : v.1 = 0
    · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      obtain ⟨x, hx⟩ := hnr
      refine ⟨(0, x / v.2), fun h => hx ?_⟩
      have h3 := congrArg Subtype.val h
      rw [hβapp] at h3
      have h4 : v.2 * (x / v.2) = x := by field_simp
      have h5 : l₁ * v.2 * (x / v.2) = l₁ * x := by rw [mul_assoc, h4]
      simp only [γ, Subfield.coe_zero, mul_zero, zero_add] at h3
      rw [h5, h4] at h3
      exact h3
    · refine ⟨(1, 0), fun h => ?_⟩
      have h3 := congrArg Subtype.val h
      rw [hβapp] at h3
      simp only [γ, Subfield.coe_one, mul_one, mul_zero, map_zero, add_zero] at h3
      exact mul_ne_zero (hne _ hl₀) (fun h5 => h1 (Subtype.ext h5)) h3
  have hβl : ∀ u : k × K, u ≠ 0 → ∃ v, β u v ≠ 0 := by
    intro u hu
    by_cases h1 : u.1 = 0
    · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
      obtain ⟨x, hx⟩ := hnr
      refine ⟨(0, x / u.2), fun h => hx ?_⟩
      have h3 := congrArg Subtype.val h
      rw [hβapp] at h3
      have h4 : x / u.2 * u.2 = x := by field_simp
      have h5 : l₁ * (x / u.2) * u.2 = l₁ * x := by rw [mul_assoc, h4]
      simp only [γ, Subfield.coe_zero, mul_zero, zero_mul, zero_add] at h3
      rw [h5, h4] at h3
      exact h3
    · refine ⟨(1, 0), fun h => ?_⟩
      have h3 := congrArg Subtype.val h
      rw [hβapp] at h3
      simp only [γ, Subfield.coe_one, mul_one, mul_zero, zero_mul, map_zero, add_zero] at h3
      exact mul_ne_zero (hne _ hl₀) (fun h5 => h1 (Subtype.ext h5)) h3
  let z : Multiplicative k →* ↥(twistedGroup σ) :=
    MonoidHom.mk' (fun c => ⟨xPar (rootOperatorFamily d4) topR ((c.toAdd : k) : K),
      z_mem hσ3 (hmk c.toAdd)⟩)
      (fun c d => Subtype.ext (by
        change xPar (rootOperatorFamily d4) topR (((c * d).toAdd : k) : K) = _
        rw [toAdd_mul, AddMemClass.coe_add]
        exact xPar_add _ _ _))
  let a : Multiplicative (k × K) →* ↥(twistedGroup σ) :=
    MonoidHom.mk' (fun u => ⟨Aelt σ ((u.toAdd.1 : k) : K) u.toAdd.2, Aelt_mem hσ3 (hmk _) _⟩)
      (fun u v => Subtype.ext (by
        change Aelt σ (((u * v).toAdd.1 : k) : K) (u * v).toAdd.2 = _
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, AddMemClass.coe_add]
        exact Aelt_add σ _ _ _ _))
  let b : k × K → ↥(twistedGroup σ) := fun v =>
    ⟨Belt σ (v.1 : K) v.2, Belt_mem hσ3 (hmk _) _⟩
  have hz : ∀ c : k, z (Multiplicative.ofAdd c) = 1 → c = 0 := by
    intro c h
    have h1 : xPar (rootOperatorFamily d4) topR (c : K) = 1 := congrArg Subtype.val h
    have h2 := xPar_injective isRoot_topR (h1.trans (xPar_zero _).symm)
    exact Subtype.ext h2
  have hza : ∀ (c : Multiplicative k) (u : Multiplicative (k × K)), z c * a u = a u * z c :=
    fun c u => Subtype.ext (commute_z_Aelt (σ := σ) _ _ _).eq
  have hbz : ∀ (c : Multiplicative k) (v : k × K), b v * z c = z c * b v :=
    fun c v => Subtype.ext (commute_z_Belt (σ := σ) _ _ _).eq.symm
  have hab : ∀ (u v : k × K), b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)) := by
    intro u v
    apply Subtype.ext
    change Belt σ (v.1 : K) v.2 * Aelt σ (u.1 : K) u.2 * (Belt σ (v.1 : K) v.2)⁻¹ =
      Aelt σ (u.1 : K) u.2 * xPar (rootOperatorFamily d4) topR ((β u v : k) : K)
    rw [hcomm (u.1 : K) u.2 (v.1 : K) v.2, hβapp]
    exact (commute_z_Aelt (σ := σ) _ _ _).eq
  have hcardV : Nat.card (k × K) = q ^ 4 := by
    rw [Nat.card_prod, hkcard, hK]; ring
  have key := FFToolkit.two_pow_le_card_of_heis_root_of_inj_one hW hp2 π hπ hker hZ (K := k)
    (V := k × K) z a b β hβ hβl hz hza hab hbz
  rwa [hcardV] at key

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
