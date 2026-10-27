module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrOrth
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrUnit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLTools
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL CFSG.LieType.BorelTits

namespace Gr

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_graph {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    (A : GL (Fin n) K) (σ : K ≃+* K)
    (hsq : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1)
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (conjAut n K A * fieldAut n K σ * dualAut n K) =
      conjAut n K A * fieldAut n K σ * dualAut n K * r)
    (hRc : ∀ s, (conjAut n K A * fieldAut n K σ * dualAut n K) s = s → Odd (orderOf s) →
      ∀ r ∈ R, MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  by_cases hσ : σ = 1
  · subst hσ
    have ht : conjAut n K A * fieldAut n K 1 * dualAut n K = conjAut n K A * dualAut n K := by
      rw [map_one, mul_one]
    rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq hn A
        hsq with hA | hA
    · have hR := inv_transpose_of_transpose_eq A hA
      obtain ⟨P, w, hw, hP⟩ := exists_orth_normal_form hK hn A⁻¹ hR
      set H := P⁻¹ with hH
      have hHA : H * A * GeneralLinearGroup.inverseTranspose H⁻¹ = (diagGL hw.1)⁻¹ := by
        have hT : CatalogueBGraphForm.glTranspose n K P * A⁻¹ * P = diagGL hw.1 := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, coe_diagGL]
          exact hP
        have hT' : CatalogueBGraphForm.glTranspose n K P =
            (GeneralLinearGroup.inverseTranspose P)⁻¹ := rfl
        rw [← hT, hT', hH, inv_inv]
        group
      set t' := conjAut n K (diagGL hw.1)⁻¹ * dualAut n K with ht'
      have htt : conjAut n K A * fieldAut n K 1 * dualAut n K =
          (conjAut n K H)⁻¹ * t' * ((conjAut n K H)⁻¹)⁻¹ := by
        have h1 := conjAut_mul_conjAut_dualAut_mul_inv H A
        rw [hHA, ← ht'] at h1
        rw [ht, inv_inv, ← h1]
        group
      rw [htt] at hRi hRc
      refine eq_one_of_conj (conjAut n K H)⁻¹ t' (fun R₀ h₁ h₂ h₃ => ?_) hRodd hRi hRc
      by_cases hexc : Nat.card K = 3 ∧ n ≤ 4
      · exact eq_one_orth_three hexc.1 hn hexc.2 hw h₁ h₂ h₃
      · have hRsym : ((diagGL hw.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = diagGL hw.1 := by
          rw [coe_diagGL, diagonal_transpose]
        exact eq_one_orth_data hK hn hinj hw (orthComponentData hK hn _ hRsym hexc) h₁ h₂ h₃
    · rw [ht] at hRi hRc
      exact eq_one_symplectic hK hn hinj hA hRodd hRi hRc
  · obtain ⟨hfe, hσp, H, hH⟩ :=
      odd_linear_graph_field_involution_conjugacy hp hf hKc hn A σ hσ hsq
    obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
    have hKe : Nat.card K = (p ^ e) ^ 2 := by rw [hKc, he, ← pow_mul, mul_comm]
    have hσe : σ = unitaryInvolution K p e := by
      ext x
      rw [hσp, unitaryInvolution_apply, he, Nat.mul_div_cancel_left _ two_pos]
    rw [hH] at hRi hRc
    refine eq_one_of_conj (conjAut n K H) (fieldAut n K σ * dualAut n K)
      (fun R₀ h₁ h₂ h₃ => ?_) hRodd hRi hRc
    rw [hσe] at h₂ h₃
    exact eq_one_unitary hp2 hKe hn hinj h₁ h₂ h₃

end Gr

variable {n : ℕ} {K : Type} [Field K]

theorem conj_injective_projectiveSL
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) K) = ⊥) :
    Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) := by
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  refine conj_injective (eq_bot_iff.mpr fun z hz => ?_)
  rw [mem_bot]
  have hz' : e z ∈ center (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [mem_center_iff]
    intro g
    rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, (mem_center_iff.mp hz _)]
  rw [hZ, mem_bot] at hz'
  exact e.injective (hz'.trans (map_one e).symm)

theorem commute_graphField {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) (hZ : center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥)
    (A : GL (Fin n) (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f)
    (hi : orderOf (CatalogueBGraphField.graphFieldAction n (GaloisField p f) A σ) = 2)
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)))}
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * CatalogueBGraphField.graphFieldAction n _ A σ =
      CatalogueBGraphField.graphFieldAction n _ A σ * r)
    (hRc : ∀ s, CatalogueBGraphField.graphFieldAction n _ A σ s = s → Odd (orderOf s) →
      ∀ r ∈ R, MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set K := GaloisField p f with hKdef
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  set Φ : MulAut (projectiveSL n K) ≃* MulAut (ProjectiveSpecialLinearGroup (Fin n) K) :=
    MulAut.congr e with hΦ
  set t := conjAut n K A * fieldAut n K σ * dualAut n K with ht
  have hΦt : Φ t = CatalogueBGraphField.graphFieldAction n K A σ :=
    CatalogueBLinearHigherB.congr_graphField A σ
  have hsq : t ^ 2 = 1 := by
    have h : orderOf t = 2 := by rw [← MulEquiv.orderOf_eq Φ, hΦt, hi]
    rw [← h, pow_orderOf_eq_one]
  set R' := R.map Φ.symm.toMonoidHom with hR'
  have hmem : ∀ r ∈ R, Φ.symm r ∈ R' := fun r hr => ⟨r, hr, rfl⟩
  have hR'odd : Odd (Nat.card R') := by
    rw [hR', Subgroup.card_map_of_injective Φ.symm.injective]
    exact hRodd
  have hR'i : ∀ r ∈ R', r * t = t * r := by
    rintro _ ⟨r, hr, rfl⟩
    apply Φ.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply, hΦt]
    exact hRi r hr
  have hconj : ∀ s : projectiveSL n K, Φ (MulAut.conj s) = MulAut.conj (e s) := by
    intro s
    ext x
    simp [hΦ, MulAut.congr_apply, MulAut.conj_apply]
  have hR'c : ∀ s, t s = s → Odd (orderOf s) → ∀ r ∈ R',
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R' := by
    rintro s hs hso _ ⟨r, hr, rfl⟩
    have hs' : CatalogueBGraphField.graphFieldAction n K A σ (e s) = e s := by
      rw [← hΦt, hΦ]
      change e (t (e.symm (e s))) = e s
      rw [MulEquiv.symm_apply_apply, hs]
    have hso' : Odd (orderOf (e s)) := by rwa [MulEquiv.orderOf_eq]
    have h := hRc (e s) hs' hso' r hr
    have h2 : MulAut.conj s * Φ.symm r * (MulAut.conj s)⁻¹ =
        Φ.symm (MulAut.conj (e s) * r * (MulAut.conj (e s))⁻¹) := by
      apply Φ.injective
      rw [map_mul, map_mul, map_inv, hconj, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [h2]
    exact hmem _ h
  have hinj := conj_injective_projectiveSL (K := K) hZ
  have hK : Nat.card K = p ^ f := GaloisField.card p f (by omega)
  have key := Gr.eq_one_graph (Fact.out : p.Prime) hp2 hf hK hn hinj A σ hsq hR'odd hR'i hR'c
  have hone : ∀ r ∈ R, r = 1 := by
    intro r hr
    have h := key _ (hmem r hr)
    have := congrArg Φ h
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  intro r₁ hr₁ r₂ hr₂
  rw [hone r₁ hr₁, hone r₂ hr₂]

end CFSG.ComponentClassification.Foote5.OddLieCore
