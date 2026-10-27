module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K] {d : ℕ}

theorem commPair_left {Q : QuadraticForm K (Fin d → K)} {g h : similarityPairs Q}
    (hg : g.val.right = 1) (hh : h.val.right = 1) :
    (g * h * g⁻¹ * h⁻¹ : similarityPairs Q).val.left =
      g.val.left * h.val.left * g.val.left⁻¹ * h.val.left⁻¹ := by
  change (g.val * h.val * g.val⁻¹ * h.val⁻¹).left = _
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right, hg, hh, mul_one, inv_one, map_one, MulAut.one_apply]

theorem false_of_exc [Finite K] (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin 8) K} (hR : (R : Matrix (Fin 8) (Fin 8) K)ᵀ = R)
    (hker : OKer (oQ R)) {M : Subgroup (GL (Fin 8) K)} (hd : ExcData R M)
    {gs : similarityPairs (oQ R)} (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1)
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs))))
    {gt : similarityPairs (oQ R)} (ht1 : gt.val.right = 1) (htt : oκ _ (gt * gt) = 1)
    (hAR : (gt.val.left : Matrix (Fin 8) (Fin 8) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin 8) (Fin 8) K) * gt.val.left))
    (hts : oκ _ gt * oκ _ gs = oκ _ gs * oκ _ gt)
    (hQt : ∀ x ∈ (M.subgroupOf (matrixDerived (oQ R))).map (projH _), oκ _ gt x ∈
      (M.subgroupOf (matrixDerived (oQ R))).map (projH _)) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set A := gt.val.left with hAdef
  obtain ⟨a₀, ha₀, hA2, -, -⟩ := inner_even_data h2 hR (by norm_num) hker ht1 htt
  have hval : ∀ X (hX : X ∈ M), ((matrixDerivedConjugation (oQ R) gt ⟨X, hd.le hX⟩ : H) :
      GL (Fin 8) K) = A * X * A⁻¹ := by
    intro X hX
    rw [matrixDerivedConjugation_val, ht1, map_one, MulAut.one_apply]
  have hBH : ∀ X ∈ M, A * X * A⁻¹ ∈ H := fun X hX =>
    hval X hX ▸ (matrixDerivedConjugation (oQ R) gt ⟨X, hd.le hX⟩).2
  have hconj : ∀ X ∈ M, A * X * A⁻¹ ∈ M := by
    refine conj_le_of_map_le hd.perf A hBH fun X hX => ?_
    have e : (⟨A * X * A⁻¹, hBH X hX⟩ : H) = matrixDerivedConjugation (oQ R) gt ⟨X, hd.le hX⟩ :=
      Subtype.ext (hval X hX).symm
    rw [e, ← kappa_proj]
    exact hQt _ ⟨⟨X, hd.le hX⟩, mem_subgroupOf.2 hX, rfl⟩
  have hAA : A * A = GeneralLinearGroup.scalar (Fin 8) (Units.mk0 a₀ ha₀) := by
    apply Units.ext
    rw [Units.val_mul, hA2, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_mk0]
  set sc := GeneralLinearGroup.scalar (Fin 8) (Units.mk0 a₀ ha₀) with hsc
  have hAi : A⁻¹ = sc⁻¹ * A := by
    have h1 : sc⁻¹ * A * A = 1 := by rw [mul_assoc, hAA, inv_mul_cancel]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hAM : ∀ X ∈ M, A⁻¹ * X * A ∈ M := by
    intro X hX
    have hc : (A * X) * sc⁻¹ = sc⁻¹ * (A * X) :=
      ((commute_scalar (Units.mk0 a₀ ha₀) (A * X)).inv_right).eq
    have e : A⁻¹ * X * A = A * X * A⁻¹ := by
      rw [hAi]
      calc sc⁻¹ * A * X * A = sc⁻¹ * (A * X) * A := by group
        _ = (A * X) * sc⁻¹ * A := by rw [← hc]
        _ = A * X * (sc⁻¹ * A) := by group
    rw [e]
    exact hconj X hX
  have hAR' : (A : Matrix (Fin 8) (Fin 8) K)ᵀ * R = -((R : Matrix (Fin 8) (Fin 8) K) * A) := by
    rw [hAR, neg_one_smul]
  by_cases hσ : gs.val.right = 1
  ·
    have hcomm : oκ _ (gt * gs * gt⁻¹ * gs⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hts, mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨-, ζ, hζ⟩ := hker _ hcomm
    rw [commPair_left ht1 hσ] at hζ
    refine false_of_exc_inner hK hR hker hd hσ hss hs1 hQs hQc ha₀ hA2 hAR' hAM ⟨ζ, ?_⟩
    rw [hζ]
    group
  ·
    have : Fintype K := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
    obtain ⟨hσ2', c, hc⟩ := hker _ hss
    have hσ2 : gs.val.right ^ 2 = 1 := by rw [← (sq_val _ gs).2]; exact hσ2'
    have hc' : gs.val.left * glFieldAut (Fin 8) K gs.val.right gs.val.left =
        GeneralLinearGroup.scalar (Fin 8) c := by rw [← (sq_val _ gs).1, hc]
    obtain ⟨e', hu, hσ'⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hσ
    obtain ⟨wF, hwF, S, ν, hS, heq⟩ :=
      exists_field_transport hu hℓ2 h2 (by norm_num) hR hσ' hc'
    have hd' := hd.transport S ν hS
    obtain ⟨hQs', hQc'⟩ := transport_comp hd.le S ν hS hQs hQc
    rw [heq] at hQs' hQc'
    exact false_of_field hu hK hℓ2 hwF hd' hQs' hQc'

end CFSG.ComponentClassification.Burgoyne.DX
