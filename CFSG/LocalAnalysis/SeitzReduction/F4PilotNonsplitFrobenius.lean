module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.Mathlib.LinearAlgebra.SpecialLinearGroup.Frobenius
public import CFSG.RankThree.PartOne.KE6.EqpOpp
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFuseFrame

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6

theorem exists_inv_mul_map_mul_eq_HSL_frob
    {K : Type} [Field K] [Finite K] [CharP K 2] {t : SL2 K}
    (ht : orderOf t = Nat.card K + 1) :
    ∃ ζ : (FiniteField.Extension K 2 2)ˣ,
      IsPrimitiveRoot (ζ : FiniteField.Extension K 2 2) (Nat.card K + 1) ∧
      ∃ P : SL2 (FiniteField.Extension K 2 2),
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) t * P =
          HSL ζ ∧
        Matrix.SpecialLinearGroup.map
          (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom P = P * eqpW := by
  let L := FiniteField.Extension K 2 2
  let Fr : L →+* L := (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom
  let B : SL2 L := Matrix.SpecialLinearGroup.map (algebraMap K L) t
  obtain ⟨ζ, Q, -, hζ1, hζpow, hQ⟩ := exists_inv_mul_map_mul_eq_HSL ht
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hζ1
    apply Units.ext
    exact eq_one_of_sq_eq_one_of_charTwo (by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h)
  have hζq : ζ ^ Nat.card K = ζ⁻¹ := by
    have h := congrArg (fun u : Lˣ => u * ζ⁻¹) hζpow
    simpa only [pow_succ, mul_assoc, mul_inv_cancel, mul_one, one_mul] using h
  have hFζ : Units.map Fr.toMonoidHom ζ = ζ⁻¹ := by
    apply Units.ext
    change FiniteField.Extension.frob K 2 2 (ζ : L) = ((ζ⁻¹ : Lˣ) : L)
    rw [FiniteField.Extension.frob_apply]
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hζq
  have hFB : Matrix.SpecialLinearGroup.map Fr B = B := by
    ext i j
    simp only [B, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (FiniteField.Extension.frob K 2 2).commutes ((t : Matrix (Fin 2) (Fin 2) K) i j)
  have hFr : ∀ x : L, Fr (Fr x) = x := by
    intro x
    have h := FiniteField.Extension.frob_iterate_apply (k := K) (p := 2) (n := 2) 2 (x := x)
    rw [pow_two, AlgEquiv.mul_apply] at h
    rw [← FiniteField.natCard_extension (k := K) (p := 2) (n := 2)] at h
    have hx : x ^ Nat.card L = x := by
      letI := Fintype.ofFinite L
      simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
    exact h.trans hx
  obtain ⟨c, hc⟩ := CFSG.StandardType.TwE6CorootCore.exists_map_eq_mul_nSL_of_conj_HSL
    hζ2 hQ hFB hFζ
  rw [nSL_eq_HSL_mul] at hc
  obtain ⟨u, -, -, hFQ⟩ := exists_HSL_normalization_of_map_eq_mul_HSL_WSL Fr hFr hc
  let P : SL2 L := Q * HSL u
  have hcomm : Commute (HSL u) (HSL ζ) := by
    change HSL u * HSL ζ = HSL ζ * HSL u
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        coe_HSL, mul_comm]
  have hdiag : P⁻¹ * B * P = HSL ζ := by
    calc
      P⁻¹ * B * P = (HSL u)⁻¹ * (Q⁻¹ * B * Q) * HSL u := by dsimp [P]; group
      _ = (HSL u)⁻¹ * HSL ζ * HSL u := by rw [hQ]
      _ = HSL ζ := by rw [hcomm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hW : (WSL : SL2 L) = eqpW := by
    rw [eqpW_eq]
    have htwo : (2 : L) = 0 := CharTwo.two_eq_zero
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, coe_uSL, coe_vSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | rfl | linear_combination htwo | linear_combination (-1 : L) * htwo
  have hFP : Matrix.SpecialLinearGroup.map Fr P = P * eqpW := by
    simpa only [P, hW] using hFQ
  have hB : B = MulAut.conj Q (HSL ζ) := by
    change Matrix.SpecialLinearGroup.map (algebraMap K L) t = Q * HSL ζ * Q⁻¹
    rw [← hQ]
    group
    rfl
  have hord : orderOf ζ = Nat.card K + 1 := by
    calc
      orderOf ζ = orderOf (HSL ζ : SL2 L) := (orderOf_HSL ζ).symm
      _ = orderOf (MulAut.conj Q (HSL ζ)) :=
        (orderOf_injective (MulAut.conj Q).toMonoidHom (MulAut.conj Q).injective (HSL ζ)).symm
      _ = orderOf B := by rw [← hB]
      _ = orderOf t := orderOf_injective _ (SL2_map_injective (algebraMap K L)) t
      _ = Nat.card K + 1 := ht
  have hprim : IsPrimitiveRoot ζ (Nat.card K + 1) := IsPrimitiveRoot.iff_orderOf.mpr hord
  exact ⟨ζ, hprim.map_of_injective (f := Units.coeHom L) Units.val_injective, P, hdiag, hFP⟩

theorem exists_inv_mul_map_mul_eq_HSL_frob_four
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {t : SL2 K} (ht : orderOf t = 5) :
    ∃ ζ : (FiniteField.Extension K 2 2)ˣ,
      IsPrimitiveRoot (ζ : FiniteField.Extension K 2 2) 5 ∧
      ∃ P : SL2 (FiniteField.Extension K 2 2),
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) t * P =
          HSL ζ ∧
        Matrix.SpecialLinearGroup.map (iterateFrobenius (FiniteField.Extension K 2 2) 2 2) P =
          P * eqpW ∧
        P⁻¹ * Matrix.SpecialLinearGroup.map
          (iterateFrobenius (FiniteField.Extension K 2 2) 2 2) P = eqpW := by
  obtain ⟨ζ, hζ, P, hdiag, hFr⟩ :=
    exists_inv_mul_map_mul_eq_HSL_frob (K := K) (t := t) (by simpa [hK] using ht)
  have heq : (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom =
      iterateFrobenius (FiniteField.Extension K 2 2) 2 2 := by
    ext x
    change FiniteField.Extension.frob K 2 2 x = iterateFrobenius (FiniteField.Extension K 2 2) 2 2 x
    rw [FiniteField.Extension.frob_apply, hK, iterateFrobenius_def]
    norm_num
  have hFr4 : Matrix.SpecialLinearGroup.map
      (iterateFrobenius (FiniteField.Extension K 2 2) 2 2) P = P * eqpW := by
    simpa only [heq] using hFr
  refine ⟨ζ, by simpa [hK] using hζ, P, hdiag, hFr4, ?_⟩
  rw [hFr4]
  group

theorem exists_simultaneous_diagonalizer_order_five
    {K Ω : Type} [Field K] [Finite K] [CharP K 2]
    [Field Ω] [CharP Ω 2] [Algebra K Ω] [IsAlgClosed Ω]
    (hK : Nat.card K = 4) (t : SL2 K) (ht : orderOf t = 5) :
    ∃ ζ : Ωˣ, IsPrimitiveRoot (ζ : Ω) 5 ∧
      ∃ A : SL2 Ω,
        A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 2) A = eqpW ∧
        A⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K Ω) t * A = HSL ζ := by
  let L := FiniteField.Extension K 2 2
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  obtain ⟨ζ, hζ, P, hdiag, -, hLang⟩ := exists_inv_mul_map_mul_eq_HSL_frob_four hK ht
  let ζ' : Ωˣ := Units.map ι.toRingHom.toMonoidHom ζ
  let A : SL2 Ω := Matrix.SpecialLinearGroup.map ι.toRingHom P
  have hζ' : IsPrimitiveRoot (ζ' : Ω) 5 :=
    hζ.map_of_injective (f := ι.toRingHom) ι.toRingHom.injective
  have hT : Matrix.SpecialLinearGroup.map ι.toRingHom
      (Matrix.SpecialLinearGroup.map (algebraMap K L) t) =
      Matrix.SpecialLinearGroup.map (algebraMap K Ω) t := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact ι.commutes ((t : Matrix (Fin 2) (Fin 2) K) i j)
  have hH : Matrix.SpecialLinearGroup.map ι.toRingHom (HSL ζ) = HSL ζ' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, coe_HSL, ζ', Units.val_inv_eq_inv_val, map_inv₀]
  have hU : Matrix.SpecialLinearGroup.map ι.toRingHom (uSL (1 : L)) = uSL (1 : Ω) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        coe_uSL]
  have hV : Matrix.SpecialLinearGroup.map ι.toRingHom (vSL (1 : L)) = vSL (1 : Ω) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        coe_vSL]
  have hW : Matrix.SpecialLinearGroup.map ι.toRingHom (eqpW : SL2 L) = (eqpW : SL2 Ω) := by
    rw [eqpW_eq, eqpW_eq, map_mul, map_mul, hU, hV]
  have hF : Matrix.SpecialLinearGroup.map ι.toRingHom
      (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) P) =
      Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 2) A := by
    ext i j
    simp [A, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, iterateFrobenius_def, map_pow]
  have hdiag' := congrArg (Matrix.SpecialLinearGroup.map ι.toRingHom) hdiag
  rw [map_mul, map_mul, map_inv, hT, hH] at hdiag'
  have hLang' := congrArg (Matrix.SpecialLinearGroup.map ι.toRingHom) hLang
  rw [map_mul, map_inv, hF, hW] at hLang'
  exact ⟨ζ', hζ', A, hLang', hdiag'⟩

end CFSG.SeitzReduction.F4Pilot

end
