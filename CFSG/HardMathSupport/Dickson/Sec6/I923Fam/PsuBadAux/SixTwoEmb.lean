module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoGroup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DBase

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem normOneScalars_five_le_ker (hq : ℓ ^ f = 2) (i₀ : Fin 6) :
    normOneScalars h (gramSU h (idGram K 5)) 5 ≤
      ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)).comp (phi6 h i₀)).ker := by
  rintro z ⟨c, -, hc5, hz⟩
  have hc3 : c ^ 3 = 1 := unit_pow_three_eq_one h hq c
  have hc1 : c = 1 := by
    calc c = c ^ 3 * c ^ 3 * (c ^ 5)⁻¹ := by group
      _ = 1 := by rw [hc3, hc5]; simp
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [hz, hc1, map_one]
    rfl
  rw [MonoidHom.mem_ker, hz1, map_one]

@[expose] noncomputable def xi6 (hq : ℓ ^ f = 2) (i₀ : Fin 6) :
    primeFormP h (idGram K 5) →* primeFormP h (idGram K 6) :=
  QuotientGroup.lift (normOneScalars h (gramSU h (idGram K 5)) 5)
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)).comp (phi6 h i₀))
    (normOneScalars_five_le_ker h hq i₀)

theorem xi6_mk (hq : ℓ ^ f = 2) (i₀ : Fin 6) (Y : gramSU h (idGram K 5)) :
    xi6 h hq i₀ (Y : primeFormP h (idGram K 5)) =
      ((phi6 h i₀ Y : gramSU h (idGram K 6)) : primeFormP h (idGram K 6)) := rfl

theorem xi6_injective (hq : ℓ ^ f = 2) (i₀ : Fin 6) : Function.Injective (xi6 h hq i₀) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H Y =>
    rw [xi6_mk] at hx
    have hmem : phi6 h i₀ Y ∈ normOneScalars h (gramSU h (idGram K 6)) 6 :=
      (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨c, -, -, hc⟩ := hmem
    have h1 : c = 1 := by
      have := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) i₀ i₀) hc
      rw [coe_phi6, frameEmb_cframe6_left, if_pos rfl,
        scalar_coe_eq_smul_one, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
      exact Units.ext this.symm
    have hphi : phi6 h i₀ Y = 1 := by
      apply Subtype.ext
      rw [hc, h1, map_one]
      rfl
    have hY : Y = 1 := phi6_injective h i₀ (by rw [hphi, map_one])
    rw [hY]
    rfl

theorem range_xi6_le_fix (hq : ℓ ^ f = 2) (i₀ : Fin 6) {ν μ : K}
    {D : primeFormUnitary h (idGram K 6)}
    (hD : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = dmat i₀ ν μ) :
    (xi6 h hq i₀).range ≤ fixSubgroup (primeFormConjHom h (idGram K 6) D) := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientGroup.induction_on with
  | H Y =>
    rw [xi6_mk]
    show primeFormConjHom h (idGram K 6) D _ = _
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hcomm : (D : GL (Fin 6) K) * (phi6 h i₀ Y : GL (Fin 6) K) =
        (phi6 h i₀ Y : GL (Fin 6) K) * (D : GL (Fin 6) K) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hD, coe_phi6]
      exact frameEmb_commute_dmat h i₀ ν μ _
    change (D : GL (Fin 6) K) * (phi6 h i₀ Y : GL (Fin 6) K) * (D : GL (Fin 6) K)⁻¹ = _
    rw [hcomm, mul_inv_cancel_right]

theorem commutator_fix_le_range_xi6 (hq : ℓ ^ f = 2) (i₀ : Fin 6) {ν μ : K} (hνμ : ν ≠ μ)
    {D : primeFormUnitary h (idGram K 6)}
    (hD : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = dmat i₀ ν μ) :
    ⁅fixSubgroup (primeFormConjHom h (idGram K 6) D),
        fixSubgroup (primeFormConjHom h (idGram K 6) D)⁆ ≤ (xi6 h hq i₀).range := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨w, hwD, hxy⟩ := commutator_fixed_conj h hx hy
  have hw : ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * dmat i₀ ν μ =
      dmat i₀ ν μ * ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [← hD]
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hwD
    simpa using this
  obtain ⟨c, Y, hY⟩ := exists_eq_scalar_mul_phi6 h hq hνμ i₀ hw
  refine ⟨(Y : primeFormP h (idGram K 5)), ?_⟩
  rw [xi6_mk, hxy, QuotientGroup.eq]
  refine mem_normOneScalars.2 ⟨c, ?_, ?_, ?_⟩
  · rw [norm_eq_cube h hq, ← Units.val_pow_eq_pow_val,
      unit_pow_three_eq_one h hq, Units.val_one]
  · rw [show 6 = 3 * 2 by norm_num, pow_mul, unit_pow_three_eq_one h hq, one_pow]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, hY,
      ← (commute_scalar c (phi6 h i₀ Y : GL (Fin 6) K)).eq, inv_mul_cancel_left]

end CFSG.HardMathSupport.Dickson.Sec6.I923
