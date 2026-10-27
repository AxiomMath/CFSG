module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.NormCoordinates
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model

public section

namespace CFSG.RankTwoShapes

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

noncomputable section

variable {K : Type} [Field K]

theorem unitaryFourW_le_specialSubgroup (hK : Nat.card K = 16) (σ : K ≃+* K)
    (hinv : Function.Involutive σ) (hσ : ∀ x, σ x = x ^ 4) :
    unitaryFourW K hK ≤ (antidiagonalHermitianForm σ hinv).specialSubgroup := by
  have := charP_two_of_natCard_eq_sixteen hK
  rintro A ⟨a, b, hab, hA⟩
  have ha := pow_sixteen_eq_self hK a
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, antidiagonalHermitianForm, unitaryFourMatrix,
        Matrix.mul_apply, Fin.sum_univ_three, hσ] <;> grind
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hA, unitaryFourMatrix_det]
    rfl

@[expose] def unitaryFourWToPSU (hK : Nat.card K = 16) (σ : K ≃+* K)
    (hinv : Function.Involutive σ) (hσ : ∀ x, σ x = x ^ 4) :
    unitaryFourW K hK →* ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv) :=
  (Matrix.ProjGenLinGroup.mk.comp (unitaryFourW K hK).subtype).codRestrict _ fun w =>
    Subgroup.mem_map_of_mem _ (unitaryFourW_le_specialSubgroup hK σ hinv hσ w.2)

theorem unitaryFourWToPSU_injective (hK : Nat.card K = 16) (σ : K ≃+* K)
    (hinv : Function.Involutive σ) (hσ : ∀ x, σ x = x ^ 4) :
    Function.Injective (unitaryFourWToPSU hK σ hinv hσ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hmk : Matrix.ProjGenLinGroup.mk (w : GL (Fin 3) K) = 1 := congrArg Subtype.val hw
  have hcenter : (w : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
    exact hmk
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter
  rw [UnitaryFourW.coe_eq] at hc
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) hc
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hc
  simp [unitaryFourMatrix, Matrix.scalar_apply] at h00 h12 h02
  ext
  · rw [UnitaryFourW.fst_one, ← h12]
  · rw [UnitaryFourW.snd_one, ← h02]

theorem exists_psu_antidiagonal (hK : Nat.card K = 16) :
    ∃ (σ : K ≃+* K) (hinv : Function.Involutive σ) (_ : ∀ x, σ x = x ^ 4),
      Finite (ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv)) ∧
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv)) =
        62400 ∧
      Nonempty (ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv) ≃*
        PSU3Model 2) := by
  have := finite_of_natCard_eq_sixteen hK
  obtain ⟨σ, hσ, hinv, hfix⟩ :=
    exists_quadraticFrobenius K 2 (by norm_num) (by rw [hK]; norm_num)
  have hσ' : ∀ x, σ x = x ^ 4 := fun x => by rw [hσ]; norm_num
  let J := antidiagonalHermitianForm σ hinv
  have hfix' : Nat.card {x : K // J.conj x = x} = 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← hfix]
    rfl
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hfinite : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := inferInstance
  rcases External.huppert_II_10_12 J 4 (by rw [hK]; norm_num) hfix' rfl with
    ⟨-, -, -, -, -, -, -, -, hGcard, -⟩
  refine ⟨σ, hinv, hσ', hfinite, ?_, ?_⟩
  · rw [hGcard]
    norm_num
  · exact projectiveSpecialUnitary_equiv_PSU3Model J 2 le_rfl rfl (by rw [hK]; norm_num)
      (by rw [hfix']; norm_num)

theorem finite_of_statedClassicalModel_PSU_three_two_two {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) : Finite H := by
  obtain ⟨e⟩ := (statedClassicalModel_PSU_three_two_iff H 2 le_rfl).mp hH
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨σ, hinv, -, hfin, -, ⟨e'⟩⟩ := exists_psu_antidiagonal hK
  exact Finite.of_equiv _ (e.trans e'.symm).symm.toEquiv

theorem nonempty_sylow_equiv_unitaryFourW {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H)
    (K : Type) [Field K] (hK : Nat.card K = 16) :
    Nonempty ((U : Subgroup H) ≃* unitaryFourW K hK) := by
  have := finite_of_natCard_eq_sixteen hK
  have := UnitaryFourW.finite_unitaryFourW (hK := hK)
  obtain ⟨σ, hinv, hσ, hfin, hcard, ⟨eG⟩⟩ := exists_psu_antidiagonal hK
  obtain ⟨eH⟩ := (statedClassicalModel_PSU_three_two_iff H 2 le_rfl).mp hH
  let G := ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv)
  let e : H ≃* G := eH.trans eG.symm
  have : Finite H := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι := unitaryFourWToPSU hK σ hinv hσ
  have hι := unitaryFourWToPSU_injective hK σ hinv hσ
  let eW : unitaryFourW K hK ≃* ι.range := MonoidHom.ofInjective hι
  have hfact : (62400 : ℕ).factorization 2 = 6 := by
    rw [show (62400 : ℕ) = 2 ^ 6 * 975 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 975 by norm_num)]
    simp
  let P₀ : Sylow 2 G := Sylow.ofCard ι.range (by
    rw [← Nat.card_congr eW.toEquiv, UnitaryFourW.natCard_unitaryFourW, hcard, hfact]
    norm_num)
  let U' : Sylow 2 G := U.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ U'
  have hU' : ((U' : Subgroup G)) = (U : Subgroup H).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  refine ⟨(e.subgroupMap (U : Subgroup H)).trans ?_⟩
  refine (MulEquiv.subgroupCongr ?_).trans ((P₀.equivSMul g).symm.trans
    ((MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _)).trans eW.symm))
  rw [hg, hU']
  rfl

theorem unitaryFour_sylow_card {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H) :
    Nat.card (U : Subgroup H) = 64 ∧ Nat.card (Subgroup.center (U : Subgroup H)) = 4 ∧
      ∀ z ∈ Subgroup.center (U : Subgroup H), z ^ 2 = 1 := by
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := nonempty_sylow_equiv_unitaryFourW hH U (GaloisField 2 4) hK
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, UnitaryFourW.natCard_unitaryFourW]
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, UnitaryFourW.natCard_center]
  · intro z hz
    have hez : e z ∈ Subgroup.center (unitaryFourW (GaloisField 2 4) hK) :=
      ((Subgroup.centerCongr e) ⟨z, hz⟩).2
    apply e.injective
    rw [map_pow, map_one]
    exact UnitaryFourW.sq_eq_one_of_mem_center hez

theorem unitaryFour_sylow_normCoordinates {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 16),
      Nonempty ((U : Subgroup H) ≃* unitaryFourW K hK) ∧
      Nat.card {t : K // t ^ 4 = t} = 4 ∧
      Nat.card (unitaryFourW K hK) = 64 ∧
      Subgroup.center (unitaryFourW K hK) = commutator (unitaryFourW K hK) ∧
      (∀ w : unitaryFourW K hK, w ∈ Subgroup.center (unitaryFourW K hK) ↔
        ∃ t : K, t ^ 4 = t ∧
          ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix 0 t) ∧
      Nat.card (Subgroup.center (unitaryFourW K hK)) = 4 ∧
      (∀ z ∈ Subgroup.center (unitaryFourW K hK), z ^ 2 = 1) ∧
      Function.Surjective (UnitaryFourW.firstCoord hK) ∧
      (UnitaryFourW.firstCoord hK).ker = Subgroup.center (unitaryFourW K hK) ∧
      ∀ (w : unitaryFourW K hK) (a b : K),
        ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b →
          UnitaryFourW.firstCoord hK w = Multiplicative.ofAdd a ∧
          (((w ^ 2 : unitaryFourW K hK) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            unitaryFourMatrix 0 (a ^ 5) := by
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  refine ⟨GaloisField 2 4, inferInstance, inferInstance, hK,
    nonempty_sylow_equiv_unitaryFourW hH U _ hK, natCard_pow_four_eq_self hK,
    UnitaryFourW.natCard_unitaryFourW, UnitaryFourW.center_eq_commutator,
    fun w => UnitaryFourW.mem_center_iff, UnitaryFourW.natCard_center,
    fun z hz => UnitaryFourW.sq_eq_one_of_mem_center hz, UnitaryFourW.firstCoord_surjective,
    UnitaryFourW.center_eq_ker_firstCoord.symm, fun w a b h => ⟨?_, ?_⟩⟩
  · rw [UnitaryFourW.firstCoord_apply, UnitaryFourW.fst_eq_of_coe_eq h]
  · rw [UnitaryFourW.coe_sq, UnitaryFourW.fst_eq_of_coe_eq h]

end

end CFSG.RankTwoShapes
