module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenLie
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Bridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCat
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Assembly.LowTwoRank
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  CFSG.LinearGroups

namespace EvenUnitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem map_rkOneQ (σ : K ≃+* K) (a b : K) :
    (rkOneQ h a b).map σ = rkOneQ h (σ a) (σ b) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
    simp [rkOneQ, heisenbergMatrix, hypIndexFin3, map_bar_comm h σ]

theorem rkOneQ_ee (a b : K) : rkOneQ h a b (.inl 0) (.inl 0) = 1 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_ez (a b : K) : rkOneQ h a b (.inl 0) (.inr (.inl 0)) = -h.bar a := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_ze (a b : K) : rkOneQ h a b (.inr (.inl 0)) (.inl 0) = 0 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_zz (a b : K) : rkOneQ h a b (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_we (a b : K) : rkOneQ h a b (.inr (.inr 0)) (.inl 0) = 0 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_wz (a b : K) : rkOneQ h a b (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_ww (a b : K) : rkOneQ h a b (.inr (.inr 0)) (.inr (.inr 0)) = 1 := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem entries {σ : K ≃+* K} {B : Matrix (HypIndex 1 1) (HypIndex 1 1) K} {a b : K}
    (hE : B * rkOneQ h (σ a) (σ b) = rkOneQ h a b * B) :
    -h.bar a * B (.inr (.inl 0)) (.inl 0) + b * B (.inr (.inr 0)) (.inl 0) = 0 ∧
    a * B (.inr (.inr 0)) (.inl 0) = 0 ∧
    -h.bar (σ a) * B (.inl 0) (.inl 0) = -h.bar a * B (.inr (.inl 0)) (.inr (.inl 0)) +
      b * B (.inr (.inr 0)) (.inr (.inl 0)) ∧
    -h.bar (σ a) * B (.inr (.inl 0)) (.inl 0) = a * B (.inr (.inr 0)) (.inr (.inl 0)) ∧
    h.bar (σ a) * B (.inr (.inr 0)) (.inl 0) = 0 ∧
    σ b * B (.inl 0) (.inl 0) + σ a * B (.inl 0) (.inr (.inl 0)) =
      -h.bar a * B (.inr (.inl 0)) (.inr (.inr 0)) + b * B (.inr (.inr 0)) (.inr (.inr 0)) ∧
    σ b * B (.inr (.inl 0)) (.inl 0) + σ a * B (.inr (.inl 0)) (.inr (.inl 0)) =
      a * B (.inr (.inr 0)) (.inr (.inr 0)) ∧
    σ b * B (.inr (.inr 0)) (.inl 0) + σ a * B (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
  have key : ∀ i j, (B * rkOneQ h (σ a) (σ b)) i j = (rkOneQ h a b * B) i j := fun i j => by
    rw [hE]
  have e00 := key (.inl 0) (.inl 0)
  have e10 := key (.inr (.inl 0)) (.inl 0)
  have e20 := key (.inr (.inr 0)) (.inl 0)
  have e01 := key (.inl 0) (.inr (.inl 0))
  have e11 := key (.inr (.inl 0)) (.inr (.inl 0))
  have e21 := key (.inr (.inr 0)) (.inr (.inl 0))
  have e02 := key (.inl 0) (.inr (.inr 0))
  have e12 := key (.inr (.inl 0)) (.inr (.inr 0))
  have e22 := key (.inr (.inr 0)) (.inr (.inr 0))
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, rkOneQ_ee, rkOneQ_ez, rkOneQ_ze, rkOneQ_zz, rkOneQ_we, rkOneQ_wz,
    rkOneQ_ww, rkOneQ_zf, rkOneQ_ef] at e00 e10 e20 e01 e11 e21 e02 e12 e22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -e00
  · linear_combination -e10
  · linear_combination e01
  · linear_combination e11
  · linear_combination -e21
  · linear_combination e02
  · linear_combination e12
  · linear_combination e22

theorem core {σ : K ≃+* K} {B : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hiso : (B.map h.bar)ᵀ * hypGram 1 1 K * B = hypGram 1 1 K)
    (hE : ∀ a b : K, h.norm a + h.trace b = 0 →
      B * rkOneQ h (σ a) (σ b) = rkOneQ h a b * B) :
    (∀ a, σ a = a) ∧ ∃ (d y : K), d ≠ 0 ∧ h.trace y = 0 ∧ B = d • rkOneQ h 0 y := by
  obtain ⟨b₁, hb₁⟩ := exists_norm_add_trace_eq_zero h 1
  obtain ⟨c1, c2, c3, c4, -, c6, c7, -⟩ := entries h (hE 1 b₁ hb₁)
  simp only [map_one, one_mul, neg_mul] at c1 c2 c3 c4 c6 c7
  have hwe : B (.inr (.inr 0)) (.inl 0) = 0 := c2
  have hze : B (.inr (.inl 0)) (.inl 0) = 0 := by
    rw [hwe] at c1
    linear_combination -c1
  have hwz : B (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    rw [hze] at c4
    linear_combination -c4
  have hezz : B (.inl 0) (.inl 0) = B (.inr (.inl 0)) (.inr (.inl 0)) := by
    rw [hwz] at c3
    linear_combination -c3
  have hzww : B (.inr (.inl 0)) (.inr (.inl 0)) = B (.inr (.inr 0)) (.inr (.inr 0)) := by
    rw [hze] at c7
    linear_combination c7
  have i1 := congrFun (congrFun hiso (.inl 0)) (.inr (.inr 0))
  simp [Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply, Matrix.transpose_apply,
    Matrix.map_apply, hwe, hze] at i1
  set d := B (.inl 0) (.inl 0) with hd
  have hzz : B (.inr (.inl 0)) (.inr (.inl 0)) = d := hezz.symm
  have hww : B (.inr (.inr 0)) (.inr (.inr 0)) = d := by rw [← hzww, hzz]
  have hnorm : h.bar d * d = 1 := by rw [hww] at i1; exact i1
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, map_zero, zero_mul] at hnorm
    exact zero_ne_one hnorm
  have hσ : ∀ a, σ a = a := by
    intro a
    obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h a
    obtain ⟨-, -, -, -, -, -, c7', -⟩ := entries h (hE a b hb)
    rw [hze, hzz, hww] at c7'
    exact mul_right_cancel₀ hd0 (by linear_combination c7')
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  obtain ⟨bω, hbω⟩ := exists_norm_add_trace_eq_zero h ω
  obtain ⟨-, -, -, -, -, c6ω, -, -⟩ := entries h (hE ω bω hbω)
  simp only [hσ, neg_mul, hww, ← hd] at c6ω c6
  have hez_zw : B (.inl 0) (.inr (.inl 0)) = - B (.inr (.inl 0)) (.inr (.inr 0)) := by
    linear_combination c6
  have hez : B (.inl 0) (.inr (.inl 0)) = 0 := by
    have h1 : (ω - h.bar ω) * B (.inl 0) (.inr (.inl 0)) = 0 := by
      linear_combination c6ω - (h.bar ω) * hez_zw
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hω))
  have hzw : B (.inr (.inl 0)) (.inr (.inr 0)) = 0 := by
    rw [hez] at hez_zw
    linear_combination hez_zw
  refine ⟨hσ, d, B (.inl 0) (.inr (.inr 0)) / d, hd0, ?_, ?_⟩
  · have i2 := congrFun (congrFun hiso (.inr (.inr 0))) (.inr (.inr 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hypGram_apply, Matrix.transpose_apply,
      Matrix.map_apply, hzw, hww] at i2
    have hbd : h.bar d ≠ 0 := (map_ne_zero h.bar).mpr hd0
    rw [UnitaryFieldData.trace, map_div₀]
    field_simp
    linear_combination i2
  · ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
      simp [rkOneQ_ee, rkOneQ_ez, rkOneQ_ze, rkOneQ_zz, rkOneQ_we, rkOneQ_wz, rkOneQ_ww,
        rkOneQ_zf, rkOneQ_ef, hwe, hze, hwz, hez, hzw, hzz, hww] <;>
      first | exact hd.symm | field_simp

end EvenUnitary

theorem sylowCentralizingAutInner_hypPSU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hq : 2 < 2 ^ f) : SylowCentralizingAutInner (hypPSU h 1 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨Qs, hQs⟩ := (unitary_order_and_Sylow h (le_refl 1) (le_refl 1)).2.2.2.2.1
  have hQ : IsSylowTwoOf (hypProjUnitriangular h 1 1) ⊤ := by
    rw [← hQs]
    exact isSylowTwoOf_top_iff.mpr ⟨Qs.isPGroup', Qs.not_dvd_index⟩
  refine sylowCentralizingAutInner_of_sylow _ hQ fun β hβ => ?_
  obtain ⟨σ, B, hiso, hβB⟩ := exists_isometry_hypPSU h hq β
  have hfix : ∀ a b : K, h.norm a + h.trace b = 0 →
      ((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          rkOneQ h (σ a) (σ b) =
        rkOneQ h a b * ((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    intro a b hab
    obtain ⟨hg, hβu⟩ := hβB (rkOneQElt h a b hab)
    have hfixu : β (hypProj h 1 1 (rkOneQElt h a b hab)) =
        hypProj h 1 1 (rkOneQElt h a b hab) :=
      hβ _ (Subgroup.mem_map_of_mem _ (rkOneQElt_mem h hab))
    rw [hβu] at hfixu
    have hker := (QuotientGroup.eq (s := hypScalars h 1 1)).mp hfixu
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hker
    have hu : ((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) =
        (B * glAut σ ((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) * B⁻¹) *
          GeneralLinearGroup.scalar (HypIndex 1 1) c := by
      rw [← inv_mul_eq_iff_eq_mul]
      simpa using hc
    have hmat : rkOneQ h a b = (c : K) •
        (((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          (rkOneQ h a b).map σ *
          ((B⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) := by
      have := congrArg
        (fun g : GL (HypIndex 1 1) K => (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hu
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_glAut, coe_rkOneQElt,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
        at this
      exact this
    have h31 : (3 : K) = 1 := by linear_combination h2
    have tr3 : (rkOneQ h a b).trace = 3 := by
      simp [Matrix.trace, Fintype.sum_sum_type, EvenUnitary.rkOneQ_ee, EvenUnitary.rkOneQ_zz,
        EvenUnitary.rkOneQ_ww]
      norm_num
    have tr3' : ((rkOneQ h a b).map σ).trace = 3 := by
      simp [Matrix.trace, Fintype.sum_sum_type, EvenUnitary.rkOneQ_ee, EvenUnitary.rkOneQ_zz,
        EvenUnitary.rkOneQ_ww]
      norm_num
    have hc1 : (c : K) = 1 := by
      have := congrArg Matrix.trace hmat
      rw [Matrix.trace_smul, Matrix.trace_units_conj, tr3', tr3, smul_eq_mul, h31] at this
      simpa using this.symm
    rw [hc1, one_smul] at hmat
    rw [← EvenUnitary.map_rkOneQ h σ a b]
    calc ((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          (rkOneQ h a b).map σ
        = (((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
            (rkOneQ h a b).map σ *
            ((B⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) *
          ((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
          rw [mul_assoc _ ((B⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K),
            Units.inv_mul, mul_one]
      _ = rkOneQ h a b *
          ((B : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
          rw [← hmat]
  obtain ⟨hσ, d, y, hd0, hy, hBd⟩ := EvenUnitary.core h hiso hfix
  have hy0 : h.norm 0 + h.trace y = 0 := by
    rw [UnitaryFieldData.norm, zero_mul, zero_add]
    exact hy
  have hBGL : B = GeneralLinearGroup.scalar (HypIndex 1 1) (Units.mk0 d hd0) *
      ((rkOneQElt h 0 y hy0 : hypSU h 1 1) : GL (HypIndex 1 1) K) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, hBd]
    rfl
  refine ⟨(hypProj h 1 1 (rkOneQElt h 0 y hy0))⁻¹, fun y' => ?_⟩
  obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 y'
  obtain ⟨hg, hβg⟩ := hβB g
  rw [hβg, inv_inv, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hσg : glAut σ (g : GL (HypIndex 1 1) K) = g := by
    apply Units.ext
    rw [coe_glAut]
    ext i j
    simp [hσ]
  show B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹ =
    ((rkOneQElt h 0 y hy0 : hypSU h 1 1) : GL (HypIndex 1 1) K) * (g : GL (HypIndex 1 1) K) *
      ((rkOneQElt h 0 y hy0 : hypSU h 1 1) : GL (HypIndex 1 1) K)⁻¹
  rw [hBGL, scalar_mul_conj_eq, hσg]

theorem evenUnitaryAutInner : EvenUnitaryAutInner := by
  intro X _ _ f hf h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact SylowCentralizingAutInner.of_mulEquiv
    ((e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)).trans
      (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.psu3EquivHypPSU (by omega)).symm)
    (sylowCentralizingAutInner_hypPSU
      (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
        (by omega)) hq)

theorem evenLieAutInner_of_tits
    (hT : TitsSylowCentralizingAutInner) : EvenLieAutInner :=
  evenLieAutInner_of_inputs hT evenUnitaryAutInner

end CFSG.QuasithinUnique.Ch1
