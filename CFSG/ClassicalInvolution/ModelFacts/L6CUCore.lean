module

public import CFSG.ClassicalInvolution.ModelFacts.L6CUSemi
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
import CFSG.ClassicalInvolution.Asc77.AscT8S26UModL
import CFSG.ClassicalInvolution.Asc77.Lemma310
import CFSG.ClassicalInvolution.Asc77.ThmEStatement
import CFSG.ClassicalInvolution.Asc77.WP1Section18
import CFSG.ClassicalInvolution.Asc77.WP1Section6
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
import CFSG.ClassicalInvolution.Balance.Theorem5Models
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.Asc77
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) K

theorem coe_rotSU4_pow (n : ℕ) :
    ((rotSU4 h ^ n : unitarySU p f K 4) : GL (Fin 4) K) =
      Matrix.SpecialLinearGroup.toGL (rot4 K ^ n) := by
  rw [Subgroup.coe_pow, map_pow]
  rfl

theorem rotSU4_pow_four : rotSU4 h ^ 4 = (1 : unitarySU p f K 4) := by
  apply Subtype.ext
  rw [coe_rotSU4_pow, rot4_pow_four, map_one]
  rfl

theorem rotSU4_sq_not_central (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    rotSU4 h ^ 2 ∉ Subgroup.center (unitarySU p f K 4) := by
  intro hc
  rw [(UnitaryAut.isPerfect_and_center_unitarySU h hq (by norm_num : 3 ≤ 4)).2] at hc
  obtain ⟨c, -, -, hcm⟩ := mem_unitaryScalars.mp hc
  have hm : ((rotSU4 h ^ 2 : unitarySU p f K 4) : GL (Fin 4) K).val =
      (rot4 K ^ 2 : SL(4, K)).val := by
    rw [coe_rotSU4_pow]
    rfl
  rw [hcm, coe_rot4_sq] at hm
  have h0 : (c : K) = -1 := by
    have := congrFun (congrFun hm 0) 0
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  have h2' : (c : K) = 1 := by
    have := congrFun (congrFun hm 2) 2
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  exact UnitaryHigher.two_ne_zero_of_odd h hp2 (by linear_combination h0 - h2')

theorem fixed_of_comm {A : GL (Fin 4) K} {φ : K → K} {α : unitarySU p f K 4 →* unitarySU p f K 4}
    (hα : ∀ g : unitarySU p f K 4, (((α g : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄) =
      (A : 𝕄₄) * ((g : GL (Fin 4) K) : 𝕄₄).map φ * ((A⁻¹ : GL (Fin 4) K) : 𝕄₄))
    (k : unitarySU p f K 4)
    (hc : (A : 𝕄₄) * (((k : GL (Fin 4) K) : 𝕄₄) * (rot4 K : 𝕄₄) *
        uadj h ((k : GL (Fin 4) K) : 𝕄₄)).map φ =
      ((k : GL (Fin 4) K) : 𝕄₄) * (rot4 K : 𝕄₄) * uadj h ((k : GL (Fin 4) K) : 𝕄₄) *
        (A : 𝕄₄)) :
    α (k * rotSU4 h * k⁻¹) = k * rotSU4 h * k⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  rw [hα, coe_conj_rotSU4 h k, hc]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem comm_of_involutive {A : GL (Fin 4) K} {φ : K ≃+* K} (hφφ : ∀ c, φ (φ c) = c)
    {hA : ∀ g : unitarySU p f K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4}
    (hαα : ∀ g : unitarySU p f K 4, UnitaryAut.unitaryConjHom A φ hA
      (UnitaryAut.unitaryConjHom A φ hA g) = g) (g : unitarySU p f K 4) :
    (A : 𝕄₄) * (A : 𝕄₄).map φ * ((g : GL (Fin 4) K) : 𝕄₄) =
      ((g : GL (Fin 4) K) : 𝕄₄) * ((A : 𝕄₄) * (A : 𝕄₄).map φ) := by
  have hφφ' : φ * φ = 1 := RingEquiv.ext fun c => by
    change φ (φ c) = c
    exact hφφ c
  have hglφ : ∀ Y : GL (Fin 4) K, glAut φ (glAut φ Y) = Y := fun Y => by
    have := congrArg (fun χ : MulAut (GL (Fin 4) K) => χ Y)
      (show glAut φ * glAut φ = 1 by rw [← map_mul, hφφ', map_one])
    exact this
  have e1 := congrArg (fun Y : unitarySU p f K 4 => (Y : GL (Fin 4) K)) (hαα g)
  simp only [UnitaryAut.coe_unitaryConjHom, map_mul, map_inv, hglφ] at e1
  have e2 : A * glAut φ A * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (A * glAut φ A) := by
    calc A * glAut φ A * (g : GL (Fin 4) K) =
        (A * (glAut φ A * (g : GL (Fin 4) K) * (glAut φ A)⁻¹) * A⁻¹) * (A * glAut φ A) := by
          group
      _ = (g : GL (Fin 4) K) * (A * glAut φ A) := by rw [e1]
  have e3 := congrArg (fun Y : GL (Fin 4) K => (Y : 𝕄₄)) e2
  simp only [Units.val_mul, coe_glAut] at e3
  simpa only [Matrix.mul_assoc] using e3

theorem graph_sq_eq_one {A : 𝕄₄} (hA : uadj h A * A = 1) {c : K}
    (hc : A * A.map h.bar = c • 1) : c = 1 ∨ c = -1 := by
  have h1 : Aᵀ * A.map h.bar = 1 := by
    have := congrArg Matrix.transpose hA
    rwa [uadj, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h2 : A.map h.bar * Aᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : A = c • Aᵀ := by
    calc A = A * (A.map h.bar * Aᵀ) := by rw [h2, Matrix.mul_one]
      _ = (A * A.map h.bar) * Aᵀ := by rw [Matrix.mul_assoc]
      _ = c • Aᵀ := by rw [hc, Matrix.smul_mul, Matrix.one_mul]
  have h3' : Aᵀ = c • A := by
    have := congrArg Matrix.transpose h3
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
  have h4 : (c * c) • A = (1 : K) • A := by
    rw [one_smul, mul_smul, ← h3', ← h3]
  have hA0 : A ≠ 0 := by
    intro h0
    apply det_ne_zero_of_uadj_mul h hA
    rw [h0, det_zero]
  exact mul_self_eq_one_iff.mp (smul_left_injective K hA0 h4)

theorem aut164U4_core (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1) {Y : Type} [Group Y]
    (ψ : unitarySU p f K 4 →* Y) (hker : ψ.ker ≤ Subgroup.center (unitarySU p f K 4))
    (hsurj : Function.Surjective ψ) (β : MulAut Y) (hβ : β ^ 2 = 1) :
    ∃ k : unitarySU p f K 4, orderOf (ψ (k * rotSU4 h * k⁻¹)) = 4 ∧
      β (ψ (k * rotSU4 h * k⁻¹)) = ψ (k * rotSU4 h * k⁻¹) := by
  have hfin := h.finite
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  have hββ : ∀ y, β (β y) = y := fun y => by
    have := congrArg (fun F : MulAut Y => F y) hβ
    simpa [pow_two] using this
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    UnitaryAut.exists_lift_unitarySU h hp2 hq5 (d := 4) (by norm_num) ψ hsurj hker β
  obtain ⟨hφ, hcomp⟩ := hinv hββ
  have hAu' : uadj h (A : 𝕄₄) * (A : 𝕄₄) = 1 := hAu
  set α := UnitaryAut.unitaryConjHom A φ hA with hαdef
  have hαα : ∀ g : unitarySU p f K 4, α (α g) = g := fun g => DFunLike.congr_fun hcomp g
  have hα : ∀ g : unitarySU p f K 4, (((α g : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄) =
      (A : 𝕄₄) * ((g : GL (Fin 4) K) : 𝕄₄).map φ * ((A⁻¹ : GL (Fin 4) K) : 𝕄₄) := fun g => by
    rw [hαdef, UnitaryAut.coe_unitaryConjHom, Units.val_mul, Units.val_mul, coe_glAut]
  have hφφ : ∀ c, φ (φ c) = c := by
    rcases hφ with hφ1 | hb
    · intro c
      rw [hφ1]
      rfl
    · intro c
      rw [hb, hb, h.bar_bar]
  obtain ⟨c, hc⟩ := UnitaryAut.eq_smul_one_of_commute h hp2 (d := 4) (by norm_num)
    ((A : 𝕄₄) * (A : 𝕄₄).map φ) fun y hy => comm_of_involutive hφφ hαα ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k : unitarySU p f K 4, α (k * rotSU4 h * k⁻¹) = k * rotSU4 h * k⁻¹ := by
    rcases hφ with hφ1 | hb
    · have hmap : ∀ X : 𝕄₄, X.map φ = X := fun X => by
        rw [hφ1]
        ext i j
        rfl
      rw [hmap] at hc
      obtain ⟨Q, hQ, hQc⟩ := exists_frame_inner h hp2 hq4 hAu' hc
      obtain ⟨k, hk⟩ := exists_unitarySU_of_unitary4 h hQ
      refine ⟨k, fixed_of_comm h hα k ?_⟩
      rw [hmap, hk]
      exact hQc
    · have hmap : ∀ X : 𝕄₄, X.map φ = X.map h.bar := fun X => by
        ext i j
        simp only [Matrix.map_apply, hb]
      rw [hmap] at hc
      rcases graph_sq_eq_one h hAu' hc with rfl | rfl
      · obtain ⟨Q, hQ, hQc⟩ := exists_frame_sym h hp2 hAu' (by rw [hc, one_smul])
        obtain ⟨k, hk⟩ := exists_unitarySU_of_unitary4 h hQ
        refine ⟨k, fixed_of_comm h hα k ?_⟩
        rw [hmap, hk]
        exact hQc
      · obtain ⟨Q, hQ, hQc⟩ := exists_frame_alt h hp2 hq4 hAu' (by rw [hc, neg_one_smul])
        obtain ⟨k, hk⟩ := exists_unitarySU_of_unitary4 h hQ
        refine ⟨k, fixed_of_comm h hα k ?_⟩
        rw [hmap, hk]
        exact hQc
  refine ⟨k, ?_, ?_⟩
  · set s₀ : unitarySU p f K 4 := k * rotSU4 h * k⁻¹ with hs₀
    have hs₀4 : s₀ ^ 4 = 1 := by
      rw [hs₀, conj_pow, rotSU4_pow_four]
      group
    have hs₀2 : ψ (s₀ ^ 2) ≠ 1 := by
      intro h'
      have hcen : s₀ ^ 2 ∈ Subgroup.center (unitarySU p f K 4) := hker h'
      apply rotSU4_sq_not_central h hp2 hq5
      apply s26_center_of_conj k
      have : k * rotSU4 h ^ 2 * k⁻¹ = s₀ ^ 2 := by
        rw [hs₀, conj_pow]
      rw [this]
      exact hcen
    have h4' : (ψ s₀) ^ 4 = 1 := by rw [← map_pow, hs₀4, map_one]
    have h2' : (ψ s₀) ^ 2 ≠ 1 := by rw [← map_pow]; exact hs₀2
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (x := ψ s₀) (by simpa using h2')
      (by simpa using h4')
  · have := hlift (k * rotSU4 h * k⁻¹)
    rw [hk] at this
    exact this.symm

end CFSG.ClassicalInvolution.ModelFacts.L6C
