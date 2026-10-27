module

public import CFSG.Open.StatedCenterThree
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverL3U3
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419CoverCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.RankThree.PerfectCover

private theorem twE6Cov_exists_statedSU_of_isU3eight {Y : Type} [Group Y]
    (h : catalogIs Y isU3eight) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      CharP K 2 ∧ Nat.card K = 8 ^ 2 ∧
        Nonempty (Y ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 8 K)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [isU3eight, onLie] at hi
  | alternating _ _ => simp [isU3eight, onLie] at hi
  | sporadic _ => simp [isU3eight, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        have hq8 : q.card = 8 := hi
        have hp2 : q.p = 2 := by
          have hdvd : q.p ∣ 8 := by
            rw [← hq8, TauCeti.PrimePower.card_def]
            exact dvd_pow_self _ q.exponent_pos.ne'
          have hdvd' : q.p ∣ 2 ^ 3 := by
            rwa [show (2 : ℕ) ^ 3 = 8 by norm_num]
          exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
            (q.prime_p.dvd_of_dvd_pow hdvd')
        have he3 : q.exponent = 3 := by
          have h1 : 2 ^ q.exponent = 2 ^ 3 := by
            rw [← hp2, ← TauCeti.PrimePower.card_def, hq8, hp2]
            norm_num
          exact Nat.pow_right_injective (le_refl 2) h1
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        haveI : Fintype (GaloisField q.p (2 * q.exponent)) := Fintype.ofFinite _
        have hcardq : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
          rw [GaloisField.card q.p (2 * q.exponent) (by omega), TauCeti.PrimePower.card_def,
            ← pow_mul, mul_comm]
        have hcardK : Nat.card (GaloisField q.p (2 * q.exponent)) = 8 ^ 2 := by
          rw [hcardq, hq8]
        have hchar : CharP (GaloisField q.p (2 * q.exponent)) 2 := by
          rw [← hp2]
          infer_instance
        obtain ⟨q', hv', hp', hcard', ⟨eSU⟩⟩ :=
          CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
            (K := GaloisField q.p (2 * q.exponent)) (m := 3) (q := 8)
            (by rw [← Nat.card_eq_fintype_card]; exact hcardK) (by norm_num)
            (fun h => absurd (Prod.mk.inj h).2 (by norm_num))
        have hringch : ringChar (GaloisField q.p (2 * q.exponent)) = 2 := ringChar.eq_iff.2 hchar
        have hq' : q' = q := by
          apply TauCeti.PrimePower.ext
          · rw [hp', hringch, hp2]
          · have h1 : q'.p ^ q'.exponent = q.p ^ q.exponent := by
              rw [← TauCeti.PrimePower.card_def, ← TauCeti.PrimePower.card_def]
              exact hcard'.trans hq8.symm
            rw [hp', hringch, hp2] at h1
            exact Nat.pow_right_injective (le_refl 2) h1
        subst hq'
        have hproj : ↥(CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) ⧸
            Subgroup.center ↥(CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) ≃*
            CFSG.Open.StatedProj
              (CFSG.Open.StatedSU 3 8 (GaloisField q'.p (2 * q'.exponent))) :=
          CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_su
            (K := GaloisField q'.p (2 * q'.exponent)) (q := 8) hcardK (by norm_num)
            (by norm_num) (MulEquiv.refl _)
        exact ⟨GaloisField q'.p (2 * q'.exponent), inferInstance, inferInstance, hchar, hcardK,
          ⟨e.trans (eSU.symm.trans hproj)⟩⟩
      · simp [isU3eight, onLie, hr] at hi
    | _ => simp [isU3eight, onLie] at hi

section Certificates

set_option linter.unusedSectionVars false


private theorem twE6Cov_card_hopfMultiplier_PSU_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 8 ^ 2) {G : Type} [Group G]
    (e : G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 8 K)) :
    Nat.card (hopfMultiplier G) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (F := K) (p := 2) (f := 3) (by rw [hK]; norm_num) (by norm_num) (n := 3) (by norm_num)
    (by decide) (by decide)
  have hcard : Nat.card (griessHopfMultiplier
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 3) K))) = 3 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    norm_num
  have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [h8] at hcard
  rw [← Nat.card_congr (hopfMultiplierEquivGriess G).toEquiv,
    Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
  exact hcard

theorem twE6Cov_exists_statedSU {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (hZ : Subgroup.center X ≠ ⊥) (hcat : catalogIs (X ⧸ Subgroup.center X) isU3eight) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ^ 2 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU 3 8 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect X := ⟨hX.1⟩
  obtain ⟨K, hKfield, hKfin, hchar, hK64, ⟨eY⟩⟩ := twE6Cov_exists_statedSU_of_isU3eight hcat
  letI : Field K := hKfield
  haveI : Finite K := hKfin
  haveI : CharP K 2 := hchar
  haveI : Fintype K := Fintype.ofFinite K
  have hcard3 : Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) = 3 :=
    twE6Cov_card_hopfMultiplier_PSU_three hK64 eY
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 :=
    (CFSG.RankThree.PerfectCover.card_center_dvd_hopf hperf).trans hcard3.dvd
  have hHperf : Group.IsPerfect ↥(CFSG.Open.StatedSU 3 8 K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2) (f := 3)
      (n := 3) (by rw [hK64]; norm_num) le_rfl (by norm_num)).1.1
  have hZH : Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K)) = 3 :=
    CFSG.Open.StatedCenterThree.card_center_statedSU_three hK64 (by norm_num)
  have eHL : ↥(CFSG.Open.StatedSU 3 8 K) ⧸
      Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K) ≃* X ⧸ Subgroup.center X :=
    (CFSG.LocalAnalysis.GLTheoremA.H1419.projective_of_su (K := K) (q := 8) hK64
      (by norm_num) (by norm_num) (MulEquiv.refl _)).trans eY.symm
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZ
  · have hnot9 : ¬ 9 ∣ Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
      rw [hcard3]
      norm_num
    obtain ⟨eXH⟩ := CFSG.RankThree.PerfectCover.unique_three_cover hperf hHperf
      (CFSG.RankThree.PerfectCover.centralQuotientMap (MulEquiv.refl (X ⧸ Subgroup.center X)))
      (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective _)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_ker _).le
      (CFSG.RankThree.PerfectCover.centralQuotientMap eHL)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective _)
      (CFSG.RankThree.PerfectCover.centralQuotientMap_ker _).le
      (by rw [CFSG.RankThree.PerfectCover.centralQuotientMap_ker]; exact h3)
      (by rw [CFSG.RankThree.PerfectCover.centralQuotientMap_ker]; exact hZH)
      hnot9
    exact ⟨K, hKfield, hKfin, hK64, ⟨eXH⟩⟩

end Certificates

section Cube

open Matrix

private noncomputable def twE6CovDiag {K : Type} [Field K] (a : K) (ha : a ^ 9 = 1) :
    GL (Fin 3) K :=
  ⟨diagonal ![a, a, a ^ 7], diagonal ![a ^ 8, a ^ 8, a ^ 2],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · show a * a ^ 8 = 1
        linear_combination ha
      · show a * a ^ 8 = 1
        linear_combination ha
      · show a ^ 7 * a ^ 2 = 1
        linear_combination ha,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · show a ^ 8 * a = 1
        linear_combination ha
      · show a ^ 8 * a = 1
        linear_combination ha
      · show a ^ 2 * a ^ 7 = 1
        linear_combination ha⟩

private theorem twE6CovDiag_mem {K : Type} [Field K] {a : K} (ha : a ^ 9 = 1) :
    twE6CovDiag a ha ∈ CFSG.Open.StatedSU 3 8 K := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · change (diagonal ![a, a, a ^ 7] : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    calc a * a * a ^ 7 = a ^ 9 := by ring
      _ = 1 := ha
  · change ((diagonal ![a, a, a ^ 7] : Matrix (Fin 3) (Fin 3) K).map (· ^ 8))ᵀ *
      diagonal ![a, a, a ^ 7] = 1
    rw [diagonal_map (f := fun x : K => x ^ 8) (zero_pow (by norm_num)), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, ← pow_succ]
      simpa using ha
    · simp only [Fin.mk_one, Matrix.cons_val_one, ← pow_succ]
      simpa using ha
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two]
      calc (a ^ 7) ^ 8 * a ^ 7 = (a ^ 9) ^ 7 := by ring
        _ = 1 := by rw [ha, one_pow]

theorem twE6Cov_su38_cube {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8 ^ 2) :
    ∃ u : ↥(CFSG.Open.StatedSU 3 8 K), u ^ 3 ∈ Subgroup.center ↥(CFSG.Open.StatedSU 3 8 K) ∧
      u ^ 3 ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := CFSG.Open.StatedCenterThree.exists_orderOf_eq hK
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hζ9' : (ζ : K) ^ 9 = 1 := by
    have := congrArg Units.val hζ9
    simpa using this
  have hc : (ζ ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hζ9
  have hq : (8 : ℕ) ≠ 0 := by norm_num
  have hcube : ((twE6CovDiag (ζ : K) hζ9' : GL (Fin 3) K)) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change (diagonal ![(ζ : K), (ζ : K), (ζ : K) ^ 7] : Matrix (Fin 3) (Fin 3) K) ^ 3 = _
    rw [diagonal_pow]
    congr 1
    funext i
    fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Pi.pow_apply, Units.val_pow_eq_pow_val]
      calc ((ζ : K) ^ 7) ^ 3 = ((ζ : K) ^ 9) ^ 2 * (ζ : K) ^ 3 := by ring
        _ = (ζ : K) ^ 3 := by rw [hζ9', one_pow, one_mul]
  refine ⟨⟨twE6CovDiag (ζ : K) hζ9', twE6CovDiag_mem hζ9'⟩, ?_, ?_⟩
  · have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) : GL (Fin 3) K) ∈
        CFSG.Open.StatedSU 3 8 K :=
      CFSG.Open.StatedCenterThree.scalar_mem hq (by norm_num) hc
    have h1 : (⟨twE6CovDiag (ζ : K) hζ9', twE6CovDiag_mem hζ9'⟩ :
        ↥(CFSG.Open.StatedSU 3 8 K)) ^ 3 = ⟨_, hmem⟩ := Subtype.ext hcube
    rw [h1]
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Matrix.GeneralLinearGroup.scalar_commute (ζ ^ 3) (g : GL (Fin 3) K)).symm
  · intro h
    have h1 : (⟨twE6CovDiag (ζ : K) hζ9', twE6CovDiag_mem hζ9'⟩ :
        ↥(CFSG.Open.StatedSU 3 8 K)) ^ 3 = 1 := h
    have h2 : ((twE6CovDiag (ζ : K) hζ9' : GL (Fin 3) K)) ^ 3 = 1 :=
      congrArg Subtype.val h1
    rw [hcube] at h2
    have h3 := congrArg (fun A : GL (Fin 3) K => ((A : Matrix (Fin 3) (Fin 3) K) 0 0)) h2
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.val_pow_eq_pow_val, Units.val_one, Matrix.one_apply_eq] at h3
    have h4 : ζ ^ 3 = 1 := Units.ext (by simpa using h3)
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hζ] at h5
    norm_num at h5

end Cube

end CFSG.LocalAnalysis.GLTheoremA.I141F

end
