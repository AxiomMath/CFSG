module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import CFSG.Open.StatedDefs
public import Certificates.Certificate8052
import CFSG.RankThree.PartOne.KF.BloomClose
import CFSG.RankThree.PartOne.S12.LA126
import CFSG.RankThree.PartOne.KF.F1322OmegaIdx
import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.Quasithin.EmptyFaithful.A38c15IrrBasic
import CFSG.RankThree.PartOne.LIT.OrthogonalTransport
import CFSG.Open.StatedAPI
import CFSG.LieType.SteinbergBRTwoRankBound
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.SubgroupLists

theorem exists_smul_transpose_mul_of_normalizes_omegaGL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep
      (CFSG.RankThree.SubgroupLists.omegaGL M).subtype)
    {g : GL (Fin 3) (ZMod p)}
    (hg : ∀ x ∈ CFSG.RankThree.SubgroupLists.omegaGL M,
      g * x * g⁻¹ ∈ CFSG.RankThree.SubgroupLists.omegaGL M) :
    ∃ l : ZMod p, (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = l • M := by
  have hΩ₀ : ∀ h ∈ omegaGL M, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      (h : Matrix (Fin 3) (Fin 3) (ZMod p)) = M := fun h hh =>
    (CFSG.RankThree.SubgroupLists.mem_soGL.mp
      (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M hh)).1
  have hinv : ∀ h ∈ omegaGL M, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
      ((g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p))) *
      (h : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    intro h hh
    exact (CFSG.RankThree.SubgroupLists.mem_soGL.mp
      ((CFSG.RankThree.PartOne.LIT.mem_soGL_congr g M h).mpr
        (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M (hg h hh)))).1
  obtain ⟨l, hl⟩ := CFSG.Quasithin.A38c15.omega_commutant_scalar hp2 hMt hMd hirr
    (S := M⁻¹ * ((g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p))))
    (fun h hh => CFSG.Quasithin.A38c15.commute_inv_mul_forms hMd
      (hΩ₀ h hh) (hinv h hh))
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hMd
  refine ⟨l, ?_⟩
  calc (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p))
      = (M * M⁻¹) * ((g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
          (g : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    _ = M * (M⁻¹ * ((g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)))) := by rw [Matrix.mul_assoc]
    _ = M * Matrix.scalar (Fin 3) l := by rw [hl]
    _ = l • M := by
        ext i j
        simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

theorem transpose_pow_mul_pow_of_smul {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring K] {M : Matrix σ σ K} {g : GL σ K} {l : K}
    (h : (g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K) = l • M) (m : ℕ) :
    (((g ^ m : GL σ K) : Matrix σ σ K))ᵀ * M *
      ((g ^ m : GL σ K) : Matrix σ σ K) = l ^ m • M := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, Matrix.transpose_mul]
    calc (g : Matrix σ σ K)ᵀ * ((g ^ m : GL σ K) : Matrix σ σ K)ᵀ * M *
          (((g ^ m : GL σ K) : Matrix σ σ K) * (g : Matrix σ σ K))
        = (g : Matrix σ σ K)ᵀ *
            (((g ^ m : GL σ K) : Matrix σ σ K)ᵀ * M *
              ((g ^ m : GL σ K) : Matrix σ σ K)) *
            (g : Matrix σ σ K) := by
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix σ σ K)ᵀ * (l ^ m • M) * (g : Matrix σ σ K) := by rw [ih]
      _ = l ^ m • ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = l ^ m • (l • M) := by rw [h]
      _ = l ^ (m + 1) • M := by rw [pow_succ', smul_smul, mul_comm]

theorem isometry_of_normalizes_omegaGL_of_orderOf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep
      (CFSG.RankThree.SubgroupLists.omegaGL M).subtype)
    {g : GL (Fin 3) (ZMod p)}
    (hg : ∀ x ∈ CFSG.RankThree.SubgroupLists.omegaGL M,
      g * x * g⁻¹ ∈ CFSG.RankThree.SubgroupLists.omegaGL M)
    {k : ℕ} (hk : orderOf g = p ^ k) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = M := by
  obtain ⟨l, hl⟩ := exists_smul_transpose_mul_of_normalizes_omegaGL hp2 hMt hMd hirr hg
  have hord : g ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have hstep := transpose_pow_mul_pow_of_smul hl (p ^ k)
  rw [hord, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hstep
  have hMne : M ≠ 0 := by
    intro h0
    exact hMd (by rw [h0, Matrix.det_zero])
  have hlpow : l ^ (p ^ k) = 1 := by
    by_contra hne
    have hzero : (l ^ (p ^ k) - 1) • M = 0 := by
      rw [sub_smul, one_smul, ← hstep, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hMne h
  have hl1 : l = 1 := by
    rw [← ZMod.pow_card_pow (n := k) l]
    exact hlpow
  rw [hl, hl1, one_smul]

theorem le_omegaGL_of_oPPrimeHull_of_normalizes {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep
      (CFSG.RankThree.SubgroupLists.omegaGL M).subtype)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hH : oPPrimeHull p H = H)
    (hnorm : ∀ g ∈ H, ∀ x ∈ CFSG.RankThree.SubgroupLists.omegaGL M,
      g * x * g⁻¹ ∈ CFSG.RankThree.SubgroupLists.omegaGL M) :
    H ≤ CFSG.RankThree.SubgroupLists.omegaGL M := by
  have hp2 : p ≠ 2 := by omega
  rw [← hH]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro x ⟨hxH, k, hk⟩
  have hiso := isometry_of_normalizes_omegaGL_of_orderOf hp2 hMt hMd hirr (hnorm x hxH) hk
  have hdet := det_eq_one_of_orderOf_eq_prime_pow hk
  have hxso : x ∈ CFSG.RankThree.SubgroupLists.soGL M :=
    CFSG.RankThree.SubgroupLists.mem_soGL.mpr ⟨hiso, hdet⟩
  have hxsq : x * x ∈ CFSG.RankThree.SubgroupLists.omegaGL M :=
    CFSG.RankThree.PartOne.KF1322.sq_mem_omegaGL hp5 hMt hMd hxso
  have hodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2).pow
  have hxk : x ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hxeq : x = (x * x) ^ ((p ^ k + 1) / 2) := by
    obtain ⟨m, hm⟩ := hodd
    have hhalf : (p ^ k + 1) / 2 = m + 1 := by omega
    have htwo : 2 * (m + 1) = p ^ k + 1 := by omega
    rw [hhalf, ← pow_two, ← pow_mul, htwo, pow_succ, hxk, one_mul]
  rw [hxeq]
  exact (CFSG.RankThree.SubgroupLists.omegaGL M).pow_mem hxsq _

section


theorem sl3_or_psl2_of_irreducible {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {H : Subgroup (GL (Fin 3) (ZMod p))} (hH : oPPrimeHull p H = H)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) :
    IsSLType 3 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨
      IsPSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) := by
  have hpdvd := dvd_card_of_oPPrimeHull_of_ne_bot hH
    (CFSG.RankThree.PartOne.LA126.ne_bot_of_isIrreducibleMatrixRep H hirr)
  obtain ⟨K, hKle, hKnorm, hKirr, -, hKcases⟩ :=
    CFSG.RankThree.PartOne.extBloomPrime_holds p hp5 hirr hpdvd
  have hHleSL := le_statedSL_of_oPPrimeHull hH
  have hpc : CFSG.pCore p ↥H = ⊥ := pCore_eq_bot_of_isIrreducibleMatrixRep hirr
  rcases hKcases with hK | ⟨M, hMt, hMd, hK⟩
  · left
    have hHeq : H = CFSG.Open.StatedSL 3 (ZMod p) := le_antisymm hHleSL (hK ▸ hKle)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans <|
      QuotientGroup.quotientBot.trans <|
        (MulEquiv.subgroupCongr hHeq).trans
          (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod p))⟩
  · right
    have hnorm : ∀ g ∈ H, ∀ x ∈ CFSG.RankThree.SubgroupLists.omegaGL M,
        g * x * g⁻¹ ∈ CFSG.RankThree.SubgroupLists.omegaGL M := by
      intro g hg x hx
      have hxK : x ∈ K := by rw [hK]; exact hx
      have h := hKnorm g hg x hxK
      rwa [hK] at h
    have hHeq : H = CFSG.RankThree.SubgroupLists.omegaGL M := le_antisymm
      (le_omegaGL_of_oPPrimeHull_of_normalizes hp5 hMt hMd (hK ▸ hKirr) hH hnorm)
      (hK ▸ hKle)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans <|
      QuotientGroup.quotientBot.trans <|
        (MulEquiv.subgroupCongr hHeq).trans
          (CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp5 hMt hMd).some⟩

end

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
