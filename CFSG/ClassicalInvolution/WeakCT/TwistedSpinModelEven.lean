module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDPairE
import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6SU6
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.CTP.SU4Even CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped Matrix MatrixGroups

section Even

variable {F K : Type} [Field F] [Field K] {b c : F}

private theorem conjTr_diagonal (σ : K ≃+* K) (d : Fin 4 → K) :
    conjTr σ (Matrix.diagonal d) = Matrix.diagonal fun i => σ (d i) := by
  rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]

private theorem conjTr_dmat_mul_unitaryJInv_mul_dmat [Algebra F K] {σ : K ≃+* K}
    (D : KleinDataEven F K σ b c) :
    conjTr σ (CompsPTwoDPairE.dmat D) * unitaryJInv * CompsPTwoDPairE.dmat D =
      D.δ • antidiag 4 := by
  have h := D.σ_δ
  rw [CompsPTwoDPairE.dmat, conjTr_diagonal]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [unitaryJInv, antidiag, h, Fin.rev]

private theorem conjTr_dinv_mul_antidiag_mul_dinv [Algebra F K] {σ : K ≃+* K}
    (D : KleinDataEven F K σ b c) :
    conjTr σ (CompsPTwoDPairE.dinv D) * antidiag 4 * CompsPTwoDPairE.dinv D =
      D.ε • unitaryJInv := by
  have h := D.σ_ε
  rw [CompsPTwoDPairE.dinv, conjTr_diagonal]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [unitaryJInv, antidiag, h, Fin.rev]

variable [Finite F] [CharP F 2] [Finite K] [CharP K 2] {f : ℕ}

theorem exists_spinMinus6_equiv_unitaryGroup_even [Algebra F K]
    (D : KleinDataEven F K (unitaryInvolution K 2 f) b c) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (hθ : ∀ x, (unitaryInvolution K 2 f).toRingHom ((unitaryInvolution K 2 f).toRingHom x) = x) :
    ∃ Θ : spinGroup (quadMinus 3 F b c) ≃* unitaryGroup (unitaryInvolution K 2 f).toRingHom hθ,
      (minusLongBlock b c).range.map Θ.toMonoidHom =
          (ulb (unitaryInvolution K 2 f).toRingHom hθ).range ∧
        (shortBlock hirr 3 finOne).range.map Θ.toMonoidHom =
          (usb (unitaryInvolution K 2 f).toRingHom hθ).range := by
  set σ := unitaryInvolution K 2 f with hσdef
  set θ : K →+* K := σ.toRingHom with hθdef
  have hσθ : involEquiv θ hθ = σ := RingEquiv.ext fun _ => rfl
  have hmem : ∀ s, CompsPTwoDPairE.theta D hirr s ∈ unitaryGroup θ hθ := by
    intro s
    have htop := spinMinus6_blocks_sup_eq_top_even hirr
    change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
    have hs : s ∈ (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range := by
      rw [htop]
      exact Subgroup.mem_top s
    refine (sup_le ?_ ?_ : _ ≤ (unitaryGroup θ hθ).comap (CompsPTwoDPairE.theta D hirr)) hs
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_comap, mem_unitaryGroup, hσθ]
      have h := congrArg (fun φ => φ A) (CompsPTwoDPairE.theta_comp_lb (D := D) (hirr := hirr))
      simp only [MonoidHom.comp_apply] at h
      rw [h, sigmaA_blockSL2_one]
      congr 1
      exact Subtype.ext (Matrix.ext fun _ _ => D.σ_alg _)
    · rintro _ ⟨B, rfl⟩
      rw [Subgroup.mem_comap]
      obtain ⟨B', hB'⟩ : CompsPTwoDPairE.theta D hirr (shortBlock hirr 3 finOne B) ∈
          (usbSL θ hθ).range := by
        rw [← CompsPTwoDPairE.range_theta_sb (D := D) (hirr := hirr)]
        exact ⟨B, rfl⟩
      rw [← hB']
      exact usbSL_mem θ hθ B'
  let Θ' : spinGroup (quadMinus 3 F b c) →* unitaryGroup θ hθ :=
    (CompsPTwoDPairE.theta D hirr).codRestrict _ hmem
  have hΘ' : ∀ s, ((Θ' s : unitaryGroup θ hθ) : SL(4, K)) = CompsPTwoDPairE.theta D hirr s :=
    fun _ => rfl
  have hinj : Function.Injective Θ' := by
    intro s t hst
    have h1 : conjSL (CompsPTwoDPairE.dmat D) (CompsPTwoDPairE.dinv D)
          (CompsPTwoDPairE.dmat_mul_dinv D) (CompsPTwoDPairE.suToSL σ (D.PhiSUEven hirr s)) =
        conjSL (CompsPTwoDPairE.dmat D) (CompsPTwoDPairE.dinv D)
          (CompsPTwoDPairE.dmat_mul_dinv D) (CompsPTwoDPairE.suToSL σ (D.PhiSUEven hirr t)) :=
      congrArg Subtype.val hst
    have h2 := (conjSL (CompsPTwoDPairE.dmat D) (CompsPTwoDPairE.dinv D)
      (CompsPTwoDPairE.dmat_mul_dinv D)).injective h1
    apply D.PhiSUEven_injective hirr
    exact Subtype.ext (Units.ext (congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K)) h2))
  have hsurj : Function.Surjective Θ' := by
    rintro ⟨g, hg⟩
    have hg' : sigmaA σ g = g := by
      rw [← hσθ]
      exact hg
    have hform := CFSG.ClassicalInvolution.RouteD.conjTr_mul_unitaryJInv_mul_of_sigmaA σ hg'
    have hdm : CompsPTwoDPairE.dinv D * CompsPTwoDPairE.dmat D = 1 :=
      mul_eq_one_comm.mp (CompsPTwoDPairE.dmat_mul_dinv D)
    set M : Matrix (Fin 4) (Fin 4) K :=
      CompsPTwoDPairE.dinv D * (g : Matrix (Fin 4) (Fin 4) K) * CompsPTwoDPairE.dmat D with hM
    have hdet : M.det = 1 := by
      rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
        ← Matrix.det_mul, hdm, Matrix.det_one]
    have hMform : conjTr σ M * antidiag 4 * M = antidiag 4 := by
      calc conjTr σ M * antidiag 4 * M
          = conjTr σ (CompsPTwoDPairE.dmat D) * (conjTr σ (g : Matrix (Fin 4) (Fin 4) K) *
              (conjTr σ (CompsPTwoDPairE.dinv D) * antidiag 4 * CompsPTwoDPairE.dinv D) *
                (g : Matrix (Fin 4) (Fin 4) K)) * CompsPTwoDPairE.dmat D := by
            simp only [hM, conjTr_mul, Matrix.mul_assoc]
        _ = D.ε • (conjTr σ (CompsPTwoDPairE.dmat D) * (conjTr σ (g : Matrix (Fin 4) (Fin 4) K) *
              unitaryJInv * (g : Matrix (Fin 4) (Fin 4) K)) * CompsPTwoDPairE.dmat D) := by
            rw [conjTr_dinv_mul_antidiag_mul_dinv]
            simp only [Matrix.mul_smul, Matrix.smul_mul]
        _ = D.ε • (D.δ • antidiag 4) := by
            rw [hform, conjTr_dmat_mul_unitaryJInv_mul_dmat]
        _ = antidiag 4 := by
            rw [smul_smul, mul_comm, D.δ_mul_ε, one_smul]
    let P : SU σ 4 := ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hdet⟩, mem_SU.mpr ⟨hdet, hMform⟩⟩
    obtain ⟨s, hs⟩ : P ∈ (D.PhiSUEven hirr).range := by
      rw [D.range_PhiSUEven_eq_top hK hirr]
      exact Subgroup.mem_top P
    have hPM : D.PhiMon s = M := by
      rw [← D.coe_PhiSUEven hirr s, hs]
      rfl
    refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
    change CompsPTwoDPairE.dmat D * D.PhiMon s * CompsPTwoDPairE.dinv D =
      (g : Matrix (Fin 4) (Fin 4) K)
    rw [hPM, hM]
    simp only [← Matrix.mul_assoc, CompsPTwoDPairE.dmat_mul_dinv, Matrix.one_mul]
    rw [Matrix.mul_assoc, CompsPTwoDPairE.dmat_mul_dinv, Matrix.mul_one]
  let Θ : spinGroup (quadMinus 3 F b c) ≃* unitaryGroup θ hθ :=
    MulEquiv.ofBijective Θ' ⟨hinj, hsurj⟩
  have hΘ : Θ.toMonoidHom = Θ' := MonoidHom.ext fun _ => rfl
  refine ⟨Θ, ?_, ?_⟩
  ·
    let ι : F →+* fixedField θ :=
      (algebraMap F K).codRestrict (fixedField θ) fun r => D.σ_alg r
    have hιsurj : Function.Surjective ι := by
      rintro ⟨y, hy⟩
      obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := y) hy
      exact ⟨r, Subtype.ext hr⟩
    let ιe : F ≃+* fixedField θ := RingEquiv.ofBijective ι ⟨ι.injective, hιsurj⟩
    have hlb : Θ'.comp (minusLongBlock b c) =
        (ulb θ hθ).comp (Matrix.SpecialLinearGroup.map (ιe : F →+* fixedField θ)) := by
      refine MonoidHom.ext fun A => Subtype.ext ?_
      have h := congrArg (fun φ => φ A) (CompsPTwoDPairE.theta_comp_lb (D := D) (hirr := hirr))
      simp only [MonoidHom.comp_apply] at h
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hΘ', h, coe_ulb]
      rfl
    have hmap : (Matrix.SpecialLinearGroup.map (n := Fin 2) (ιe : F →+* fixedField θ)).range =
        ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro A
      refine ⟨Matrix.SpecialLinearGroup.map (ιe.symm : fixedField θ →+* F) A, ?_⟩
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rw [hΘ, ← MonoidHom.range_comp, hlb, MonoidHom.range_comp, hmap, ← MonoidHom.range_eq_map]
  · apply Subgroup.map_injective (unitaryGroup θ hθ).subtype_injective
    rw [Subgroup.map_map, hΘ]
    have hcomp : (unitaryGroup θ hθ).subtype.comp Θ' = CompsPTwoDPairE.theta D hirr :=
      MonoidHom.ext fun _ => rfl
    have husb : (unitaryGroup θ hθ).subtype.comp (usb θ hθ) = usbSL θ hθ :=
      MonoidHom.ext fun B => coe_usb θ hθ B
    rw [hcomp, ← MonoidHom.range_comp, ← MonoidHom.range_comp, husb]
    exact CompsPTwoDPairE.range_theta_sb (D := D) (hirr := hirr)

theorem unitaryB2BlockStandardPair_minusDatum_even (hF : Nat.card F = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {θ : K →+* K} (hθ : ∀ x, θ (θ x) = x)
    (hθf : ∀ x, θ x = x ^ 2 ^ f) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin (n - 1)} (hia : i.val + 3 = n) (hjb : j.val + 2 = n) :
    ∃ W, UnitaryB2BlockStandardPair θ hθ W
        (CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup i)
        (CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup j) ∧
      W ≤ CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup i ⊔
        CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup j := by
  have := fact_shortField hirr
  obtain rfl : θ = (unitaryInvolution K 2 f).toRingHom :=
    RingHom.ext fun x => (hθf x).trans (unitaryInvolution_apply K 2 f x).symm
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hF hK hirr
  obtain ⟨Θ, hl, hs⟩ := exists_spinMinus6_equiv_unitaryGroup_even D hK hirr hθ
  have hi : i.val + 1 < n - 1 := by omega
  have hj : ¬ j.val + 1 < n - 1 := by omega
  have hinj := spinGroupMap_minusShift_injective_even n hn hirr
  have hL := minusShift_comp_longBlock (b := b) (c := c) hn hia hi
  have hS := minusShift_comp_shortBlock hn hirr hjb
  let φ : unitaryGroup (unitaryInvolution K 2 f).toRingHom hθ →* spinGroup (quadMinus n F b c) :=
    (minusShift n hn b c).spinGroupMap.comp Θ.symm.toMonoidHom
  have hφ : Function.Injective φ := hinj.comp Θ.symm.injective
  have hφΘ : φ.comp Θ.toMonoidHom = (minusShift n hn b c).spinGroupMap := by
    refine MonoidHom.ext fun s => ?_
    change (minusShift n hn b c).spinGroupMap (Θ.symm (Θ s)) = (minusShift n hn b c).spinGroupMap s
    rw [MulEquiv.symm_apply_apply]
  have hU : (ulb _ hθ).range.map φ =
      CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup i := by
    rw [← hl, Subgroup.map_map, hφΘ, ← MonoidHom.range_comp, hL, rankOne_minusDatum_long hirr hi]
  have hV : (usb _ hθ).range.map φ =
      CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup j := by
    rw [← hs, Subgroup.map_map, hφΘ, ← MonoidHom.range_comp, hS, rankOne_minusDatum_short hirr hj]
  refine ⟨φ.range, ⟨φ, rfl, ?_, hφ.comp (ulb_injective _ hθ), hφ.comp (usb_injective _ hθ), hU,
    hV⟩, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hφ]
    exact bot_le
  · have htop := spinMinus6_blocks_sup_eq_top_even hirr
    change (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ at htop
    have hW : φ.range = (ulb _ hθ).range.map φ ⊔ (usb _ hθ).range.map φ := by
      rw [← Subgroup.map_sup, ← hl, ← hs, ← Subgroup.map_sup, htop,
        Subgroup.map_top_of_surjective _ Θ.surjective, MonoidHom.range_eq_map]
    rw [hW, hU, hV]

end Even

end CFSG.ClassicalInvolution.WeakCT

end
