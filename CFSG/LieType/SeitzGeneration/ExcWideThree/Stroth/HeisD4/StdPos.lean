module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Defs
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

@[expose] def stdWord : List (Fin Tag.E6.rank) := [5, 4, 3, 1, 0]

@[expose] def stdChar : Fin Tag.E6.rank → ZMod 3 := ![2, 0, 0, 0, 0, 2]

theorem stdWord_check : ∀ l ∈ Tag.E6.artifactRoots,
    (triPairing repD (fun i : Fin Tag.E6.rank => l.getD i 0) = 0 ↔
      ((wordAct Tag.E6 stdWord (fun i : Fin Tag.E6.rank => l.getD i 0)) 0 = 0 ∧
        (wordAct Tag.E6 stdWord (fun i : Fin Tag.E6.rank => l.getD i 0)) 5 = 0)) := by
  decide +kernel

theorem stdChar_check : ∀ i : Fin Tag.E6.rank,
    triPairing stdChar (wordAct Tag.E6 stdWord (Pi.single i 1)) =
      triPairing repD (Pi.single i 1) := by
  decide +kernel

@[expose] def stdV : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd stdWord

@[expose] def wBeta : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd d4TrialityWord

theorem wBeta_stab_check : ∀ i : Fin Tag.E6.rank,
    triPairing stdChar (wordAct Tag.E6 d4TrialityWord (Pi.single i 1)) =
      triPairing stdChar (Pi.single i 1) := by
  decide +kernel

theorem wBeta_shift_check : ∀ i : Fin Tag.E6.rank,
    (3 : ℤ) * (![-2, -1, -2, -2, -1, 0] : Fin Tag.E6.rank → ℤ) i =
      wordAct Tag.E6 d4TrialityWord e6Omega3 i - e6Omega3 i := by
  decide +kernel

theorem stdChar_shift_wBeta_check :
    triPairing stdChar (![-2, -1, -2, -2, -1, 0] : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  decide +kernel

@[expose] def triPairingHom (b : Fin Tag.E6.rank → ZMod 3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 where
  toFun := triPairing b
  map_zero' := triPairing_zero b
  map_add' := triPairing_add b

theorem triPairingHom_apply (b : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    triPairingHom b v = triPairing b v := rfl

theorem pi_eq_sum_single (v : Fin Tag.E6.rank → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem triPairing_smul_eq_of_basis {b b' : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup Tag.E6}
    (h : ∀ i, triPairing b (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      triPairing b' (Pi.single i 1)) (v : Fin Tag.E6.rank → ℤ) :
    triPairing b (w • v) = triPairing b' v := by
  conv_lhs => rw [pi_eq_sum_single v, Finset.smul_sum]
  conv_rhs => rw [pi_eq_sum_single v]
  rw [← triPairingHom_apply, ← triPairingHom_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, map_zsmul, map_zsmul, triPairingHom_apply, triPairingHom_apply, h i]

theorem stdChar_smul (x : Fin Tag.E6.rank → ℤ) :
    triPairing stdChar (stdV • x) = triPairing repD x := by
  refine triPairing_smul_eq_of_basis (fun i => ?_) x
  rw [stdV, ← wordAct_eq_smul]
  exact stdChar_check i

theorem mem_charStabilizer_wBeta : wBeta ∈ charStabilizer (triChar stdChar) := by
  intro v
  rw [triChar_apply, triChar_apply]
  congr 1
  refine triPairing_smul_eq_of_basis (b' := stdChar) (fun i => ?_) v
  rw [wBeta, ← wordAct_eq_smul]
  exact wBeta_stab_check i

theorem triPairing_e6Shift_wBeta : triPairing stdChar (e6Shift wBeta) ≠ 0 := by
  have : e6Shift wBeta = ![-2, -1, -2, -2, -1, 0] := by
    refine e6Shift_eq_of_three_smul ?_
    rw [wBeta, ← wordAct_eq_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    exact wBeta_shift_check i
  rw [this]
  exact stdChar_shift_wBeta_check

theorem ofFn_getD (α : Fin Tag.E6.rank → ℤ) :
    (fun i : Fin Tag.E6.rank => (List.ofFn α).getD i 0) = α := by
  funext i
  simp

theorem stdChar_kernel_check : ∀ l ∈ Tag.E6.artifactRoots,
    (triPairing stdChar (fun i : Fin Tag.E6.rank => l.getD i 0) = 0 ↔
      ((fun i : Fin Tag.E6.rank => l.getD i 0) 0 = 0 ∧
        (fun i : Fin Tag.E6.rank => l.getD i 0) 5 = 0)) := by
  decide +kernel

theorem mem_parabolicRoots_d4Support_iff' {α : Fin Tag.E6.rank → ℤ} :
    α ∈ parabolicRoots Tag.E6 d4Support ↔ IsRoot Tag.E6 α ∧ α 0 = 0 ∧ α 5 = 0 := by
  refine and_congr_right fun _ => ⟨fun h => ⟨h 0 (by simp [d4Support]), h 5 (by simp [d4Support])⟩,
    fun ⟨h0, h5⟩ i hi => ?_⟩
  rw [d4Support, Set.mem_setOf_eq, not_and_or, not_not, not_not] at hi
  rcases hi with rfl | rfl
  · exact h0
  · exact h5

theorem mem_kernelRoots_stdChar {α : Fin Tag.E6.rank → ℤ} :
    α ∈ kernelRoots (triChar stdChar) ↔ α ∈ parabolicRoots Tag.E6 d4Support := by
  rw [mem_kernelRoots_triChar, mem_parabolicRoots_d4Support_iff']
  refine and_congr_right fun hα => ?_
  have h := stdChar_kernel_check (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
  rwa [ofFn_getD] at h

theorem charStab_conj_of_pair {b b' : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup Tag.E6}
    (hpair : ∀ v, triPairing b (t • v) = triPairing b' v) {w : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar b')) : t * w * t⁻¹ ∈ charStabilizer (triChar b) := by
  intro v
  rw [triChar_apply, triChar_apply]
  congr 1
  have h1 : triPairing b ((t * w * t⁻¹) • v) = triPairing b' (w • (t⁻¹ • v)) := by
    rw [mul_smul, mul_smul]
    exact hpair _
  rw [h1, triPairing_smul_of_mem hw, ← hpair, smul_inv_smul]

theorem shift_conj_of_pair {b b' : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup Tag.E6}
    (hpair : ∀ v, triPairing b (t • v) = triPairing b' v) {w : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar b')) :
    triPairing b (e6Shift (t * w * t⁻¹)) = triPairing b' (e6Shift w) := by
  have hinv : t • e6Shift t⁻¹ + e6Shift t = 0 := by
    rw [← e6Shift_mul, mul_inv_cancel, e6Shift_one]
  have e1 : e6Shift (t * w * t⁻¹) = t • (w • e6Shift t⁻¹) + t • e6Shift w + e6Shift t := by
    rw [mul_assoc, e6Shift_mul, e6Shift_mul, smul_add]
  have e2 : triPairing b (e6Shift t) + triPairing b' (e6Shift t⁻¹) = 0 := by
    have := congrArg (triPairing b) hinv
    rw [triPairing_add, hpair, triPairing_zero] at this
    linear_combination this
  rw [e1, triPairing_add, triPairing_add, hpair, hpair, triPairing_smul_of_mem hw]
  linear_combination e2

theorem stdPosition {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6}
    (h : HeisClassD a w) :
    ∃ s : WeylGroup Tag.E6,
      (∀ α, IsRoot Tag.E6 α → (rootChar a α = 1 ↔ s • α ∈ parabolicRoots Tag.E6 d4Support)) ∧
      s * w * s⁻¹ ∈ charStabilizer (triChar stdChar) ∧
      triPairing stdChar (e6Shift (s * w * s⁻¹)) ≠ 0 := by
  obtain ⟨b, t, hker, hpair, hwt, hsht⟩ := h
  have hpair' : ∀ v, triPairing stdChar (stdV • v) = triPairing repD v := stdChar_smul
  have hconj : (stdV * t⁻¹) * w * (stdV * t⁻¹)⁻¹ = stdV * (t⁻¹ * w * t) * stdV⁻¹ := by group
  refine ⟨stdV * t⁻¹, ?_, ?_, ?_⟩
  · intro α hα
    have hα' : IsRoot Tag.E6 (t⁻¹ • α) := IsRoot.smul hα t⁻¹
    have h1 : triPairing b α = triPairing repD (t⁻¹ • α) := by
      have := hpair (t⁻¹ • α)
      rwa [smul_inv_smul] at this
    have h2 := stdWord_check (List.ofFn (t⁻¹ • α)) (isRoot_iff_mem_artifactRoots.1 hα')
    rw [ofFn_getD, wordAct_eq_smul] at h2
    have h3 : (stdV * t⁻¹) • α = (coxeterSystem Tag.E6).wordProd stdWord • (t⁻¹ • α) := by
      rw [mul_smul]
      rfl
    rw [h3, mem_parabolicRoots_d4Support_iff']
    have h4 : rootChar a α = 1 ↔ triPairing b α = 0 := by
      have := hker α
      rw [mem_kernelRoots_triChar] at this
      constructor
      · intro hc
        exact (this.1 ⟨hα, hc⟩).2
      · intro hc
        exact (this.2 ⟨hα, hc⟩).2
    rw [h4, h1, h2]
    exact ⟨fun hh => ⟨IsRoot.smul hα' _, hh⟩, fun hh => hh.2⟩
  · rw [hconj]
    exact charStab_conj_of_pair hpair' hwt
  · rw [hconj, shift_conj_of_pair hpair' hwt]
    exact hsht

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
