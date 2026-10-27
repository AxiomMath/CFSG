module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

theorem borelQuotient_su_level (hn : 3 ≤ n) (hnq : (n, 2 ^ 1) ≠ (3, 2))
    {ζ : traceZero (unitaryInvolution F 2 1)} (hζ : (ζ : F) ≠ 0) {Y : Type} [Group Y]
    (π : SU (unitaryInvolution F 2 1) n →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n)) :
    BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F 2 1)) π (Nat.card F - 1) := by
  have h0 := borelQuotient_su hF (by omega) ζ hζ
    (MulEquiv.refl (StatedProj (StatedSU n (2 ^ 1) F)))
  have hpow : ∀ z ∈ π.ker, z ^ (Nat.card F - 1) = 1 := by
    intro z hz
    apply h0.ker_pow z
    have hcen := (isQuasisimple_statedSU_of_card hF hn hnq).2
    set ψ := equivStatedSU hF n
    have h1 : ψ z ∈ Subgroup.center ↥(StatedSU n (2 ^ 1) F) := by
      rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv ψ]
      exact ⟨z, hker hz, rfl⟩
    rw [hcen] at h1
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 h1
  exact { ct := h0.ct, extras := h0.extras, pGroup := h0.pGroup, surj := hπ, odd := h0.odd
          torus_pow := h0.torus_pow, ker_central := fun z hz => hker hz, ker_pow := hpow }

include hF in
theorem exists_scalar_eq_mat_of_mem_center (hn : 3 ≤ n) (hnq : (n, 2 ^ 1) ≠ (3, 2))
    {z : SU (unitaryInvolution F 2 1) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 1) n)) :
    ∃ u : F, mat (unitaryInvolution F 2 1) n z = Matrix.scalar (Fin n) u := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  set ψ : SU (unitaryInvolution F 2 1) n ≃* StatedSU n (2 ^ 1) F :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n)) with hψ
  have h1 : ψ z ∈ Subgroup.center ↥(StatedSU n (2 ^ 1) F) := by
    rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv ψ]
    exact ⟨z, hz, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hF hn hnq).2, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := h1
  have hcoe : ((ψ z : StatedSU n (2 ^ 1) F) : GL (Fin n) F) = P * (z : GL (Fin n) F) * P⁻¹ := rfl
  have hz' : (z : GL (Fin n) F) = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P := by
    rw [hu, hcoe]
    group
  refine ⟨(u : F), ?_⟩
  rw [mat_apply, hz', Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    ← (Matrix.scalar_commute (u : F) (fun r => mul_comm _ r) _).eq, Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

include hF in
theorem center_inf_rankOne_last_eq_bot (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) {z : SU (unitaryInvolution F 2 1) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    (hzL : z ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n)
      k) :
    z = 1 := by
  obtain ⟨u, hu⟩ :=
    exists_scalar_eq_mat_of_mem_center hF (by omega) (fun h => by simp at h; omega) hz
  have hblk := isBlkOn_lastIdxOdd hn hk hzL
  set s₀ : Fin n := ⟨0, by omega⟩
  have hk1 : 1 ≤ k.val := by
    have := k.isLt
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
    omega
  have hs₀ : s₀ ∉ Set.range (lastIdxOdd k hn) := by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    fin_cases i <;> simp [lastIdxOdd, s₀, val_lowIdx, midIdx, Fin.val_rev] at this <;> omega
  have h1 := hblk s₀ s₀ (Or.inl hs₀)
  rw [hu, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  apply Subtype.ext
  apply Units.ext
  change mat (unitaryInvolution F 2 1) n z = mat (unitaryInvolution F 2 1) n 1
  rw [hu, map_one, h1, map_one]

section Commutator

variable {ω : F}

@[expose] def rootElt3 (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 1, ω; 0, 1, 1; 0, 0, 1]

@[expose] def rootElt3Inv (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 1, ω ^ 2; 0, 1, 1; 0, 0, 1]

omit [Finite F] in
theorem rootElt3_mul_inv (hs : 1 + ω + ω ^ 2 = 0) :
    rootElt3 ω * rootElt3Inv ω = 1 ∧ rootElt3Inv ω * rootElt3 ω = 1 := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rootElt3, rootElt3Inv, mul_apply, Fin.sum_univ_three] <;>
      grind

omit [Field F] [Finite F] [CharP F 2] in
theorem antidiag_three_eq_matrix {R : Type*} [Field R] :
    (antidiag 3 : Matrix (Fin 3) (Fin 3) R) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

theorem rootElt3_mem_SU (hs : 1 + ω + ω ^ 2 = 0)
    (hσ : unitaryInvolution F 2 1 ω = ω ^ 2) :
    (⟨rootElt3 ω, rootElt3Inv ω, (rootElt3_mul_inv hs).1, (rootElt3_mul_inv hs).2⟩ :
      GL (Fin 3) F) ∈ SU (unitaryInvolution F 2 1) 3 := by
  rw [mem_SU]
  refine ⟨by simp [rootElt3, det_fin_three], ?_⟩
  change conjTr (unitaryInvolution F 2 1) (rootElt3 ω) * antidiag 3 * rootElt3 ω = antidiag 3
  rw [rootElt3, CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.conjTr_fin_three,
    antidiag_three_eq_matrix]
  simp only [map_one, map_zero, hσ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind

omit [Finite F] in
theorem rootElt3_comm_cube_ne_one (hs : 1 + ω + ω ^ 2 = 0) :
    (rootElt3 ω * !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] * rootElt3Inv ω *
      !![ω, 0, 0; 0, 1, 0; 0, 0, ω]) ^ 3 ≠ 1 := by
  have hB : rootElt3 ω * !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] * rootElt3Inv ω *
      !![ω, 0, 0; 0, 1, 0; 0, 0, ω] = !![1, ω, ω ^ 2; 0, 1, ω ^ 2; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootElt3, rootElt3Inv, mul_apply, Fin.sum_univ_three] <;> grind
  rw [hB, pow_three]
  intro h
  have := congrFun (congrFun h 0) 1
  simp [mul_apply, Fin.sum_univ_three] at this
  grind

omit [Field F] [Finite F] [CharP F 2] in
theorem submatrix_mul_diagonal' {R : Type*} [Field R] {r m : ℕ} (e : Fin r → Fin m)
    (N : Matrix (Fin m) (Fin m) R) (t : Fin m → R) :
    (N * diagonal t).submatrix e e = N.submatrix e e * diagonal (t ∘ e) := by
  ext i j
  simp [mul_diagonal]

omit [Field F] [Finite F] [CharP F 2] in
theorem submatrix_diagonal_mul' {R : Type*} [Field R] {r m : ℕ} (e : Fin r → Fin m)
    (N : Matrix (Fin m) (Fin m) R) (t : Fin m → R) :
    (diagonal t * N).submatrix e e = diagonal (t ∘ e) * N.submatrix e e := by
  ext i j
  simp [diagonal_mul]

end Commutator

include hF in
theorem exists_torus_rankOne_commutator (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) :
    ∃ d ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i,
      ∃ q ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n) k,
        (q * d * q⁻¹ * d⁻¹) ^ 3 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_primitive_cube_root_of_card_four hF
  have hσω : unitaryInvolution F 2 1 ω = ω ^ 2 := by rw [unitaryInvolution_apply, pow_one]
  have hs : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hω1
    · exact h
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', hω3]
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
  have hkv : k.val + 1 = n / 2 := by have := k.isLt; omega
  set k' : Fin (n / 2) := ⟨k.val - 1, by omega⟩ with hk'
  have h' : k'.val + 1 < n / 2 := by simp only [hk']; omega
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF n (by omega) ζ hζ
  set d := shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ h') (lowIdx_ne_rev k' k')
    (lowIdx_ne_rev _ _) ((Units.mk0 ω hω0 : Fˣ) : F) with hd
  have hdT : d ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i :=
    Subgroup.mem_iSup_of_mem k' (shortTorus_mem_levelTorus hσ h' _)
  set t := shortTorusFun (unitaryInvolution F 2 1) (lowIdx k') (lowIdx ⟨k'.val + 1, h'⟩) ω
    with ht
  have hdmat : mat (unitaryInvolution F 2 1) n d = diagonal t :=
    coe_shortTorus _ hσ _ _ _ (lowIdx_ne_rev _ _) hω0
  have hD : diagonal (t ∘ lastIdxOdd k hn) = !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] := by
    have ht0 : t (lowIdx k) = ω ^ 2 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, hk']; omega),
        ite_eq_left (by simp [Fin.ext_iff, val_lowIdx, hk']; omega), hωinv]
    have ht1 : t (midIdx n hn) = 1 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, Fin.val_rev, hk']; omega)]
    have ht2 : t (Fin.rev (lowIdx k)) = ω ^ 2 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_left (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega), hσω]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lastIdxOdd, ht0, ht1, ht2]
  set Q : SU (unitaryInvolution F 2 1) 3 := ⟨_, rootElt3_mem_SU hs hσω⟩ with hQ
  set eL := rankOneLastOddEquiv hF hn hk with heL
  set ql := eL.symm Q with hql
  refine ⟨d, hdT, (ql : SU _ n), ql.2, fun h3 => ?_⟩
  have hdN := ParabPrime.iSup_torus_le_normalizer_rankOne (D := rootDatum hF n) hct k hdT
  have hwL : (ql : SU (unitaryInvolution F 2 1) n) * d * (ql : SU (unitaryInvolution F 2 1) n)⁻¹ *
      d⁻¹ ∈ rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k := by
    have h1 : d * (ql : SU (unitaryInvolution F 2 1) n)⁻¹ * d⁻¹ ∈
        rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k :=
      (Subgroup.mem_set_normalizer_iff.1 hdN _).1 (inv_mem ql.2)
    have := mul_mem ql.2 h1
    rwa [← mul_assoc, ← mul_assoc] at this
  set wl : rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k := ⟨_, hwL⟩ with hwl
  have hw3 : wl ^ 3 = 1 := Subtype.ext (by simpa using h3)
  set e := lastIdxOdd k hn with he
  have hblock : ∀ g : rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k,
      mat (unitaryInvolution F 2 1) 3 (eL g) = (mat (unitaryInvolution F 2 1) n g).submatrix e e :=
    fun g => by rw [heL, mat_rankOneLastOddEquiv, toBlock3_eq_submatrix]; rfl
  have hQm : (mat (unitaryInvolution F 2 1) n ql).submatrix e e = rootElt3 ω := by
    rw [← hblock, hql, MulEquiv.apply_symm_apply]
    rfl
  have hQm' : (mat (unitaryInvolution F 2 1) n (ql⁻¹ : rankOne _ k)).submatrix e e =
      rootElt3Inv ω := by
    rw [← hblock, map_inv, hql, MulEquiv.apply_symm_apply]
    rfl
  have hqblk : IsBlkOn e (mat (unitaryInvolution F 2 1) n ql) := isBlkOn_lastIdxOdd hn hk ql.2
  have hwd : (wl : SU (unitaryInvolution F 2 1) n) * d =
      ql * d * ((ql⁻¹ : rankOne _ k) : SU (unitaryInvolution F 2 1) n) := by
    simp only [hwl, Subgroup.coe_inv]
    group
  have hB : (mat (unitaryInvolution F 2 1) n wl).submatrix e e *
      !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] =
        rootElt3 ω * !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] * rootElt3Inv ω := by
    have h1 := congrArg (fun g => (mat (unitaryInvolution F 2 1) n g).submatrix e e) hwd
    simp only [map_mul] at h1
    rw [hdmat, submatrix_mul_diagonal', hD, Matrix.mul_assoc,
      submatrix_mul_of_isBlkOn (lastIdxOdd_injective hk hn) hqblk, submatrix_diagonal_mul', hD,
      hQm, hQm'] at h1
    rw [h1, Matrix.mul_assoc]
  have hD' : !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] * !![ω, 0, 0; 0, 1, 0; 0, 0, ω] =
      (1 : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind
  have hBe : (mat (unitaryInvolution F 2 1) n wl).submatrix e e =
      rootElt3 ω * !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] * rootElt3Inv ω *
        !![ω, 0, 0; 0, 1, 0; 0, 0, ω] := by
    rw [← hB, Matrix.mul_assoc, hD', Matrix.mul_one]
  apply rootElt3_comm_cube_ne_one hs
  rw [← hBe, ← hblock, ← map_pow, ← map_pow, hw3, map_one, map_one]

end CFSG.AGLEmbedding
