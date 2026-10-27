module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Phan.PhanDn.WeakPhan
public import CFSG.LocalAnalysis.StandardType.PhanEReduction
public import CFSG.RankThree.PartOne.CTP.Phan5Cent
public import CFSG.LieType.Universal.Unitary.Hermitian

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.Timmesfeld
open QuadraticMap
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]

theorem SUid_two_entries (g : SUid (unitaryInvolution K 2 f) 2) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
        unitaryInvolution K 2 f (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) ∧
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
        unitaryInvolution K 2 f (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  set M := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = 1 := g.2.1
  have hconj : conjTr (unitaryInvolution K 2 f) M * M = 1 := g.2.2
  have hadj : M * M.adjugate = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  have h : M.adjugate = conjTr (unitaryInvolution K 2 f) M :=
    Matrix.right_inv_eq_left_inv hadj hconj
  constructor
  · have := congrFun (congrFun h 1) 0
    simpa [Matrix.adjugate_fin_two, conjTr_apply, CharTwo.neg_eq] using this
  · have := congrFun (congrFun h 0) 0
    simpa [Matrix.adjugate_fin_two, conjTr_apply] using this

theorem blockEmb2_last_smul_zero {m : ℕ} (hm : 3 ≤ m) (A : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ A • v) ⟨m - 1, by omega⟩ =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * v ⟨m - 1, by omega⟩ +
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 * v (Fin.last m) := by
  have hblk : (m - 1) + 2 ≤ m + 1 := by omega
  rw [smul_def, coe_coe_blockEmb2]
  rw [show (⟨m - 1, by omega⟩ : Fin (m + 1)) = blockIdx (m - 1) hblk 0 from
    Fin.ext (by simp only [blockIdx_val]; omega)]
  rw [blockMat_mulVec_blockIdx]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (blockIdx (m - 1) hblk 0 : Fin (m + 1)) = ⟨m - 1, by omega⟩ from
    Fin.ext (by simp),
    show (blockIdx (m - 1) hblk 1 : Fin (m + 1)) = Fin.last m from
    Fin.ext (by simp only [blockIdx_val, Fin.val_last]; omega)]

theorem blockEmb2_last_smul_one {m : ℕ} (hm : 3 ≤ m) (A : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ A • v) (Fin.last m) =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * v ⟨m - 1, by omega⟩ +
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 * v (Fin.last m) := by
  have hblk : (m - 1) + 2 ≤ m + 1 := by omega
  rw [smul_def, coe_coe_blockEmb2]
  rw [show (Fin.last m : Fin (m + 1)) = blockIdx (m - 1) hblk 1 from
    Fin.ext (by simp only [blockIdx_val, Fin.val_last]; omega)]
  rw [blockMat_mulVec_blockIdx]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (blockIdx (m - 1) hblk 0 : Fin (m + 1)) = ⟨m - 1, by omega⟩ from
    Fin.ext (by simp),
    show (blockIdx (m - 1) hblk 1 : Fin (m + 1)) = Fin.last m from
    Fin.ext (by simp only [blockIdx_val, Fin.val_last]; omega)]

theorem blockEmb2_last_smul_of_ne {m : ℕ} (hm : 3 ≤ m) (A : Su K 2 f 2)
    (v : Fin (m + 1) → K) {i : Fin (m + 1)}
    (hi : i.val ≠ m - 1) (hi' : i.val ≠ m) :
    (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ A • v) i = v i := by
  rw [smul_def, coe_coe_blockEmb2]
  refine blockMat_mulVec_of_not_mem _ _ ?_
  rintro ⟨h1, h2⟩
  have hm2 : m - 1 + 2 = m + 1 := by omega
  rw [hm2] at h2
  have hlt := i.isLt
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · exact hi h.symm
  · refine absurd ?_ hi'
    refine le_antisymm (Nat.lt_succ_iff.mp hlt) ?_
    have h' := Nat.succ_le_of_lt h
    rw [Nat.succ_eq_add_one, show m - 1 + 1 = m from by omega] at h'
    exact h'

variable (E : QuadExt F K (unitaryInvolution K 2 f))

theorem blockEmb2_last_smul_comm {m : ℕ} (hm : 3 ≤ m) (A B : Su K 2 f 2)
    (x : Fin (m + 1) → K) :
    blockEmb2 K 2 f m ⟨m - 1, by omega⟩ A •
        (tauAt E (Fin.last m) (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ B •
          (tauAt E (Fin.last m) x))) =
      tauAt E (Fin.last m) (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ B •
        (tauAt E (Fin.last m) (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ A • x))) := by
  obtain ⟨hA10, hA11⟩ := SUid_two_entries A
  obtain ⟨hB10, hB11⟩ := SUid_two_entries B
  have hA10' : unitaryInvolution K 2 f
      (((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have h := congrArg (unitaryInvolution K 2 f) hA10
    rwa [E.isUnitary.invol] at h
  have hA11' : unitaryInvolution K 2 f
      (((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have h := congrArg (unitaryInvolution K 2 f) hA11
    rwa [E.isUnitary.invol] at h
  have hB10' : unitaryInvolution K 2 f
      (((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) =
      ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have h := congrArg (unitaryInvolution K 2 f) hB10
    rwa [E.isUnitary.invol] at h
  have hB11' : unitaryInvolution K 2 f
      (((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) =
      ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have h := congrArg (unitaryInvolution K 2 f) hB11
    rwa [E.isUnitary.invol] at h
  have hp : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    rw [show (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) from rfl]
    exact Fin.castSucc_ne_last _
  funext i
  by_cases hip : i = ⟨m - 1, by omega⟩
  · subst hip
    simp only [blockEmb2_last_smul_zero hm, blockEmb2_last_smul_one hm, tauAt_apply, hp,
      if_pos, ite_false]
    simp only [map_add, map_mul, E.isUnitary.invol, hA10, hA11, hB10, hB11]
    ring
  · by_cases hiq : i = Fin.last m
    · subst hiq
      simp only [blockEmb2_last_smul_zero hm, blockEmb2_last_smul_one hm, tauAt_apply, hp,
        if_pos, ite_false]
      simp only [map_add, map_mul, E.isUnitary.invol, hA10, hA11, hB10, hB11]
      ring
    · have hipv : i.val ≠ m - 1 := fun h => hip (Fin.ext (by simpa using h))
      have hiqv : i.val ≠ m := fun h => hiq (Fin.ext (by simpa [Fin.val_last] using h))
      rw [blockEmb2_last_smul_of_ne hm A _ hipv hiqv,
        tauAt_apply, if_neg hiq,
        blockEmb2_last_smul_of_ne hm B _ hipv hiqv,
        tauAt_apply, if_neg hiq,
        tauAt_apply, if_neg hiq,
        blockEmb2_last_smul_of_ne hm B _ hipv hiqv,
        tauAt_apply, if_neg hiq,
        blockEmb2_last_smul_of_ne hm A _ hipv hiqv]

@[expose] noncomputable def stdChainIota (m : ℕ) (k : Fin m) :
    Su K 2 f 2 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)).comp (blockEmb2 K 2 f m k)

@[expose] noncomputable def stdTau (m : ℕ) : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) :=
  tauAt E (Fin.last m)

@[expose] noncomputable def stdConj (m : ℕ) :
    MulAut ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  MulAut.conj (stdTau E m)

@[expose] noncomputable def stdChainTheta (m : ℕ) (k : Fin m) (h : k.val + 1 < m) :
    Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)).comp (blockEmb3 K 2 f m k h)

@[expose] noncomputable def stdForkIota (m : ℕ) (hm : 3 ≤ m) :
    Su K 2 f 2 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  (stdConj E m).toMonoidHom.comp (stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩)

@[expose] noncomputable def stdForkTheta (m : ℕ) (hm : 3 ≤ m) :
    Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  (stdConj E m).toMonoidHom.comp
    (stdChainTheta (F := F) (f := f) m ⟨m - 2, by omega⟩ (by
      show m - 2 + 1 < m
      omega))

@[expose] noncomputable def stdThetaAt (m : ℕ) (i : Fin (m + 1)) (j' : Fin m) :
    Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  if h : i.val + 1 = j'.val then
    (let hi : i.val < m := by omega
     let hi' : i.val + 1 < m := by omega
     stdChainTheta (F := F) (f := f) m ⟨i.val, hi⟩ hi')
  else 1

@[expose] noncomputable def stdIota (m : ℕ) (hm : 3 ≤ m) (k : Fin (m + 1)) :
    Su K 2 f 2 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  Fin.lastCases (motive := fun _ => Su K 2 f 2 →* ((Fin (m + 1) → K) ≃ₗ[F] _))
    (stdForkIota E m hm) (fun k' => stdChainIota (F := F) (f := f) m k') k

@[expose] noncomputable def stdTheta (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  Fin.lastCases (motive := fun _ => Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] _))
    (stdForkTheta E m hm) (fun j' => stdThetaAt (F := F) (f := f) m i j') j

@[simp] theorem stdIota_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m) :
    stdIota E m hm (Fin.castSucc k) = stdChainIota (F := F) (f := f) m k := by
  rw [stdIota, Fin.lastCases_castSucc]

@[simp] theorem stdIota_last (m : ℕ) (hm : 3 ≤ m) :
    stdIota E m hm (Fin.last m) = stdForkIota E m hm := by
  rw [stdIota, Fin.lastCases_last]

@[simp] theorem stdTheta_castSucc (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) (j' : Fin m) :
    stdTheta E m hm i (Fin.castSucc j') = stdThetaAt (F := F) (f := f) m i j' := by
  rw [stdTheta, Fin.lastCases_castSucc]

@[simp] theorem stdTheta_last (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    stdTheta E m hm i (Fin.last m) = stdForkTheta E m hm := by
  rw [stdTheta, Fin.lastCases_last]

theorem chainIota_commute_tau (m : ℕ) (k : Fin m) (hk : k.val + 1 < m) (a : Su K 2 f 2) :
    Commute (stdChainIota m k a) (stdTau E m) := by
  have hblk : k.val + 2 ≤ m + 1 := by omega
  have hl : ¬ (k.val ≤ (Fin.last m).val ∧ (Fin.last m).val < k.val + 2) := by
    simp only [Fin.val_last]
    omega
  have hfix : blockEmb2 K 2 f m k a • (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K) =
      Pi.single (Fin.last m) 1 := by
    change blockEmb K 2 f (m + 1) 2 k.val hblk a • _ = _
    exact blockEmb_smul_single_of_not_mem hblk a hl
  have hpres : ∀ x : Fin (m + 1) → K, x (Fin.last m) = 0 →
      (blockEmb2 K 2 f m k a • x) (Fin.last m) = 0 := by
    intro x hx
    rw [smul_def, coe_coe_blockEmb2, blockMat_mulVec_of_not_mem _ _ hl]
    exact hx
  exact suEndN_commute_tauAt E (blockEmb2 K 2 f m k a) (Fin.last m) hfix hpres

theorem stdConj_chainIota (m : ℕ) (k : Fin m) (hk : k.val + 1 < m) (a : Su K 2 f 2) :
    (stdConj E m).toMonoidHom (stdChainIota m k a) = stdChainIota m k a := by
  have hc := chainIota_commute_tau E m k hk a
  rw [stdConj]
  change MulAut.conj (stdTau E m) (stdChainIota m k a) = stdChainIota m k a
  rw [MulAut.conj_apply, ← hc, mul_assoc, mul_inv_cancel, mul_one]

theorem stdConj_comp_chainIota (m : ℕ) (k : Fin m) (hk : k.val + 1 < m) :
    (stdConj E m).toMonoidHom.comp (stdChainIota (F := F) (f := f) m k) =
      stdChainIota (F := F) (f := f) m k := by
  refine MonoidHom.ext fun a => ?_
  exact stdConj_chainIota E m k hk a

theorem chainIota_mul_comm (m : ℕ) (k l : Fin m) (hkl : k.val + 1 < l.val)
    (a b : Su K 2 f 2) :
    stdChainIota (F := F) (f := f) m k a * stdChainIota (F := F) (f := f) m l b =
      stdChainIota (F := F) (f := f) m l b * stdChainIota (F := F) (f := f) m k a := by
  unfold stdChainIota
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, blockEmb2_comm m k l hkl, map_mul]

theorem chainIota_comm_fork (m : ℕ) (hm : 3 ≤ m) (k : Fin m) (hk : k.val + 1 < m - 1)
    (a b : Su K 2 f 2) :
    stdChainIota (F := F) (f := f) m k a * stdForkIota E m hm b =
      stdForkIota E m hm b * stdChainIota (F := F) (f := f) m k a := by
  have hcomm : stdChainIota (F := F) (f := f) m k a *
      stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ b =
      stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ b *
        stdChainIota (F := F) (f := f) m k a :=
    chainIota_mul_comm m k ⟨m - 1, by omega⟩ hk a b
  have hfix : (stdConj E m).toMonoidHom (stdChainIota m k a) = stdChainIota m k a :=
    stdConj_chainIota E m k (by omega) a
  rw [stdForkIota]
  calc stdChainIota m k a * (stdConj E m).toMonoidHom (stdChainIota m ⟨m - 1, by omega⟩ b)
      = (stdConj E m).toMonoidHom (stdChainIota m k a) *
          (stdConj E m).toMonoidHom (stdChainIota m ⟨m - 1, by omega⟩ b) := by rw [hfix]
    _ = (stdConj E m).toMonoidHom
          (stdChainIota m k a * stdChainIota m ⟨m - 1, by omega⟩ b) :=
          (map_mul (stdConj E m).toMonoidHom _ _).symm
    _ = (stdConj E m).toMonoidHom
          (stdChainIota m ⟨m - 1, by omega⟩ b * stdChainIota m k a) := by rw [hcomm]
    _ = (stdConj E m).toMonoidHom (stdChainIota m ⟨m - 1, by omega⟩ b) *
          (stdConj E m).toMonoidHom (stdChainIota m k a) :=
          map_mul (stdConj E m).toMonoidHom _ _
    _ = (stdConj E m).toMonoidHom (stdChainIota m ⟨m - 1, by omega⟩ b) *
          stdChainIota m k a := by rw [hfix]

theorem suEndN_blockEmb2_last_comm (m : ℕ) (hm : 3 ≤ m) (a b : Su K 2 f 2) :
    Commute
      (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ a))
      (MulAut.conj (stdTau E m)
        (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
          (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ b))) := by
  rw [Commute, MulAut.conj_apply, stdTau]
  rw [inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))]
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, suEndN_apply]
  exact blockEmb2_last_smul_comm (m := m) E hm a b x

theorem stdChainTheta_comp_two (m : ℕ) (k : Fin m) (h : k.val + 1 < m) :
    (stdChainTheta (F := F) (f := f) m k h).comp
        (embSUid (unitaryInvolution K 2 f) 2) =
      stdChainIota (F := F) (f := f) m k := by
  unfold stdChainTheta stdChainIota
  rw [MonoidHom.comp_assoc, blockEmb3_comp_embSUid_two]

theorem stdChainTheta_comp_zero (m : ℕ) (k : Fin m) (h : k.val + 1 < m) :
    (stdChainTheta (F := F) (f := f) m k h).comp
        (embSUid (unitaryInvolution K 2 f) 0) =
      stdChainIota (F := F) (f := f) m ⟨k.val + 1, h⟩ := by
  unfold stdChainTheta stdChainIota
  simp only [MonoidHom.comp_assoc]
  rw [blockEmb3_comp_embSUid_zero]

theorem stdThetaAt_comp_two_of {m : ℕ} (i : Fin (m + 1)) (j' : Fin m)
    (h : i.val + 1 = j'.val) (hi : i.val < m) (hi' : i.val + 1 < m) :
    (stdThetaAt (F := F) (f := f) m i j').comp (embSUid (unitaryInvolution K 2 f) 2) =
      stdChainIota (F := F) (f := f) m ⟨i.val, hi⟩ := by
  unfold stdThetaAt
  rw [dif_pos h]
  exact stdChainTheta_comp_two m ⟨i.val, hi⟩ hi'

theorem stdThetaAt_comp_zero_of {m : ℕ} (i : Fin (m + 1)) (j' : Fin m)
    (h : i.val + 1 = j'.val) (hi : i.val < m) (hi' : i.val + 1 < m) :
    (stdThetaAt (F := F) (f := f) m i j').comp (embSUid (unitaryInvolution K 2 f) 0) =
      stdChainIota (F := F) (f := f) m ⟨i.val + 1, hi'⟩ := by
  unfold stdThetaAt
  rw [dif_pos h]
  exact stdChainTheta_comp_zero m ⟨i.val, hi⟩ hi'

theorem stdForkTheta_comp_two (m : ℕ) (hm : 3 ≤ m) :
    (stdForkTheta E m hm).comp (embSUid (unitaryInvolution K 2 f) 2) =
      stdChainIota (F := F) (f := f) m ⟨m - 2, by omega⟩ := by
  unfold stdForkTheta stdChainTheta stdChainIota
  simp only [MonoidHom.comp_assoc]
  rw [blockEmb3_comp_embSUid_two]
  exact stdConj_comp_chainIota E m ⟨m - 2, by omega⟩ (by
    show m - 2 + 1 < m
    omega)

theorem stdForkTheta_comp_zero (m : ℕ) (hm : 3 ≤ m) :
    (stdForkTheta E m hm).comp (embSUid (unitaryInvolution K 2 f) 0) =
      stdForkIota E m hm := by
  have hidx : (⟨(⟨m - 2, by omega⟩ : Fin m).val + 1, by
      show m - 2 + 1 < m
      omega⟩ : Fin m) = (⟨m - 1, by omega⟩ : Fin m) := by
    apply Fin.ext
    show (⟨m - 2, by omega⟩ : Fin m).val + 1 = m - 1
    have hval : (⟨m - 2, by omega⟩ : Fin m).val = m - 2 := rfl
    omega
  unfold stdForkTheta stdForkIota stdChainTheta stdChainIota
  simp only [MonoidHom.comp_assoc]
  rw [blockEmb3_comp_embSUid_zero, hidx]

private theorem edgeD_succ_iff_of_three_le {m : ℕ} (hm : 3 ≤ m) {i j : Fin (m + 1)} :
    edgeD (m + 1) i j ↔
      (i.val + 1 = j.val ∧ j.val + 1 < m + 1) ∨ (i.val = m - 2 ∧ j.val = m) := by
  rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
  have h1 : (m + 1) - 3 = m - 2 := by omega
  have h2 : (m + 1) - 1 = m := by omega
  rw [h1, h2]

@[expose] noncomputable def stdFamilyV (m : ℕ) (hm : 3 ≤ m) :
    PhanFamilyE K 2 f (CFSG.StandardType.ggCoxeterMatrixD (m + 1))
      ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) where
  ι := stdIota E m hm
  θ := stdTheta E m hm
  left i j hij hM := by
    rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
    ·
      have hE : edgeD (m + 1) i (Fin.castSucc j') := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.castSucc j')).1 hM
          with h | h
        · exact h
        · rw [edgeD_succ_iff_of_three_le hm] at h
          have hlt : i.val < j'.val := hij
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Fin.val_castSucc] at h1 h2
            omega
          · simp only [Fin.val_castSucc] at h1 h2
            omega
      rw [edgeD_succ_iff_of_three_le hm] at hE
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      ·
        have hchain : i.val + 1 = j'.val := h1
        have hilt : i.val < m := by omega
        have hi' : i.val + 1 < m := by omega
        have hi : i = Fin.castSucc ⟨i.val, hilt⟩ := Fin.ext rfl
        rw [hi, stdTheta_castSucc, stdIota_castSucc,
          stdThetaAt_comp_two_of (m := m) (Fin.castSucc ⟨i.val, hilt⟩) j' hchain hilt hi']
        exact congrArg (stdChainIota (F := F) (f := f) m) (Fin.ext rfl)
      ·
        simp only [Fin.val_castSucc] at h2
        omega
    ·
      have hE : edgeD (m + 1) i (Fin.last m) := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.last m)).1 hM
          with h | h
        · exact h
        · rw [edgeD_succ_iff_of_three_le hm] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Fin.val_last] at h1 h2
            omega
          · simp only [Fin.val_last] at h1 h2
            omega
      rw [edgeD_succ_iff_of_three_le hm] at hE
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      ·
        simp only [Fin.val_last] at h2
        omega
      ·
        have hi : i = ⟨m - 2, by omega⟩ := by
          ext
          show i.val = m - 2
          omega
        have hic : (⟨m - 2, by omega⟩ : Fin (m + 1)) =
            Fin.castSucc (⟨m - 2, by omega⟩ : Fin m) := rfl
        rw [hi, hic, stdTheta_last, stdIota_castSucc, stdForkTheta_comp_two]
  right i j hij hM := by
    rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
    ·
      have hE : edgeD (m + 1) i (Fin.castSucc j') := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.castSucc j')).1 hM
          with h | h
        · exact h
        · rw [edgeD_succ_iff_of_three_le hm] at h
          have hlt : i.val < j'.val := hij
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Fin.val_castSucc] at h1 h2
            omega
          · simp only [Fin.val_castSucc] at h1 h2
            omega
      rw [edgeD_succ_iff_of_three_le hm] at hE
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      ·
        have hchain : i.val + 1 = j'.val := h1
        have hilt : i.val < m := by omega
        have hi' : i.val + 1 < m := by omega
        have hi : i = Fin.castSucc ⟨i.val, hilt⟩ := Fin.ext rfl
        rw [hi, stdTheta_castSucc, stdIota_castSucc,
          stdThetaAt_comp_zero_of (m := m) (Fin.castSucc ⟨i.val, hilt⟩) j' hchain hilt hi']
        congr 1
        exact Fin.ext (by simp only [Fin.val_castSucc]; omega)
      ·
        simp only [Fin.val_castSucc] at h2
        omega
    ·
      have hE : edgeD (m + 1) i (Fin.last m) := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.last m)).1 hM
          with h | h
        · exact h
        · rw [edgeD_succ_iff_of_three_le hm] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Fin.val_last] at h1 h2
            omega
          · simp only [Fin.val_last] at h1 h2
            omega
      rw [edgeD_succ_iff_of_three_le hm] at hE
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      ·
        simp only [Fin.val_last] at h2
        omega
      ·
        have hi : i = ⟨m - 2, by omega⟩ := by
          ext
          show i.val = m - 2
          omega
        have hic : (⟨m - 2, by omega⟩ : Fin (m + 1)) =
            Fin.castSucc (⟨m - 2, by omega⟩ : Fin m) := rfl
        rw [hi, hic, stdTheta_last, stdIota_last, stdForkTheta_comp_zero]
  comm i j hM a b := by
    have h2 := (ggCoxeterMatrixD_eq_two_iff (by omega : 4 ≤ m + 1) i j).1 hM
    rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
      ·
        obtain ⟨hne, h1, h2'⟩ := h2
        have hne' : i' ≠ j' := fun h => hne (by rw [h])
        have e1 : i'.val + 1 ≠ j'.val := by
          intro h
          exact h1 (by
            rw [edgeD_succ_iff_of_three_le hm]
            exact Or.inl ⟨by simpa using h, by simp only [Fin.val_castSucc]; omega⟩)
        have e2 : j'.val + 1 ≠ i'.val := by
          intro h
          exact h2' (by
            rw [edgeD_succ_iff_of_three_le hm]
            exact Or.inl ⟨by simpa using h, by simp only [Fin.val_castSucc]; omega⟩)
        have hlt : i'.val + 1 < j'.val ∨ j'.val + 1 < i'.val := by
          have := i'.isLt
          have := j'.isLt
          omega
        rcases hlt with h | h
        · rw [stdIota_castSucc, stdIota_castSucc]
          exact chainIota_mul_comm m i' j' h a b
        · rw [stdIota_castSucc, stdIota_castSucc]
          exact (chainIota_mul_comm m j' i' h b a).symm
      ·
        obtain ⟨-, h1, -⟩ := h2
        have e1 : i'.val ≠ m - 2 := by
          intro h
          exact h1 (by
            rw [edgeD_succ_iff_of_three_le hm]
            exact Or.inr ⟨by simpa using h, by simp only [Fin.val_last]⟩)
        have := i'.isLt
        by_cases hlast : i'.val = m - 1
        · have hieq : i' = ⟨m - 1, by omega⟩ := Fin.ext (by simpa using hlast)
          rw [hieq]
          rw [stdIota_castSucc, stdIota_last]
          exact suEndN_blockEmb2_last_comm E m hm a b
        · have hk : i'.val + 1 < m - 1 := by omega
          rw [stdIota_castSucc, stdIota_last]
          exact chainIota_comm_fork E m hm i' hk a b
    · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
      ·
        obtain ⟨-, -, h2'⟩ := h2
        have e2 : j'.val ≠ m - 2 := by
          intro h
          exact h2' (by
            rw [edgeD_succ_iff_of_three_le hm]
            exact Or.inr ⟨by simpa using h, by simp only [Fin.val_last]⟩)
        have := j'.isLt
        by_cases hlast : j'.val = m - 1
        · have hjeq : j' = ⟨m - 1, by omega⟩ := Fin.ext (by simpa using hlast)
          rw [hjeq]
          rw [stdIota_last, stdIota_castSucc]
          exact (suEndN_blockEmb2_last_comm E m hm b a).symm
        · have hk : j'.val + 1 < m - 1 := by omega
          rw [stdIota_last, stdIota_castSucc]
          exact (chainIota_comm_fork E m hm j' hk b a).symm
      ·
        obtain ⟨hne, -, -⟩ := h2
        exact absurd rfl hne

@[simp] theorem stdFamilyV_ι (m : ℕ) (hm : 3 ≤ m) :
    (stdFamilyV E m hm).ι = stdIota E m hm := rfl

@[simp] theorem stdFamilyV_θ (m : ℕ) (hm : 3 ≤ m) :
    (stdFamilyV E m hm).θ = stdTheta E m hm := rfl

@[simp] theorem stdFamilyV_ι_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m) :
    (stdFamilyV E m hm).ι (Fin.castSucc k) = stdChainIota (F := F) (f := f) m k := by
  rw [stdFamilyV_ι, stdIota_castSucc]

@[simp] theorem stdFamilyV_ι_last (m : ℕ) (hm : 3 ≤ m) :
    (stdFamilyV E m hm).ι (Fin.last m) = stdForkIota E m hm := by
  rw [stdFamilyV_ι, stdIota_last]


theorem stdFamilyV_ι_mem_orthogonalGroup (m : ℕ) (hm : 3 ≤ m) (k : Fin (m + 1))
    (a : Su K 2 f 2) :
    (stdFamilyV E m hm).ι k a ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) k with ⟨k', rfl⟩ | rfl
  · rw [stdFamilyV_ι, stdIota_castSucc]
    unfold stdChainIota
    exact suEndN_mem_orthogonalGroup E (m + 1) (blockEmb2 K 2 f m k' a)
  · rw [stdFamilyV_ι, stdIota_last]
    unfold stdForkIota stdChainIota stdConj
    change MulAut.conj (stdTau E m)
        (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
          (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ a)) ∈ _
    rw [MulAut.conj_apply]
    unfold stdTau
    exact tauAt_conj_mem_orthogonalGroup E (Fin.last m)
      (suEndN_mem_orthogonalGroup E (m + 1) (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ a))

theorem stdFamilyV_θ_mem_orthogonalGroup (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1))
    (a : Su K 2 f 3) :
    (stdFamilyV E m hm).θ i j a ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · rw [stdFamilyV_θ, stdTheta_castSucc]
    unfold stdThetaAt
    split_ifs with h
    · unfold stdChainTheta
      exact suEndN_mem_orthogonalGroup E (m + 1)
        (blockEmb3 K 2 f m ⟨i.val, by omega⟩ (by
          show i.val + 1 < m
          omega) a)
    · exact Subgroup.one_mem _
  · rw [stdFamilyV_θ, stdTheta_last]
    unfold stdForkTheta stdChainTheta stdConj
    change MulAut.conj (stdTau E m)
        (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
          (blockEmb3 K 2 f m ⟨m - 2, by omega⟩ (by
            show m - 2 + 1 < m
            omega) a)) ∈ _
    rw [MulAut.conj_apply]
    unfold stdTau
    exact tauAt_conj_mem_orthogonalGroup E (Fin.last m)
      (suEndN_mem_orthogonalGroup E (m + 1)
        (blockEmb3 K 2 f m ⟨m - 2, by omega⟩ (by
            show m - 2 + 1 < m
            omega) a))

theorem two_le_of_four_le_pow (hq : 4 ≤ 2 ^ f) : 2 ≤ f := by
  rcases Nat.lt_or_ge f 2 with h | h
  · interval_cases f <;> norm_num at hq
  · exact h

theorem pow_ne_two_of_four_le (hq : 4 ≤ 2 ^ f) : 2 ^ f ≠ 2 := by
  intro h
  rw [h] at hq
  norm_num at hq

theorem range_le_commutator_of_su2 (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (F' : Su K 2 f 2 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
    (hF : F'.range ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))) :
    F'.range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  have hperf : Group.IsPerfect (Su K 2 f 2) :=
    CFSG.RankThree.PartOne.CTP.isPerfect_su_two hK (two_le_of_four_le_pow hq)
  have hEq : ⁅F'.range, F'.range⁆ = F'.range :=
    Subgroup.isPerfect_iff.mp
      (@Group.IsPerfect.range (Su K 2 f 2)
        ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) _ _ F' hperf)
  rw [← hEq]
  exact Subgroup.commutator_mono hF hF

theorem range_le_commutator_of_su3 (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (F' : Su K 2 f 3 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
    (h12 : (F'.comp (embSUid (unitaryInvolution K 2 f) 2)).range ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆)
    (h23 : (F'.comp (embSUid (unitaryInvolution K 2 f) 0)).range ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆) :
    F'.range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  have htop : B12 K 2 f ⊔ B23 K 2 f = ⊤ :=
    B12_sup_B23_eq_top (K := K) (p := 2) (f := f) hK (pow_ne_two_of_four_le hq)
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [B12, ← MonoidHom.range_comp]
    exact h12
  · rw [B23, ← MonoidHom.range_comp]
    exact h23

theorem chainIota_range_le_commutator (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin m) :
    (stdChainIota (F := F) (f := f) m k).range ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  refine range_le_commutator_of_su2 E m hK hq _ ?_
  rintro x ⟨y, rfl⟩
  unfold stdChainIota
  exact suEndN_mem_orthogonalGroup E (m + 1) (blockEmb2 K 2 f m k y)

theorem stdFamilyV_ι_range_le_commutator (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (k : Fin (m + 1)) :
    ((stdFamilyV E m hm).ι k).range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  refine range_le_commutator_of_su2 E m hK hq _ ?_
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact stdFamilyV_ι_mem_orthogonalGroup E m hm k y

theorem stdFamilyV_ι_mem_commutator (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin (m + 1)) (a : Su K 2 f 2) :
    (stdFamilyV E m hm).ι k a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ :=
  stdFamilyV_ι_range_le_commutator E m hm hK hq k ⟨a, rfl⟩

theorem stdChainTheta_range_le_commutator (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin m) (h : k.val + 1 < m) :
    (stdChainTheta (F := F) (f := f) m k h).range ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  refine range_le_commutator_of_su3 E m hK hq _ ?_ ?_
  · rw [stdChainTheta_comp_two]
    exact chainIota_range_le_commutator E m hK hq k
  · rw [stdChainTheta_comp_zero]
    exact chainIota_range_le_commutator E m hK hq ⟨k.val + 1, h⟩

theorem stdChainTheta_mem_commutator (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin m) (h : k.val + 1 < m) (a : Su K 2 f 3) :
    stdChainTheta (F := F) (f := f) m k h a ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ :=
  stdChainTheta_range_le_commutator E m hK hq k h ⟨a, rfl⟩

theorem stdThetaAt_mem_commutator (m : ℕ) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (i : Fin (m + 1)) (j' : Fin m) (a : Su K 2 f 3) :
    stdThetaAt (F := F) (f := f) m i j' a ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  unfold stdThetaAt
  split_ifs with h
  · have hi : i.val < m := by omega
    have hi' : i.val + 1 < m := by omega
    exact stdChainTheta_mem_commutator E m hK hq ⟨i.val, hi⟩ hi' a
  · exact Subgroup.one_mem _

theorem stdForkTheta_mem_commutator (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (a : Su K 2 f 3) :
    stdForkTheta E m hm a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  refine range_le_commutator_of_su3 E m hK hq _ ?_ ?_ ⟨a, rfl⟩
  · rw [stdForkTheta_comp_two]
    exact chainIota_range_le_commutator E m hK hq ⟨m - 2, by omega⟩
  · rw [stdForkTheta_comp_zero, ← stdIota_last, ← stdFamilyV_ι]
    exact stdFamilyV_ι_range_le_commutator E m hm hK hq (Fin.last m)

theorem stdFamilyV_θ_mem_commutator (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (i j : Fin (m + 1)) (a : Su K 2 f 3) :
    (stdFamilyV E m hm).θ i j a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · rw [stdFamilyV_θ, stdTheta_castSucc]
    exact stdThetaAt_mem_commutator E m hK hq i j' a
  · rw [stdFamilyV_θ, stdTheta_last]
    exact stdForkTheta_mem_commutator E m hm hK hq a

@[expose] noncomputable def stdFamilyΩ (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    PhanFamilyE K 2 f (CFSG.StandardType.ggCoxeterMatrixD (m + 1))
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆ where
  ι k := ((stdFamilyV E m hm).ι k).codRestrict _ fun a =>
    stdFamilyV_ι_mem_commutator E m hm hK hq k a
  θ i j := ((stdFamilyV E m hm).θ i j).codRestrict _ fun a =>
    stdFamilyV_θ_mem_commutator E m hm hK hq i j a
  left i j hij hM := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun ((stdFamilyV E m hm).left i j hij hM) a
  right i j hij hM := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun ((stdFamilyV E m hm).right i j hij hM) a
  comm i j hM a b := Subtype.ext ((stdFamilyV E m hm).comm i j hM a b)

@[simp] theorem coe_stdFamilyΩ_ι (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (k : Fin (m + 1)) :
    (Subgroup.subtype ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆).comp
        ((stdFamilyΩ E m hm hK hq).ι k) = (stdFamilyV E m hm).ι k := by
  ext a
  rfl

@[simp] theorem coe_stdFamilyΩ_θ (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (i j : Fin (m + 1)) :
    (Subgroup.subtype ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆).comp
        ((stdFamilyΩ E m hm hK hq).θ i j) = (stdFamilyV E m hm).θ i j := by
  ext a
  rfl

end CFSG.ClassicalInvolution.PhanDn
