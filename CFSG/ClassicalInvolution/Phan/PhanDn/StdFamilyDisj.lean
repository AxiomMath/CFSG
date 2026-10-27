module

public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamily

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

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 f))

omit [Finite K] [CharP K 2] in
theorem eq_one_of_forall_single {m : ℕ}
    {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    (hsmul : ∀ (c : K) (v : Fin (m + 1) → K), g (c • v) = c • g v)
    (h : ∀ c : Fin (m + 1), g (Pi.single c (1 : K)) = Pi.single c (1 : K)) : g = 1 := by
  apply LinearEquiv.ext
  intro v
  have hv : v = ∑ c, v c • (Pi.single c (1 : K) : Fin (m + 1) → K) := by
    funext d
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hc
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hc), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ d) h
  calc g v = g (∑ c, v c • (Pi.single c (1 : K) : Fin (m + 1) → K)) := congrArg g hv
    _ = ∑ c, g (v c • (Pi.single c (1 : K) : Fin (m + 1) → K)) := by rw [map_sum]
    _ = ∑ c, v c • g (Pi.single c (1 : K)) := by
          exact Finset.sum_congr rfl fun c _ => hsmul (v c) _
    _ = ∑ c, v c • (Pi.single c (1 : K) : Fin (m + 1) → K) := by
          exact Finset.sum_congr rfl fun c _ => by rw [h c]
    _ = v := hv.symm

theorem stdChainIota_apply {m : ℕ} (k : Fin m) (a : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    stdChainIota (F := F) (f := f) m k a v = blockEmb2 K 2 f m k a • v := by
  unfold stdChainIota
  rw [MonoidHom.comp_apply, suEndN_apply]

theorem su_smul_smul {n : ℕ} (g : Su K 2 f n) (c : K) (v : Fin n → K) :
    g • (c • v) = c • (g • v) :=
  (SMulCommClass.smul_comm c (g : SUid (unitaryInvolution K 2 f) n) v).symm

theorem stdChainIota_smul {m : ℕ} (k : Fin m) (a : Su K 2 f 2)
    (c : K) (v : Fin (m + 1) → K) :
    stdChainIota (F := F) (f := f) m k a (c • v) =
      c • stdChainIota (F := F) (f := f) m k a v := by
  rw [stdChainIota_apply, stdChainIota_apply]
  exact su_smul_smul _ _ _

theorem stdChainIota_apply_of_not_mem {m : ℕ} (k : Fin m) (a : Su K 2 f 2)
    (v : Fin (m + 1) → K) {d : Fin (m + 1)}
    (hd : ¬ (k.val ≤ d.val ∧ d.val < k.val + 2)) :
    stdChainIota (F := F) (f := f) m k a v d = v d := by
  rw [stdChainIota_apply, smul_def, coe_coe_blockEmb2]
  exact blockMat_mulVec_of_not_mem _ v hd

theorem blockEmb2_smul_apply_left {m : ℕ} (k : Fin m) (A : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    (blockEmb2 K 2 f m k A • v) ⟨k.val, by omega⟩ =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * v ⟨k.val, by omega⟩ +
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
          v ⟨k.val + 1, by omega⟩ := by
  have hblk : k.val + 2 ≤ m + 1 := by omega
  rw [smul_def, coe_coe_blockEmb2]
  rw [show (⟨k.val, by omega⟩ : Fin (m + 1)) = blockIdx k.val hblk 0 from
    Fin.ext (by simp only [blockIdx_val]; omega)]
  rw [blockMat_mulVec_blockIdx]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (blockIdx k.val hblk 0 : Fin (m + 1)) = ⟨k.val, by omega⟩ from
    Fin.ext (by simp only [blockIdx_val]; omega),
    show (blockIdx k.val hblk 1 : Fin (m + 1)) = ⟨k.val + 1, by omega⟩ from
    Fin.ext (by simp only [blockIdx_val]; omega)]

theorem blockEmb2_smul_apply_right {m : ℕ} (k : Fin m) (A : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    (blockEmb2 K 2 f m k A • v) ⟨k.val + 1, by omega⟩ =
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 * v ⟨k.val, by omega⟩ +
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 *
          v ⟨k.val + 1, by omega⟩ := by
  have hblk : k.val + 2 ≤ m + 1 := by omega
  rw [smul_def, coe_coe_blockEmb2]
  rw [show (⟨k.val + 1, by omega⟩ : Fin (m + 1)) = blockIdx k.val hblk 1 from
    Fin.ext (by simp only [blockIdx_val]; omega)]
  rw [blockMat_mulVec_blockIdx]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (blockIdx k.val hblk 0 : Fin (m + 1)) = ⟨k.val, by omega⟩ from
    Fin.ext (by simp only [blockIdx_val]; omega),
    show (blockIdx k.val hblk 1 : Fin (m + 1)) = ⟨k.val + 1, by omega⟩ from
    Fin.ext (by simp only [blockIdx_val]; omega)]

theorem stdChainIota_single_of_not_mem {m : ℕ} (k : Fin m) (a : Su K 2 f 2)
    {c : Fin (m + 1)} (h1 : c.val ≠ k.val) (h2 : c.val ≠ k.val + 1) :
    stdChainIota (F := F) (f := f) m k a (Pi.single c (1 : K)) =
      Pi.single c (1 : K) := by
  funext d
  by_cases hd : k.val ≤ d.val ∧ d.val < k.val + 2
  · have hdk : d.val = k.val ∨ d.val = k.val + 1 := by omega
    have hdc : d ≠ c := by
      intro h
      rcases hdk with h' | h'
      · exact h1 (by simpa [h] using h')
      · exact h2 (by simpa [h] using h')
    rw [Pi.single_eq_of_ne hdc]
    have hck : c ≠ (⟨k.val, by omega⟩ : Fin (m + 1)) := by
      intro h; exact h1 (by rw [h])
    have hck1 : c ≠ (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
      intro h; exact h2 (by rw [h])
    rcases hdk with h' | h'
    · have hd' : d = ⟨k.val, by omega⟩ := Fin.ext h'
      rw [hd', stdChainIota_apply, blockEmb2_smul_apply_left,
        Pi.single_eq_of_ne (Ne.symm hck), Pi.single_eq_of_ne (Ne.symm hck1)]
      simp
    · have hd' : d = ⟨k.val + 1, by omega⟩ := Fin.ext h'
      rw [hd', stdChainIota_apply, blockEmb2_smul_apply_right,
        Pi.single_eq_of_ne (Ne.symm hck), Pi.single_eq_of_ne (Ne.symm hck1)]
      simp
  · rw [stdChainIota_apply_of_not_mem _ _ _ hd]

theorem stdChainTheta_apply {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) (a : Su K 2 f 3)
    (v : Fin (m + 1) → K) :
    stdChainTheta (F := F) (f := f) m k hk a v = blockEmb3 K 2 f m k hk a • v := by
  unfold stdChainTheta
  rw [MonoidHom.comp_apply, suEndN_apply]

theorem stdChainTheta_smul {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) (a : Su K 2 f 3)
    (c : K) (v : Fin (m + 1) → K) :
    stdChainTheta (F := F) (f := f) m k hk a (c • v) =
      c • stdChainTheta (F := F) (f := f) m k hk a v := by
  rw [stdChainTheta_apply, stdChainTheta_apply]
  exact su_smul_smul (blockEmb3 K 2 f m k hk a) c v

theorem stdChainTheta_single_of_not_mem {m : ℕ} (k : Fin m) (hk : k.val + 1 < m)
    (a : Su K 2 f 3) {c : Fin (m + 1)}
    (hc : ¬ (k.val ≤ c.val ∧ c.val < k.val + 3)) :
    stdChainTheta (F := F) (f := f) m k hk a (Pi.single c (1 : K)) =
      Pi.single c (1 : K) := by
  rw [stdChainTheta_apply]
  exact blockEmb_smul_single_of_not_mem (p := 2) (f := f) (m := m + 1) (k := 3)
    (i := k.val) (h := by omega) a hc

private theorem stdTau_single_of_ne_last {m : ℕ} {c : Fin (m + 1)} (hc : c ≠ Fin.last m) :
    stdTau E m (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
  funext d
  unfold stdTau
  rw [tauAt_apply]
  by_cases hd : d = Fin.last m
  · subst hd
    rw [if_pos rfl, Pi.single_eq_of_ne (Ne.symm hc), map_zero]
  · rw [if_neg hd]

theorem stdForkTheta_single_of_not_mem {m : ℕ} (hm : 3 ≤ m) (a : Su K 2 f 3)
    {c : Fin (m + 1)} (h1 : c.val ≠ m - 2) (h2 : c.val ≠ m - 1) (h3 : c.val ≠ m) :
    stdForkTheta E m hm a (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
  have hc_last : c ≠ Fin.last m := by
    intro h
    exact h3 (by simpa using congrArg Fin.val h)
  have hk : (m - 2) + 1 < m := by omega
  have hq : stdChainTheta (F := F) (f := f) m ⟨m - 2, by omega⟩ hk a
      (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    refine stdChainTheta_single_of_not_mem (k := ⟨m - 2, by omega⟩) (hk := hk)
      (a := a) ?_
    rintro ⟨hle, hlt⟩
    change m - 2 ≤ c.val at hle
    change c.val < m - 2 + 3 at hlt
    rcases eq_or_ne c.val (m - 2) with h | h
    · exact h1 h
    rcases eq_or_ne c.val (m - 1) with h' | h'
    · exact h2 h'
    rcases eq_or_ne c.val m with h'' | h''
    · exact h3 h''
    · omega
  unfold stdForkTheta stdConj
  rw [MonoidHom.comp_apply]
  change MulAut.conj (stdTau E m)
      (stdChainTheta (F := F) (f := f) m ⟨m - 2, by omega⟩ hk a)
      (Pi.single c (1 : K)) = Pi.single c (1 : K)
  rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hτ : stdTau E m (Pi.single c (1 : K)) = Pi.single c (1 : K) :=
    stdTau_single_of_ne_last E hc_last
  have hτinv : (stdTau E m)⁻¹ (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    unfold stdTau
    rw [inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))]
    exact hτ
  rw [hτinv, hq, hτ]

theorem stdForkIota_apply {m : ℕ} (hm : 3 ≤ m) (b : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    stdForkIota E m hm b v =
      stdTau E m (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ b • (stdTau E m v)) := by
  unfold stdForkIota stdConj
  rw [MonoidHom.comp_apply]
  change MulAut.conj (stdTau E m)
      (stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ b) v = _
  rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hτ : (stdTau E m)⁻¹ = stdTau E m := by
    unfold stdTau
    exact inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))
  rw [hτ, stdChainIota_apply]

theorem stdForkIota_apply_of_not_mem {m : ℕ} (hm : 3 ≤ m) (b : Su K 2 f 2)
    (v : Fin (m + 1) → K) {d : Fin (m + 1)}
    (hd1 : d.val ≠ m - 1) (hd2 : d.val ≠ m) :
    stdForkIota E m hm b v d = v d := by
  rw [stdForkIota_apply]
  have hdq : d ≠ Fin.last m := by
    intro h
    exact hd2 (by simpa using congrArg Fin.val h)
  have hτv : stdTau E m v d = v d := by
    unfold stdTau
    rw [tauAt_apply, if_neg hdq]
  have hsd : (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ b • (stdTau E m v)) d =
      (stdTau E m v) d :=
    blockEmb2_last_smul_of_ne hm b _ hd1 hd2
  have hgoal : stdTau E m (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ b • (stdTau E m v)) d =
      v d := by
    unfold stdTau at hsd hτv ⊢
    rw [tauAt_apply, if_neg hdq]
    rw [hsd, hτv]
  exact hgoal

theorem stdForkIota_apply_left {m : ℕ} (hm : 3 ≤ m) (b : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    stdForkIota E m hm b v ⟨m - 1, by omega⟩ =
      ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 * v ⟨m - 1, by omega⟩ +
        ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
          unitaryInvolution K 2 f (v (Fin.last m)) := by
  rw [stdForkIota_apply]
  have hp : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  unfold stdTau
  rw [tauAt_apply, if_neg hp]
  rw [blockEmb2_last_smul_zero hm b]
  rw [show (tauAt E (Fin.last m) v) ⟨m - 1, by omega⟩ = v ⟨m - 1, by omega⟩ from by
    rw [tauAt_apply, if_neg hp]]
  rw [show (tauAt E (Fin.last m) v) (Fin.last m) =
      unitaryInvolution K 2 f (v (Fin.last m)) from by
    rw [tauAt_apply, if_pos rfl]]

theorem stdForkIota_apply_right {m : ℕ} (hm : 3 ≤ m) (b : Su K 2 f 2)
    (v : Fin (m + 1) → K) :
    stdForkIota E m hm b v (Fin.last m) =
      unitaryInvolution K 2 f (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) *
          unitaryInvolution K 2 f (v ⟨m - 1, by omega⟩) +
        unitaryInvolution K 2 f (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) *
          v (Fin.last m) := by
  rw [stdForkIota_apply]
  have hp : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  unfold stdTau
  rw [tauAt_apply, if_pos rfl]
  rw [blockEmb2_last_smul_one hm b]
  rw [map_add, map_mul, map_mul]
  rw [show (tauAt E (Fin.last m) v) ⟨m - 1, by omega⟩ = v ⟨m - 1, by omega⟩ from by
    rw [tauAt_apply, if_neg hp]]
  rw [show (tauAt E (Fin.last m) v) (Fin.last m) =
      unitaryInvolution K 2 f (v (Fin.last m)) from by
    rw [tauAt_apply, if_pos rfl]]
  rw [E.isUnitary.invol]

theorem stdForkIota_single_of_not_mem {m : ℕ} (hm : 3 ≤ m) (b : Su K 2 f 2)
    {c : Fin (m + 1)} (h1 : c.val ≠ m - 1) (h2 : c.val ≠ m) :
    stdForkIota E m hm b (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
  funext d
  by_cases hd : d.val = m - 1 ∨ d.val = m
  · have hdc : d ≠ c := by
      intro h
      rcases hd with h' | h'
      · exact h1 (by simpa [h] using h')
      · exact h2 (by simpa [h] using h')
    rw [Pi.single_eq_of_ne hdc]
    have hcp : c ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
      intro h; exact h1 (by rw [h])
    have hcq : c ≠ Fin.last m := by
      intro h
      exact h2 (by simpa using congrArg Fin.val h)
    rcases hd with h' | h'
    · have hd' : d = ⟨m - 1, by omega⟩ := Fin.ext h'
      rw [hd', stdForkIota_apply_left,
        Pi.single_eq_of_ne (Ne.symm hcp), Pi.single_eq_of_ne (Ne.symm hcq)]
      simp
    · have hd' : d = Fin.last m := Fin.ext (by simpa using h')
      rw [hd', stdForkIota_apply_right,
        Pi.single_eq_of_ne (Ne.symm hcp), Pi.single_eq_of_ne (Ne.symm hcq)]
      simp
  · rw [stdForkIota_apply_of_not_mem E hm b _ (by omega) (by omega)]

private theorem chainIota_eq_one_of_eq_succ {m : ℕ} (k : Fin m)
    (hk : k.val + 1 < m) (a b : Su K 2 f 2)
    (h : stdChainIota (F := F) (f := f) m ⟨k.val + 1, hk⟩ b =
      stdChainIota (F := F) (f := f) m k a) :
    stdChainIota (F := F) (f := f) m ⟨k.val + 1, hk⟩ b = 1 := by
  have hc : k.val + 2 < m + 1 := by omega
  have hp : k.val < m + 1 := by omega
  have hsucc : k.val + 1 < m + 1 := by omega
  have hB01 : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have hval := DFunLike.congr_fun h (Pi.single ⟨k.val + 2, hc⟩ (1 : K) : Fin (m + 1) → K)
    have hleft := congrFun hval ⟨k.val + 1, hsucc⟩
    rw [stdChainIota_apply, blockEmb2_smul_apply_left] at hleft
    rw [stdChainIota_apply, blockEmb2_smul_apply_right] at hleft
    rw [Pi.single_eq_same] at hleft
    rw [Pi.single_eq_of_ne (show (⟨k.val + 1, hsucc⟩ : Fin (m + 1)) ≠ ⟨k.val + 2, hc⟩ by
      intro hh
      have := congrArg Fin.val hh
      simp at this)] at hleft
    rw [Pi.single_eq_of_ne (show (⟨k.val, hp⟩ : Fin (m + 1)) ≠ ⟨k.val + 2, hc⟩ by
      intro hh
      have := congrArg Fin.val hh
      simp at this)] at hleft
    simpa using hleft
  have hB11 : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hval := DFunLike.congr_fun h (Pi.single ⟨k.val + 2, hc⟩ (1 : K) : Fin (m + 1) → K)
    have hright := congrFun hval ⟨k.val + 2, hc⟩
    rw [stdChainIota_apply, blockEmb2_smul_apply_right] at hright
    rw [stdChainIota_apply_of_not_mem _ _ _ (by simp)] at hright
    rw [Pi.single_eq_same] at hright
    rw [Pi.single_eq_of_ne (show (⟨k.val + 1, hsucc⟩ : Fin (m + 1)) ≠ ⟨k.val + 2, hc⟩ by
      intro hh
      have := congrArg Fin.val hh
      simp at this)] at hright
    simpa using hright
  have hB00 : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hdet : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := b.2.1
    rw [Matrix.det_fin_two] at hdet
    rw [hB01, hB11] at hdet
    simpa using hdet
  have hB10 : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have hshape := (SUid_two_entries b).1
    rw [hB01, map_zero] at hshape
    exact hshape
  have hb : b = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB00, hB01, hB10, hB11]
  rw [hb, map_one]

private theorem chainIota_eq_one_of_fork_pred {m : ℕ} (hm : 3 ≤ m) (a b : Su K 2 f 2)
    (h : stdChainIota (F := F) (f := f) m ⟨m - 2, by omega⟩ a = stdForkIota E m hm b) :
    stdChainIota (F := F) (f := f) m ⟨m - 2, by omega⟩ a = 1 := by
  have hA00 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hfix : stdForkIota E m hm b (Pi.single ⟨m - 2, by omega⟩ (1 : K)) =
        Pi.single ⟨m - 2, by omega⟩ (1 : K) :=
      stdForkIota_single_of_not_mem E hm b
        (by simp; omega) (by simp; omega)
    have hval := congrFun (h.symm ▸ hfix) ⟨m - 2, by omega⟩
    rw [stdChainIota_apply, blockEmb2_smul_apply_left] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne
      (show (⟨(⟨m - 2, by omega⟩ : Fin m).val + 1, by omega⟩ : Fin (m + 1)) ≠
        ⟨m - 2, by omega⟩ by
        intro hh
        have := congrArg Fin.val hh
        simp at this)] at hval
    simpa using hval
  have hA10 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have hfix : stdForkIota E m hm b (Pi.single ⟨m - 2, by omega⟩ (1 : K)) =
        Pi.single ⟨m - 2, by omega⟩ (1 : K) :=
      stdForkIota_single_of_not_mem E hm b
        (by simp; omega) (by simp; omega)
    have hval := congrFun (h.symm ▸ hfix) ⟨m - 1, by omega⟩
    rw [show (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        ⟨(⟨m - 2, by omega⟩ : Fin m).val + 1, by omega⟩ from
        Fin.ext (by simp; omega)] at hval
    rw [stdChainIota_apply, blockEmb2_smul_apply_right] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne
      (show (⟨(⟨m - 2, by omega⟩ : Fin m).val + 1, by omega⟩ : Fin (m + 1)) ≠
        ⟨m - 2, by omega⟩ by
        intro hh
        have := congrArg Fin.val hh
        simp at this)] at hval
    simpa using hval
  have hA01 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have hval := DFunLike.congr_fun h (Pi.single ⟨m - 1, by omega⟩ (1 : K))
    have hval := congrFun hval ⟨m - 2, by omega⟩
    rw [stdChainIota_apply, blockEmb2_smul_apply_left] at hval
    rw [stdForkIota_apply_of_not_mem E hm b _
      (by simp; omega) (by simp; omega)] at hval
    rw [show (⟨(⟨m - 2, by omega⟩ : Fin m).val + 1, by omega⟩ : Fin (m + 1)) =
        ⟨m - 1, by omega⟩ from Fin.ext (by simp; omega)] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne
      (show (⟨(⟨m - 2, by omega⟩ : Fin m).val, by omega⟩ : Fin (m + 1)) ≠
        ⟨m - 1, by omega⟩ by
        intro hh; have := congrArg Fin.val hh
        simp at this; omega)] at hval
    simpa using hval
  have hA11 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hdet : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := a.2.1
    rw [Matrix.det_fin_two] at hdet
    rw [hA00, hA01, hA10] at hdet
    simpa using hdet
  have ha : a = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA00, hA01, hA10, hA11]
  rw [ha, map_one]

private theorem chainIota_eq_one_of_fork_last {m : ℕ} (hm : 3 ≤ m) (a b : Su K 2 f 2)
    (h : stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a = stdForkIota E m hm b) :
    stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a = 1 := by
  obtain ⟨c, hc⟩ := E.isUnitary.exists_ne
  have hcne : c - unitaryInvolution K 2 f c ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hc)
  have hA00 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have hval := DFunLike.congr_fun h (Pi.single ⟨m - 1, by omega⟩ (1 : K))
    have hval := congrFun hval ⟨m - 1, by omega⟩
    rw [stdChainIota_apply, blockEmb2_last_smul_zero hm a] at hval
    rw [stdForkIota_apply_left] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (Fin.last m) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simpa using hval
  have hA10 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      unitaryInvolution K 2 f
        (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    have hval := DFunLike.congr_fun h (Pi.single ⟨m - 1, by omega⟩ (1 : K))
    have hval := congrFun hval (Fin.last m)
    rw [stdChainIota_apply, blockEmb2_last_smul_one hm a] at hval
    rw [stdForkIota_apply_right] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (Fin.last m) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simpa using hval
  have hA01 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have hval := DFunLike.congr_fun h (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K)
    have hval := congrFun hval ⟨m - 1, by omega⟩
    rw [stdChainIota_apply, blockEmb2_last_smul_zero hm a] at hval
    rw [stdForkIota_apply_left] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simpa using hval
  have hA11 : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      unitaryInvolution K 2 f
        (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) := by
    have hval := DFunLike.congr_fun h (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K)
    have hval := congrFun hval (Fin.last m)
    rw [stdChainIota_apply, blockEmb2_last_smul_one hm a] at hval
    rw [stdForkIota_apply_right] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simpa using hval
  have hA10' : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have hval := DFunLike.congr_fun h (c • (Pi.single ⟨m - 1, by omega⟩ (1 : K) : Fin (m + 1) → K))
    have hval := congrFun hval (Fin.last m)
    rw [stdChainIota_apply, blockEmb2_last_smul_one hm a] at hval
    rw [stdForkIota_apply_right] at hval
    simp only [Pi.smul_apply] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (Fin.last m) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at hval
    rw [hA10] at hval
    have hzero : unitaryInvolution K 2 f
        (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) *
        (c - unitaryInvolution K 2 f c) = 0 := by
      linear_combination hval
    have hB10 : unitaryInvolution K 2 f
        (((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hcne
    rw [hA10, hB10]
  have hA01' : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have hval := DFunLike.congr_fun h (c • (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K))
    have hval := congrFun hval ⟨m - 1, by omega⟩
    rw [stdChainIota_apply, blockEmb2_last_smul_zero hm a] at hval
    rw [stdForkIota_apply_left] at hval
    simp only [Pi.smul_apply] at hval
    rw [Pi.single_eq_same] at hval
    rw [Pi.single_eq_of_ne (show (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m by
      intro hh
      have := congrArg Fin.val hh
      simp at this; omega)] at hval
    simp only [smul_eq_mul, mul_one, mul_zero] at hval
    rw [hA01] at hval
    have hzero : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (c - unitaryInvolution K 2 f c) = 0 := by
      linear_combination hval
    have hB01 : ((b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hcne
    rw [hA01, hB01]
  have hdiag : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have hshape := (SUid_two_entries b).2
    rw [hA00, hA11, hshape]
    simp only [E.isUnitary.invol]
  have hsq : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
      ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hdet : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := a.2.1
    rw [Matrix.det_fin_two] at hdet
    rw [hA01', hA10'] at hdet
    rw [hdiag] at hdet ⊢
    simpa [mul_comm] using hdet
  have hA00' : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hsq' : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 = 1 := by
      rw [pow_two]; exact hsq
    rcases (sq_eq_one_iff.mp hsq') with h1 | hm1
    · exact h1
    · rw [hm1]
      exact CharTwo.neg_eq 1
  have hA11' : ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [← hdiag, hA00']
  have ha : a = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA00', hA01', hA10', hA11']
  rw [ha, map_one]

theorem edgeD_lt_of {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (h : edgeD n i j) : i < j := by
  rw [edgeD_iff_of_four_le hn] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Fin.lt_def.mpr (by omega)
  · exact Fin.lt_def.mpr (by omega)

theorem stdThetaAt_eq_chainTheta {m : ℕ} {i : Fin (m + 1)} {j' : Fin m}
    (h : i.val + 1 = j'.val) (hi : i.val < m) :
    stdThetaAt (F := F) (K := K) (f := f) m i j' =
      stdChainTheta (F := F) (K := K) (f := f) m ⟨i.val, hi⟩
        (by have := j'.isLt; simp; omega) := by
  unfold stdThetaAt
  rw [dif_pos h]

theorem stdFamilyV_θ_inj (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ} (hm : 3 ≤ m) :
    ∀ i j, i < j → CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3 →
      Function.Injective ((stdFamilyV E m hm).θ i j) := by
  intro i j hij hM
  rw [stdFamilyV_θ]
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · rw [stdTheta_castSucc]
    have hE : edgeD (m + 1) i (Fin.castSucc j') := by
      rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i
        (Fin.castSucc j')).1 hM with h | h
      · exact h
      · exact absurd (edgeD_lt_of (by omega) h) (not_lt.mpr (le_of_lt hij))
    rw [edgeD_iff_of_four_le (by omega)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.val_castSucc] at h1
      have hi : i.val < m := by have := j'.isLt; omega
      rw [stdThetaAt_eq_chainTheta (F := F) (f := f) (m := m) (i := i) (j' := j') h1 hi]
      unfold stdChainTheta
      exact (suEndN_injective (F := F) (unitaryInvolution K 2 f) (m + 1)).comp
        (blockEmb3_injective m ⟨i.val, hi⟩
          (by have := j'.isLt; simp; omega))
    · have := j'.isLt
      simp only [Fin.val_castSucc] at h2
      omega
  · rw [stdTheta_last]
    unfold stdForkTheta
    have hlt : m - 2 < m := by omega
    have hlt' : m - 2 + 1 < m := by omega
    exact (stdConj E m).injective.comp
      ((suEndN_injective (F := F) (unitaryInvolution K 2 f) (m + 1)).comp
        (blockEmb3_injective m ⟨m - 2, hlt⟩ hlt'))

private theorem chainIota_inf_chainIota_eq_bot {m : ℕ} {i' j' : Fin m} (hij : i' ≠ j') :
    (stdChainIota (K := K) (F := F) (f := f) m i').range ⊓
      (stdChainIota (K := K) (F := F) (f := f) m j').range = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hx
  obtain ⟨a, rfl⟩ := hx.1
  obtain ⟨b, hb⟩ := hx.2
  by_cases hji : j'.val = i'.val + 1
  · have hji' : j' = ⟨i'.val + 1, by omega⟩ := Fin.ext hji
    rw [hji'] at hb
    rw [← hb]
    exact chainIota_eq_one_of_eq_succ i' (by omega) a b hb
  · by_cases hij' : i'.val = j'.val + 1
    · have hij'' : i' = ⟨j'.val + 1, by omega⟩ := Fin.ext hij'
      rw [hij''] at hb ⊢
      exact chainIota_eq_one_of_eq_succ j' (by omega) b a hb.symm
    · have hne : i'.val ≠ j'.val := by
        intro h
        exact hij (Fin.ext h)
      have hfar : i'.val + 1 < j'.val ∨ j'.val + 1 < i'.val := by omega
      have hsingle : ∀ c : Fin (m + 1),
          stdChainIota (F := F) (f := f) m j' b (Pi.single c (1 : K)) =
            Pi.single c (1 : K) := by
        intro c
        by_cases hc : i'.val ≤ c.val ∧ c.val < i'.val + 2
        · have h1 : c.val ≠ j'.val := by omega
          have h2 : c.val ≠ j'.val + 1 := by omega
          exact stdChainIota_single_of_not_mem j' b h1 h2
        · have h1 : c.val ≠ i'.val := by
            intro h
            exact hc ⟨le_of_eq h.symm, by omega⟩
          have h2 : c.val ≠ i'.val + 1 := by
            intro h
            exact hc ⟨by omega, by omega⟩
          rw [hb]
          exact stdChainIota_single_of_not_mem i' a h1 h2
      rw [← hb]
      exact eq_one_of_forall_single
        (fun c v => stdChainIota_smul (F := F) (f := f) j' b c v) hsingle

private theorem chainIota_inf_forkIota_eq_bot {m : ℕ} (hm : 3 ≤ m) (i' : Fin m) :
    (stdChainIota (F := F) (f := f) m i').range ⊓ (stdForkIota E m hm).range = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hx
  obtain ⟨a, rfl⟩ := hx.1
  obtain ⟨b, hb⟩ := hx.2
  by_cases hfar : i'.val ≤ m - 3
  · have hsingle : ∀ c : Fin (m + 1),
        stdChainIota (F := F) (f := f) m i' a (Pi.single c (1 : K)) =
          Pi.single c (1 : K) := by
      intro c
      by_cases hc : i'.val ≤ c.val ∧ c.val < i'.val + 2
      · rw [← hb]
        exact stdForkIota_single_of_not_mem E hm b (by omega) (by omega)
      · exact stdChainIota_single_of_not_mem i' a (by omega) (by omega)
    exact eq_one_of_forall_single
      (fun c v => stdChainIota_smul (F := F) (f := f) i' a c v) hsingle
  · by_cases hlast : i'.val = m - 1
    · have hi' : i' = ⟨m - 1, by omega⟩ := Fin.ext hlast
      rw [hi'] at hb ⊢
      exact chainIota_eq_one_of_fork_last (E := E) hm a b hb.symm
    · have hge : m - 2 ≤ i'.val := by omega
      have hle : i'.val ≤ m - 2 := by have := i'.isLt; omega
      have hlt : m - 2 < m := by omega
      have hival : i'.val = m - 2 := by omega
      have hi' : i' = ⟨m - 2, hlt⟩ := Fin.ext hival
      rw [hi'] at hb ⊢
      exact chainIota_eq_one_of_fork_pred (E := E) hm a b hb.symm

theorem stdFamilyV_disj (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ} (hm : 3 ≤ m) :
    ∀ i j, i ≠ j →
      ((stdFamilyV E m hm).ι i).range ⊓ ((stdFamilyV E m hm).ι j).range = ⊥ := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨i', rfl⟩ | rfl
  · rw [stdFamilyV_ι_castSucc]
    rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
    · rw [stdFamilyV_ι_castSucc]
      exact chainIota_inf_chainIota_eq_bot (fun h => hij (by rw [h]))
    · rw [stdFamilyV_ι_last]
      exact chainIota_inf_forkIota_eq_bot E hm i'
  · rw [stdFamilyV_ι_last]
    rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
    · rw [stdFamilyV_ι_castSucc, inf_comm]
      exact chainIota_inf_forkIota_eq_bot E hm j'
    · exact absurd rfl hij

theorem stdFamilyV_inj (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ} (hm : 3 ≤ m)
    (i : Fin (m + 1)) :
    Function.Injective ((stdFamilyV E m hm).ι i) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · rw [stdFamilyV_ι_castSucc]
    unfold stdChainIota
    exact (suEndN_injective (F := F) (unitaryInvolution K 2 f) (m + 1)).comp
      (blockEmb2_injective m k)
  · rw [stdFamilyV_ι_last]
    unfold stdForkIota stdChainIota
    exact (stdConj E m).injective.comp
      ((suEndN_injective (F := F) (unitaryInvolution K 2 f) (m + 1)).comp
        (blockEmb2_injective m ⟨m - 1, by omega⟩))

end CFSG.ClassicalInvolution.PhanDn
