module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitFox

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar Matrix


@[expose] noncomputable def aM (ε : Eps) (i : Fin 7) (f : Fin (mOf ε) → V7) : Fin (mOf ε) → V7 :=
  indAct (rhoE ε) (alphaZ ε) (sGen ε i) f

theorem aM_add (ε : Eps) (i : Fin 7) (f f' : Fin (mOf ε) → V7) :
    aM ε i (f + f') = aM ε i f + aM ε i f' := indAct_add _ _ _ f f'

@[expose] noncomputable def aE (ε : Eps) (i : Fin 7) (x : V7) : V7 := rhoE ε (sGen ε i) x

theorem aE_add (ε : Eps) (i : Fin 7) (x y : V7) : aE ε i (x + y) = aE ε i x + aE ε i y :=
  map_add _ x y

theorem relWords_getD_lt {j : ℕ} : ∀ i ∈ relWords.getD j [], i < 7 := by
  by_cases hj : j < relWords.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact relWords_lt _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    simp

theorem rels7_getD (j : ℕ) : rels7.getD j [] = (relWords.getD j []).map (Fin.ofNat 7) := by
  by_cases hj : j < relWords.length
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa [rels7] using hj)]
    simp [rels7]
  · rw [List.getD_eq_default _ _ (not_lt.mp hj), List.getD_eq_default _ _ (by
      simpa [rels7] using not_lt.mp hj)]
    rfl

theorem rels7_length : rels7.length = 29 := by simp [rels7, relWords]

theorem mem_rels7 {w : List (Fin 7)} (hw : w ∈ rels7) : ∃ j < 29, rels7.getD j [] = w := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
  exact ⟨j, by rw [← rels7_length]; exact hj, List.getD_eq_getElem _ _ hj⟩

theorem foxMCode_lt (ε : Eps) {d : ℕ → ℕ} (hd : ∀ i, d i < 2 ^ nM ε) :
    ∀ {w : List ℕ}, (∀ i ∈ w, i < 7) → foxMCode ε d w < 2 ^ nM ε
  | [], _ => by simp [foxMCode]
  | i :: w, hw => by
    have hi := hw i List.mem_cons_self
    have h2 : actMCode ε i (foxMCode ε d w) < 2 ^ nM ε := by
      rw [actMCode_eq, nM, Nat.mul_comm]
      exact foldOr_lt (by norm_num) _ fun g _ => actECode_lt ε hi (blkN_lt 7 _ _)
    exact Nat.xor_lt_two_pow (hd i) h2

@[expose] def unpackD (ε : Eps) (y : Fin (7 * nM ε) → ZMod 2) : Fin 7 → Fin (mOf ε) → V7 :=
  fun i => unpackV (mOf ε) 7 (unpackV 7 (nM ε) y i)

@[expose] def packR (ε : Eps) (F : Fin 29 → Fin (mOf ε) → V7) : Fin (29 * nM ε) → ZMod 2 :=
  packV 29 (nM ε) fun j => packV (mOf ε) 7 (F j)

theorem packR_add (ε : Eps) (F G : Fin 29 → Fin (mOf ε) → V7) :
    packR ε (F + G) = packR ε F + packR ε G := rfl

theorem packR_zero (ε : Eps) : packR ε 0 = 0 := rfl

theorem unpackR_packR (ε : Eps) (F : Fin 29 → Fin (mOf ε) → V7) (j : Fin 29) :
    unpackV (mOf ε) 7 (unpackV 29 (nM ε) (packR ε F) j) = F j := by
  rw [packR, unpackV_packV, unpackV_packV]

@[expose] noncomputable def fmFun (ε : Eps) (y : Fin (7 * nM ε) → ZMod 2) :
    Fin (29 * nM ε) → ZMod 2 :=
  packR ε fun j => foxSum (aM ε) (unpackD ε y) (rels7.getD j [])

theorem fmFun_zero (ε : Eps) : fmFun ε 0 = 0 := by
  show packR ε _ = 0
  rw [← packR_zero ε]
  congr 1
  funext j
  exact foxSum_zero (aM ε) (aM_add ε) _

theorem fmFun_add (ε : Eps) (y z : Fin (7 * nM ε) → ZMod 2) :
    fmFun ε (y + z) = fmFun ε y + fmFun ε z := by
  show packR ε _ = packR ε _ + packR ε _
  rw [← packR_add]
  congr 1
  funext j
  exact foxSum_add (aM ε) (aM_add ε) (unpackD ε y) (unpackD ε z) _

@[expose] noncomputable def fmLin (ε : Eps) :
    (Fin (7 * nM ε) → ZMod 2) →ₗ[ZMod 2] (Fin (29 * nM ε) → ZMod 2) where
  toFun := fmFun ε
  map_add' := fmFun_add ε
  map_smul' c y := by
    rcases zmod2_cases c with rfl | rfl
    · simp [fmFun_zero]
    · simp

theorem fmLin_apply (ε : Eps) (y : Fin (7 * nM ε) → ZMod 2) : fmLin ε y = fmFun ε y := rfl

theorem toVec_foxMb (ε : Eps) (v : ℕ) :
    toVec (29 * nM ε) (foxMb ε v) = fmLin ε (toVec (7 * nM ε) v) := by
  have hm : 0 < nM ε := by cases ε <;> decide
  apply unpackV_injective 29 (nM ε)
  rw [foxMb, toVec_foldOr hm _ (fun j _ => foxMCode_lt ε (fun i => blkN_lt _ _ _)
    relWords_getD_lt), fmLin_apply, fmFun]
  ext1 j
  apply unpackV_injective (mOf ε) 7
  rw [unpackR_packR]
  show unpackV (mOf ε) 7 (toVec (mOf ε * 7) (foxMCode ε (blkN (nM ε) v)
    (relWords.getD j []))) = _
  rw [unpack_foxMCode ε _ relWords_getD_lt, rels7_getD]
  congr 1
  ext1 i
  exact congrArg (unpackV (mOf ε) 7) (toVec_blkN (k := 7) v i)

@[expose] def ioFun (ε : Eps) (c : Fin 203 → ZMod 2) : Fin (29 * nM ε) → ZMod 2 :=
  packR ε fun j _ => unpackV 29 7 c j

@[expose] def ioLin (ε : Eps) : (Fin 203 → ZMod 2) →ₗ[ZMod 2] (Fin (29 * nM ε) → ZMod 2) where
  toFun := ioFun ε
  map_add' c d := rfl
  map_smul' a c := by
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]; rfl
    · simp

theorem ioLin_apply (ε : Eps) (c : Fin 203 → ZMod 2) : ioLin ε c = ioFun ε c := rfl

theorem toVec_constM (ε : Eps) {x : ℕ} (hx : x < 128) :
    unpackV (mOf ε) 7 (toVec (mOf ε * 7) (constM ε x)) = fun _ => toVec 7 x := by
  rw [constM, toVec_foldOr (by norm_num) _ (fun _ _ => hx)]

theorem toVec_iotaB (ε : Eps) (v : ℕ) : toVec (29 * nM ε) (iotaB ε v) = ioLin ε (toVec 203 v) := by
  have hm : 0 < nM ε := by cases ε <;> decide
  apply unpackV_injective 29 (nM ε)
  have hlt : ∀ j < 29, constM ε (blkN 7 v j) < 2 ^ nM ε := fun j _ => by
    rw [constM, nM, Nat.mul_comm]
    exact foldOr_lt (by norm_num) _ fun _ _ => blkN_lt 7 v j
  rw [iotaB, toVec_foldOr hm _ hlt, ioLin_apply, ioFun]
  ext1 j
  apply unpackV_injective (mOf ε) 7
  show unpackV (mOf ε) 7 (toVec (mOf ε * 7) (constM ε (blkN 7 v j))) = _
  rw [toVec_constM ε (blkN_lt 7 v j), unpackR_packR]
  funext g
  exact toVec_blkN (k := 29) v j

@[expose] noncomputable def feFun (ε : Eps) (e : Fin 49 → ZMod 2) : Fin 203 → ZMod 2 :=
  packV 29 7 fun j => foxSum (aE ε) (unpackV 7 7 e) (rels7.getD j [])

@[expose] noncomputable def feLin (ε : Eps) : (Fin 49 → ZMod 2) →ₗ[ZMod 2] (Fin 203 → ZMod 2) where
  toFun := feFun ε
  map_add' e f := by
    show packV 29 7 _ = packV 29 7 _ + packV 29 7 _
    rw [← packV_add]
    congr 1
    funext j
    exact foxSum_add (aE ε) (aE_add ε) (unpackV 7 7 e) (unpackV 7 7 f) _
  map_smul' a e := by
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      show packV 29 7 _ = 0
      have h : packV 29 7 (0 : Fin 29 → Fin 7 → ZMod 2) = 0 := rfl
      rw [← h]
      congr 1
      funext j
      exact foxSum_zero (aE ε) (aE_add ε) _
    · simp

theorem feLin_apply (ε : Eps) (e : Fin 49 → ZMod 2) : feLin ε e = feFun ε e := rfl

theorem toVec_foxEb (ε : Eps) (v : ℕ) : toVec 203 (foxEb ε v) = feLin ε (toVec 49 v) := by
  apply unpackV_injective 29 7
  rw [foxEb, toVec_foldOr (by norm_num) _ (fun j _ => foxECode_lt ε (fun i => blkN_lt 7 v i)
    relWords_getD_lt), feLin_apply, feFun, unpackV_packV]
  ext1 j
  rw [toVec_foxECode ε (fun i => blkN_lt 7 v i) relWords_getD_lt, rels7_getD]
  congr 1
  ext1 i
  exact toVec_blkN (k := 7) v i

@[expose] def cobFb (ε : Eps) (v : ℕ) : ℕ := foldOr 7 7 fun i => actECode ε i v ^^^ v

@[expose] noncomputable def cobFun (ε : Eps) (x : Fin 7 → ZMod 2) : Fin 49 → ZMod 2 :=
  packV 7 7 fun i => aE ε i x + x

@[expose] noncomputable def cobLin (ε : Eps) : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 49 → ZMod 2) where
  toFun := cobFun ε
  map_add' x y := by
    show packV 7 7 _ = packV 7 7 _ + packV 7 7 _
    rw [← packV_add]
    congr 1
    funext i
    simp only [Pi.add_apply, aE_add]
    abel
  map_smul' a x := by
    rcases zmod2_cases a with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      show packV 7 7 _ = 0
      have h : packV 7 7 (0 : Fin 7 → Fin 7 → ZMod 2) = 0 := rfl
      rw [← h]
      congr 1
      funext i
      simp only [aE, map_zero, add_zero]
      rfl
    · simp

theorem cobLin_apply (ε : Eps) (x : Fin 7 → ZMod 2) : cobLin ε x = cobFun ε x := rfl

theorem toVec_cobFb (ε : Eps) {v : ℕ} (hv : v < 128) :
    toVec 49 (cobFb ε v) = cobLin ε (toVec 7 v) := by
  apply unpackV_injective 7 7
  have hlt : ∀ i < 7, actECode ε i v ^^^ v < 2 ^ 7 := fun i hi =>
    Nat.xor_lt_two_pow (actECode_lt ε hi hv) hv
  rw [cobFb, toVec_foldOr (by norm_num) _ hlt, cobLin_apply, cobFun, unpackV_packV]
  ext1 i
  rw [toVec_xorN, toVec_actECode ε i.2 hv]
  rfl

theorem toMat_eq_zero_of_bIsZero {n m : ℕ} {X : Array ℕ} (h : bIsZero n X = true) :
    toMat n m X = 0 := by
  ext i j
  simp only [bIsZero, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [toMat_apply, h i i.2]
  simp [bz]

theorem foxECols_tr (ε : Eps) : btr 49 203 (foxECols ε) = linBits 49 203 (foxEb ε) := rfl

theorem toMat_fmMat (ε : Eps) (y : Fin (7 * nM ε) → ZMod 2) :
    toMat (29 * nM ε) (7 * nM ε) (fmMat ε) *ᵥ y = fmLin ε y :=
  toMat_linBits_mulVec (foxMb ε) (fmLin ε) (fun j => by rw [toVec_foxMb, toVec_two_pow]) y

theorem toMat_iotaMat (ε : Eps) (c : Fin 203 → ZMod 2) :
    toMat (29 * nM ε) 203 (iotaMat ε) *ᵥ c = ioLin ε c :=
  toMat_linBits_mulVec (iotaB ε) (ioLin ε) (fun j => by rw [toVec_iotaB, toVec_two_pow]) c

theorem toMat_foxE (ε : Eps) (e : Fin 49 → ZMod 2) :
    toMat 203 49 (linBits 49 203 (foxEb ε)) *ᵥ e = feLin ε e :=
  toMat_linBits_mulVec (foxEb ε) (feLin ε) (fun j => by rw [toVec_foxEb, toVec_two_pow]) e

theorem toMat_cob (ε : Eps) (x : Fin 7 → ZMod 2) :
    toMat 49 7 (linBits 7 49 (cobFb ε)) *ᵥ x = cobLin ε x :=
  toMat_linBits_mulVec (cobFb ε) (cobLin ε) (fun j => by
    have hj : 2 ^ (j : ℕ) < 128 := by
      have := j.2
      have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) this
      simpa using h
    rw [toVec_cobFb ε hj, toVec_two_pow]) x

@[expose] def relVec (c : List (Fin 7) → V7) : Fin 203 → ZMod 2 :=
  packV 29 7 fun j => c (rels7.getD j [])

theorem fox_split (ε : Eps) (m : Fin 7 → Fin (mOf ε) → V7) (c : List (Fin 7) → V7)
    (hm : ∀ w ∈ rels7, foxSum (aM ε) m w = fun _ => c w) :
    ∃ e : Fin 7 → V7, ∀ w ∈ rels7, foxSum (aE ε) e w = c w := by
  obtain ⟨Y, hc⟩ : ∃ Y : Array ℕ, splitTest ε (29 * nM ε) (fmMat ε) (iotaMat ε) Y = true := by
    cases ε; exact nsSplitCheck_plus; exact nsSplitCheck_minus
  rw [splitTest, Bool.and_eq_true] at hc
  obtain ⟨hz, hcert⟩ := hc
  have hY : toMat Y.size (29 * nM ε) Y * toMat (29 * nM ε) (7 * nM ε) (fmMat ε) = 0 := by
    rw [← toMat_bmul]; exact toMat_eq_zero_of_bIsZero hz
  let D : Fin (7 * nM ε) → ZMod 2 := packV 7 (nM ε) fun i => packV (mOf ε) 7 (m i)
  have hD : unpackD ε D = m := by
    ext1 i
    simp only [unpackD, D, unpackV_packV]
  have hmem : ∀ j : Fin 29, rels7.getD j [] ∈ rels7 := fun j => by
    rw [List.getD_eq_getElem _ _ (by rw [rels7_length]; exact j.2)]
    exact List.getElem_mem _
  have hFD : fmLin ε D = ioLin ε (relVec c) := by
    rw [fmLin_apply, fmFun, ioLin_apply, ioFun, hD]
    congr 1
    funext j
    rw [hm _ (hmem j)]
    funext g
    show c (rels7.getD j []) = unpackV 29 7 (packV 29 7 fun j => c (rels7.getD j [])) j
    rw [unpackV_packV]
  have hzero : toMat Y.size 203 (bmul Y.size (29 * nM ε) Y (iotaMat ε)) *ᵥ relVec c = 0 := by
    rw [toMat_bmul, ← mulVec_mulVec, toMat_iotaMat, ← hFD, ← toMat_fmMat, mulVec_mulVec, hY,
      zero_mulVec]
  obtain ⟨l, hl⟩ := exists_eq_mulVec_of_certCheck hcert hzero
  rw [← toMat_btr, foxECols_tr, toMat_foxE] at hl
  refine ⟨unpackV 7 7 l, fun w hw => ?_⟩
  obtain ⟨j, hj, rfl⟩ := mem_rels7 hw
  have := congrArg (fun y => unpackV 29 7 y ⟨j, hj⟩) hl
  simp only [relVec, feLin_apply, feFun] at this
  rw [unpackV_packV, unpackV_packV] at this
  exact this.symm

theorem fox_h1 (ε : Eps) (e : Fin 7 → V7) (he : ∀ w ∈ rels7, foxSum (aE ε) e w = 0) :
    ∃ x : V7, ∀ i, e i = aE ε i x + x := by
  have hc : nsH1Check ε = true := by
    cases ε; exact nsH1Check_plus; exact nsH1Check_minus
  rw [nsH1Check] at hc
  have hmem : ∀ j : Fin 29, rels7.getD j [] ∈ rels7 := fun j => by
    rw [List.getD_eq_getElem _ _ (by rw [rels7_length]; exact j.2)]
    exact List.getElem_mem _
  have hzero : toMat 203 49 (linBits 49 203 (foxEb ε)) *ᵥ packV 7 7 e = 0 := by
    rw [toMat_foxE, feLin_apply, feFun, unpackV_packV]
    have h0 : packV 29 7 (0 : Fin 29 → Fin 7 → ZMod 2) = 0 := rfl
    rw [← h0]
    congr 1
    funext j
    exact he _ (hmem j)
  obtain ⟨l, hl⟩ := exists_eq_mulVec_of_certCheck hc hzero
  have hcob : btr 7 49 (Array.ofFn (n := 7) fun b => cobCol ε b) = linBits 7 49 (cobFb ε) := rfl
  rw [← toMat_btr, hcob, toMat_cob, cobLin_apply, cobFun] at hl
  refine ⟨l, fun i => ?_⟩
  have := congrArg (fun y => unpackV 7 7 y i) hl
  simp only [unpackV_packV] at this
  exact this

end CFSG.EvenSmallLie.OmegaEight.NSplit
