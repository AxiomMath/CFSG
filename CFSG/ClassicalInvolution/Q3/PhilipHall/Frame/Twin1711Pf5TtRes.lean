module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Tt48Data
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Cov

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

set_option linter.unusedSectionVars false

@[expose] def embF (j : ℕ) : Fin 240 := ⟨embL.getD j 0 % 240, Nat.mod_lt _ (by norm_num)⟩

@[expose] def ResRep (p : ℕ) (x : Equiv.Perm (Fin 240)) : Prop :=
  p < 64 ^ 48 ∧ ∀ i : Fin 48, dg 64 p i < 48 ∧ x (embF i) = embF (dg 64 p i)

@[expose] def embChk : Bool :=
  (List.range 48).all fun i => decide (embL.getD i 0 < 240) &&
    (List.range 48).all fun j => decide (embL.getD i 0 = embL.getD j 0 → i = j)

theorem embChk_true : embChk = true := by decide +kernel

theorem embF_inj {i j : ℕ} (hi : i < 48) (hj : j < 48) (h : embF i = embF j) : i = j := by
  have h1 := List.all_eq_true.1 embChk_true i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  have h2 := (h1.2 j (List.mem_range.2 hj))
  apply h2
  have h3 := congrArg Fin.val h
  simp only [embF] at h3
  rw [Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt (by
    have := List.all_eq_true.1 embChk_true j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1)] at h3
  exact h3

theorem ResRep.comp {p q : ℕ} {x y : Equiv.Perm (Fin 240)} (hp : ResRep p x) (hq : ResRep q y) :
    ResRep (PkG.comp 64 48 p q) (x * y) := by
  refine ⟨compAux_lt (by norm_num) p q 48, fun i => ?_⟩
  have h1 := hq.2 i
  have h2 := hp.2 ⟨dg 64 q i, h1.1⟩
  rw [PkG.comp, dg_compAux (by norm_num) p q 48 i i.2]
  refine ⟨h2.1, ?_⟩
  rw [Equiv.Perm.mul_apply, h1.2]
  exact h2.2

theorem ResRep.one : ResRep (PkG.one 64 48) 1 := by
  refine ⟨oneAux_lt (by norm_num) 48 (by norm_num), fun i => ?_⟩
  rw [PkG.one, dg_oneAux (by norm_num) 48 i (by norm_num) i.2]
  exact ⟨i.2, rfl⟩

theorem ResRep.ne {p q : ℕ} {x y : Equiv.Perm (Fin 240)} (hp : ResRep p x) (hq : ResRep q y)
    (hpq : p ≠ q) : x ≠ y := by
  intro hxy
  apply hpq
  refine pack_inj (by norm_num) hp.1 hq.1 fun i hi => ?_
  have h1 := hp.2 ⟨i, hi⟩
  have h2 := hq.2 ⟨i, hi⟩
  rw [hxy] at h1
  exact embF_inj h1.1 h2.1 (h1.2.symm.trans h2.2)

theorem ResRep.digits_unique {p q : ℕ} {x : Equiv.Perm (Fin 240)} (hp : ResRep p x)
    (hq : ResRep q x) : p = q := by
  by_contra h
  exact hp.ne hq h rfl

@[expose] def invLit48 (p q : ℕ) : Bool :=
  (List.range 48).all fun i => decide (dg 64 q i < 48) && dg 64 p (dg 64 q i) == i

theorem ResRep.inv_of_lit {p q : ℕ} {x : Equiv.Perm (Fin 240)} (hq : q < 64 ^ 48)
    (hp : ResRep p x) (h : invLit48 p q = true) : ResRep q x⁻¹ := by
  refine ⟨hq, fun i => ?_⟩
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 i.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  refine ⟨h1.1, ?_⟩
  have h2 := (hp.2 ⟨dg 64 q i, h1.1⟩).2
  have h3 : x (embF (dg 64 q i)) = embF i := by
    rw [h2, h1.2]
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact h3.symm

section Cert

@[expose] noncomputable def CG (l : ℕ) : Equiv.Perm (Fin 240) :=
  if l < 3 then permOfArr 240 cA[l]! else if l < 6 then (permOfArr 240 cA[l - 3]!)⁻¹ else 1

theorem cA_mem (k : ℕ) (hk : k < 3) : cA[k]! ∈ cA.toList := by
  have : k < cA.size := by rw [cA_size]; exact hk
  rw [getElem!_pos cA k this]
  exact Array.getElem_mem_toList this

theorem CG_mem (l : ℕ) : CG l ∈ ySub := by
  unfold CG
  split_ifs with h1 h2
  · exact (c_data (cA_mem l h1)).2.2
  · exact ySub.inv_mem (c_data (cA_mem (l - 3) (by omega))).2.2
  · exact ySub.one_mem

theorem baseC_lt : ∀ k < 6, baseC.getD k (one 256 240) < 256 ^ 240 := by decide +kernel

theorem baseC0 : arrChk (baseC.getD 0 (one 256 240)) cA[0]! = true := by decide +kernel
theorem baseC1 : arrChk (baseC.getD 1 (one 256 240)) cA[1]! = true := by decide +kernel
theorem baseC2 : arrChk (baseC.getD 2 (one 256 240)) cA[2]! = true := by decide +kernel
theorem baseCI0 : invLitChk (baseC.getD 0 (one 256 240)) (baseC.getD 3 (one 256 240)) = true := by
  decide +kernel
theorem baseCI1 : invLitChk (baseC.getD 1 (one 256 240)) (baseC.getD 4 (one 256 240)) = true := by
  decide +kernel
theorem baseCI2 : invLitChk (baseC.getD 2 (one 256 240)) (baseC.getD 5 (one 256 240)) = true := by
  decide +kernel

theorem rep_c {k : ℕ} (hk : k < 3) {L : ℕ} (hL : L < 256 ^ 240) (h : arrChk L cA[k]! = true) :
    PkG.Rep 256 240 L (permOfArr 240 cA[k]!) :=
  rep_of_arrChk hL h (c_data (cA_mem k hk)).1

theorem prepC (l : ℕ) : PkG.Rep 256 240 (baseC.getD l (one 256 240)) (CG l) := by
  by_cases h1 : l < 3
  · have e : CG l = permOfArr 240 cA[l]! := by simp [CG, h1]
    rw [e]
    have h : arrChk (baseC.getD l (one 256 240)) cA[l]! = true := by
      have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
      rcases this with rfl | rfl | rfl
      exacts [baseC0, baseC1, baseC2]
    exact rep_c h1 (baseC_lt l (by omega)) h
  · by_cases h2 : l < 6
    · have e : CG l = (permOfArr 240 cA[l - 3]!)⁻¹ := by simp [CG, h1, h2]
      rw [e]
      have hp : arrChk (baseC.getD (l - 3) (one 256 240)) cA[l - 3]! = true := by
        have : l - 3 = 0 ∨ l - 3 = 1 ∨ l - 3 = 2 := by omega
        rcases this with h | h | h <;> rw [h]
        exacts [baseC0, baseC1, baseC2]
      have hi : invLitChk (baseC.getD (l - 3) (one 256 240)) (baseC.getD l (one 256 240)) = true := by
        have : l = 3 ∨ l = 4 ∨ l = 5 := by omega
        rcases this with rfl | rfl | rfl
        exacts [baseCI0, baseCI1, baseCI2]
      exact rep_inv_of_chk (baseC_lt l h2)
        (rep_c (k := l - 3) (by omega) (baseC_lt (l - 3) (by omega)) hp) hi
    · have e : CG l = 1 := by simp [CG, h1, h2]
      rw [e]
      have : baseC.getD l (one 256 240) = one 256 240 :=
        getD_default' _ _ _ (by simp [baseC]; omega)
      rw [this]
      exact PkG.Rep.one (by norm_num) (by norm_num)

@[expose] def resArrChk (p : ℕ) (a : Array ℕ) : Bool :=
  (List.range 48).all fun i => decide (dg 64 p i < 48) &&
    a[embL.getD i 0]! == embL.getD (dg 64 p i) 0

theorem res_of_arr {p : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin 240)} (hp : p < 64 ^ 48)
    (h : resArrChk p a = true) (hg : CFSG.Monster.B.Co2.Rep 240 a g) : ResRep p g := by
  refine ⟨hp, fun i => ?_⟩
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 i.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  refine ⟨h1.1, ?_⟩
  have hemb : embL.getD i 0 < 240 := by
    have := List.all_eq_true.1 embChk_true i (List.mem_range.2 i.2)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hemb' : embL.getD (dg 64 p i) 0 < 240 := by
    have := List.all_eq_true.1 embChk_true (dg 64 p i) (List.mem_range.2 h1.1)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  apply Fin.ext
  have h2 := hg (embF i)
  have e1 : (embF i : ℕ) = embL.getD i 0 := Nat.mod_eq_of_lt hemb
  rw [e1] at h2
  rw [← h2, h1.2]
  exact (Nat.mod_eq_of_lt hemb').symm

theorem base48_lt : ∀ k < 6, base48.getD k (one 64 48) < 64 ^ 48 := by decide +kernel

theorem res0 : resArrChk (base48.getD 0 (one 64 48)) cA[0]! = true := by decide +kernel
theorem res1 : resArrChk (base48.getD 1 (one 64 48)) cA[1]! = true := by decide +kernel
theorem res2 : resArrChk (base48.getD 2 (one 64 48)) cA[2]! = true := by decide +kernel
theorem resI0 : invLit48 (base48.getD 0 (one 64 48)) (base48.getD 3 (one 64 48)) = true := by
  decide +kernel
theorem resI1 : invLit48 (base48.getD 1 (one 64 48)) (base48.getD 4 (one 64 48)) = true := by
  decide +kernel
theorem resI2 : invLit48 (base48.getD 2 (one 64 48)) (base48.getD 5 (one 64 48)) = true := by
  decide +kernel

theorem resC (l : ℕ) : ResRep (base48.getD l (one 64 48)) (CG l) := by
  by_cases h1 : l < 3
  · have e : CG l = permOfArr 240 cA[l]! := by simp [CG, h1]
    rw [e]
    have h : resArrChk (base48.getD l (one 64 48)) cA[l]! = true := by
      have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
      rcases this with rfl | rfl | rfl
      exacts [res0, res1, res2]
    exact res_of_arr (base48_lt l (by omega)) h (c_data (cA_mem l h1)).1
  · by_cases h2 : l < 6
    · have e : CG l = (permOfArr 240 cA[l - 3]!)⁻¹ := by simp [CG, h1, h2]
      rw [e]
      have hp : resArrChk (base48.getD (l - 3) (one 64 48)) cA[l - 3]! = true := by
        have : l - 3 = 0 ∨ l - 3 = 1 ∨ l - 3 = 2 := by omega
        rcases this with h | h | h <;> rw [h]
        exacts [res0, res1, res2]
      have hi : invLit48 (base48.getD (l - 3) (one 64 48)) (base48.getD l (one 64 48)) = true := by
        have : l = 3 ∨ l = 4 ∨ l = 5 := by omega
        rcases this with rfl | rfl | rfl
        exacts [resI0, resI1, resI2]
      exact ResRep.inv_of_lit (base48_lt l h2)
        (res_of_arr (base48_lt (l - 3) (by omega)) hp (c_data (cA_mem (l - 3) (by omega))).1) hi
    · have e : CG l = 1 := by simp [CG, h1, h2]
      rw [e]
      have : base48.getD l (one 64 48) = one 64 48 :=
        getD_default' _ _ _ (by simp [base48]; omega)
      rw [this]
      exact ResRep.one

theorem resW : ∀ w : List ℕ, ResRep (evalW 64 48 base48 w) (permW CG w)
  | [] => by simpa [evalW, permW] using ResRep.one
  | l :: w => by
    have := (resC l).comp (resW w)
    simpa [evalW, permW_cons] using this

@[expose] noncomputable def GO (l : ℕ) : Equiv.Perm (Fin 240) :=
  if l < 6 then GBase l else CG (l - 6)

theorem baseD_eq : baseD = CovK.baseGl := by decide +kernel

theorem zpT_eq : zpT = CovK.zp := by decide +kernel

theorem baseO_lt : ∀ l, l < 6 → baseO.getD l (one 256 240) = CovK.baseGl.getD l (one 256 240) := by
  intro l hl
  unfold baseO
  rw [baseD_eq, List.getD_append _ _ _ _ (by simp [CovK.baseGl]; omega)]

theorem baseO_ge (l : ℕ) (hl : 6 ≤ l) : baseO.getD l (one 256 240) = baseC.getD (l - 6) (one 256 240) := by
  unfold baseO
  rw [baseD_eq, List.getD_append_right _ _ _ _ (by simp [CovK.baseGl]; omega)]
  simp [CovK.baseGl]

theorem prepO (l : ℕ) : PkG.Rep 256 240 (baseO.getD l (one 256 240)) (GO l) := by
  by_cases hl : l < 6
  · have e : GO l = GBase l := by simp [GO, hl]
    rw [e, baseO_lt l hl]
    exact CovK.prep_base l
  · have e : GO l = CG (l - 6) := by simp [GO, hl]
    rw [e, baseO_ge l (by omega)]
    exact prepC (l - 6)

@[expose] noncomputable def LGO : ℕ → Equiv.Perm (Fin 240) := LG lwO GO

theorem prepLO (l : ℕ) : PkG.Rep 256 240 (GLO.getD l (one 256 240)) (LGO l) := by
  have := prep_LG (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prepO lwO l
  rwa [GLO_eq] at this

theorem prepWO (w : List ℕ) : PkG.Rep 256 240 (evalW 256 240 GLO w) (permW LGO w) := by
  have := prep_permW (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prepO lwO w
  rwa [GLO_eq] at this

theorem invO_fix : ∀ l, 35 ≤ l → invO l = l := fun l hl => by
  unfold invO
  exact getD_default' _ _ _ (by simpa using hl)

theorem hIO : ∀ l, LGO (invO l) = (LGO l)⁻¹ := by
  refine LG_inv (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prepO lwO
    (invL := invO) 35 (by decide) invO_fix ?_
  intro l hl
  have h := List.all_eq_true.1 invChkO_true l (List.mem_range.2 hl)
  rw [beq_iff_eq] at h
  rw [GLO_eq]
  exact h

theorem LGO_mem (l : ℕ) : LGO l ∈ ySub := by
  show permW GO (lwO.getD l []) ∈ ySub
  refine permW_mem GO ?_ _
  intro l'
  unfold GO
  split_ifs
  · exact GBase_mem l'
  · exact CG_mem _

theorem permW_shift : ∀ w : List ℕ, (∀ l ∈ w, l < 6) → permW GO (w.map (· + 6)) = permW CG w
  | [], _ => rfl
  | l :: w, h => by
    simp only [List.map_cons, permW_cons]
    have h1 : GO (l + 6) = CG l := by
      have : ¬ (l + 6 < 6) := by omega
      simp [GO, this]
    rw [h1, permW_shift w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

theorem spW_lt : (spW.all fun w => w.all fun l => decide (l < 6)) = true := by decide +kernel

theorem spW_lt' {w : List ℕ} (hw : w ∈ spW) : ∀ l ∈ w, l < 6 := by
  have := List.all_eq_true.1 spW_lt w hw
  intro l hl
  simpa using List.all_eq_true.1 this l hl

theorem spW_get_mem {k : ℕ} (hk : k < spW.length) : spW.getD k [] ∈ spW := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem lwO_sp : [lwO.getD 12 [], lwO.getD 13 [], lwO.getD 14 [], lwO.getD 15 [], lwO.getD 16 [],
    lwO.getD 17 [], lwO.getD 18 [], lwO.getD 19 [], lwO.getD 20 [], lwO.getD 22 []] =
    ([spW.getD 0 [], spW.getD 1 [], spW.getD 2 [], spW.getD 3 [], spW.getD 4 [], spW.getD 5 [],
      spW.getD 6 [], spW.getD 7 [], spW.getD 8 [], spW.getD 10 []]).map (List.map (· + 6)) := by
  decide +kernel

theorem LGO_cw {l : ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x < 6) (h : lwO.getD l [] = w.map (· + 6)) :
    LGO l = permW CG w := by
  show permW GO (lwO.getD l []) = _
  rw [h, permW_shift w hw]

theorem permW_inv6 : ∀ w : List ℕ, (∀ l ∈ w, l < 6) →
    permW CG (invW6 w) = (permW CG w)⁻¹ := by
  intro w hw
  unfold invW6 permW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  have hl6 := hw l hl
  simp only [Function.comp]
  unfold CG
  have : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem arrT : arrChk (GLO.getD 12 (one 256 240)) tA = true := by decide +kernel
theorem arrI : arrChk (GLO.getD 13 (one 256 240)) iA = true := by decide +kernel
theorem arrJ : arrChk (GLO.getD 15 (one 256 240)) jA = true := by decide +kernel

theorem LGO_12 : LGO 12 = Sp6Cover.tP := by
  have h1 : PkG.Rep 256 240 (GLO.getD 12 (one 256 240)) Sp6Cover.tP :=
    rep_of_arrChk (by decide +kernel) arrT t_data.1
  exact PkG.Rep.unique (prepLO 12) h1

theorem LGO_13 : LGO 13 = Sp6Cover.iP := by
  have h1 : PkG.Rep 256 240 (GLO.getD 13 (one 256 240)) Sp6Cover.iP :=
    rep_of_arrChk (by decide +kernel) arrI i_data.1
  exact PkG.Rep.unique (prepLO 13) h1

theorem LGO_15 : LGO 15 = Sp6Cover.jP := by
  have h1 : PkG.Rep 256 240 (GLO.getD 15 (one 256 240)) Sp6Cover.jP :=
    rep_of_arrChk (by decide +kernel) arrJ j_data.1
  exact PkG.Rep.unique (prepLO 15) h1

@[expose] noncomputable def eP : Equiv.Perm (Fin 240) := LGO 23

theorem LGO_21 : LGO 21 = LGl 12 := by
  have h := conjChkO_true
  simp only [conjChkO, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : PkG.Rep 256 240 (GLO.getD 21 (one 256 240)) (LGl 12) := by
    have := prepL 12
    have e : GLt.getD 12 (one 256 240) = CovK.zp := rfl
    rw [e] at this
    rw [h.2, zpT_eq]
    exact this
  exact PkG.Rep.unique (prepLO 21) h1

theorem LGO_17 : LGO 17 = eP * LGO 13 * eP⁻¹ := by
  have h := conjChkO_true
  simp only [conjChkO, Bool.and_eq_true, beq_iff_eq] at h
  have a := (((prepLO 23).comp (by norm_num : 0 < 256) (prepLO 13)).comp (by norm_num : 0 < 256)
    (prepLO 24))
  rw [h.1.1.1.1] at a
  have e : LGO 24 = (LGO 23)⁻¹ := by
    have := hIO 23
    exact this
  rw [e] at a
  exact (PkG.Rep.unique a (prepLO 17)).symm

theorem LGO_19 : LGO 19 = eP * LGO 15 * eP⁻¹ := by
  have h := conjChkO_true
  simp only [conjChkO, Bool.and_eq_true, beq_iff_eq] at h
  have a := (((prepLO 23).comp (by norm_num : 0 < 256) (prepLO 15)).comp (by norm_num : 0 < 256)
    (prepLO 24))
  rw [h.1.1.1.2] at a
  have e : LGO 24 = (LGO 23)⁻¹ := hIO 23
  rw [e] at a
  exact (PkG.Rep.unique a (prepLO 19)).symm

theorem LGO_22 : LGO 22 = LGO 12 * LGO 21 := by
  have h := conjChkO_true
  simp only [conjChkO, Bool.and_eq_true, beq_iff_eq] at h
  have a := (prepLO 12).comp (by norm_num : 0 < 256) (prepLO 21)
  rw [← h.1.1.2] at a
  exact (PkG.Rep.unique a (prepLO 22)).symm

theorem LGO_etz : eP * LGO 12 * eP⁻¹ = LGO 22 := by
  have h := conjChkO_true
  simp only [conjChkO, Bool.and_eq_true, beq_iff_eq] at h
  have a := (((prepLO 23).comp (by norm_num : 0 < 256) (prepLO 12)).comp (by norm_num : 0 < 256)
    (prepLO 24))
  rw [h.1.2] at a
  have e : LGO 24 = (LGO 23)⁻¹ := hIO 23
  rw [e] at a
  exact PkG.Rep.unique a (prepLO 22)

theorem lwO_base : ∀ l, l < 12 → lwO.getD l [] = [l] := by decide +kernel

theorem LGO_base {l : ℕ} (hl : l < 12) : LGO l = GO l := by
  show permW GO (lwO.getD l []) = _
  rw [lwO_base l hl, permW_single]

theorem CG_comm_t (l : ℕ) : CG l * Sp6Cover.tP = Sp6Cover.tP * CG l := by
  by_cases h3 : l < 3
  · have hk := cCommChk_true
    have h := List.all_eq_true.1 hk l (List.mem_range.2 h3)
    rw [beq_iff_eq] at h
    have a := (prepLO (6 + l)).comp (by norm_num : 0 < 256) (prepLO 12)
    have b := (prepLO 12).comp (by norm_num : 0 < 256) (prepLO (6 + l))
    rw [h] at a
    have := PkG.Rep.unique a b
    rw [LGO_base (by omega), LGO_12] at this
    have e : GO (6 + l) = CG l := by
      have : ¬ (6 + l < 6) := by omega
      simp [GO, this]
    rw [e] at this
    exact this
  · by_cases h6 : l < 6
    · have e : CG l = (CG (l - 3))⁻¹ := by
        have h1 : ¬ l < 3 := h3
        have : CG l = (permOfArr 240 cA[l - 3]!)⁻¹ := by simp [CG, h1, h6]
        rw [this]
        have h2 : CG (l - 3) = permOfArr 240 cA[l - 3]! := by
          have : l - 3 < 3 := by omega
          simp [CG, this]
        rw [h2]
      rw [e]
      have := CG_comm_t' (l - 3) (by omega)
      exact (Commute.inv_left this).eq
    · have e : CG l = 1 := by simp [CG, h3, h6]
      rw [e]
      simp
where
  CG_comm_t' (l : ℕ) (h3 : l < 3) : Commute (CG l) Sp6Cover.tP := by
    have hk := cCommChk_true
    have h := List.all_eq_true.1 hk l (List.mem_range.2 h3)
    rw [beq_iff_eq] at h
    have a := (prepLO (6 + l)).comp (by norm_num : 0 < 256) (prepLO 12)
    have b := (prepLO 12).comp (by norm_num : 0 < 256) (prepLO (6 + l))
    rw [h] at a
    have := PkG.Rep.unique a b
    rw [LGO_base (by omega), LGO_12] at this
    have e : GO (6 + l) = CG l := by
      have : ¬ (6 + l < 6) := by omega
      simp [GO, this]
    rw [e] at this
    exact this

theorem permW_shiftL : ∀ w : List ℕ, (∀ l ∈ w, l < 6) → permW LGO (w.map (· + 6)) = permW CG w
  | [], _ => rfl
  | l :: w, h => by
    simp only [List.map_cons, permW_cons]
    have h1 : LGO (l + 6) = CG l := by
      rw [LGO_base (by have := h l (List.mem_cons_self ..); omega)]
      have : ¬ (l + 6 < 6) := by omega
      simp [GO, this]
    rw [h1, permW_shiftL w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
