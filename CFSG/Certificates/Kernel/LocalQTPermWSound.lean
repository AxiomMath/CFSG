module

public import CFSG.Certificates.Kernel.LocalQTPairsHSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2CheckInputs
import CFSG.Certificates.Kernel.LocalQTPermWSnd.Tree

public section

namespace CFSG.KC.LQT.PW

open Equiv CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
  CFSG.ComponentClassification.J2Cover
open scoped Pointwise

@[expose] def cJ (x : XJ) : ℕ := ((List.finRange 315).map fun i => ((x : Perm (Fin 315)) i : ℕ) *
  2 ^ (9 * (i : ℕ))).sum

def valsJ (x : XJ) (i : ℕ) : ℕ := if h : i < 315 then ((x : Perm (Fin 315)) ⟨i, h⟩ : ℕ) else 0

theorem valsJ_lt (x : XJ) (i : ℕ) : valsJ x i < 315 := by
  unfold valsJ
  split_ifs
  · exact Fin.isLt _
  · norm_num

theorem cJ_eq_sumW (x : XJ) : cJ x = sumW 9 (valsJ x) 315 := by
  rw [cJ, ← Fin.sum_univ_def, sumW, ← Fin.sum_univ_eq_sum_range (fun i => valsJ x i * 2 ^ (9 * i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [valsJ, i.isLt]

theorem imgW_cJ (x : XJ) (k : ℕ) : imgW 9 (cJ x) k = valsJ x k := by
  rw [cJ_eq_sumW, imgW_sumW (fun i _ => Nat.lt_trans (valsJ_lt x i) (by norm_num))]
  split_ifs with hk
  · rfl
  · simp [valsJ, hk]

theorem imgW_cJ_fin (x : XJ) (i : Fin 315) : imgW 9 (cJ x) i = ((x : Perm (Fin 315)) i : ℕ) := by
  rw [imgW_cJ]
  simp [valsJ, i.isLt]

theorem cJ_ext {x : XJ} {c : ℕ} (h : ∀ k, imgW 9 c k = valsJ x k) : cJ x = c :=
  eq_of_imgW (w := 9) (by norm_num) fun k => by rw [imgW_cJ, h]

theorem lt512 {a : ℕ} (h : a < 315) : a < 2 ^ 9 := Nat.lt_trans h (by norm_num)

theorem pAI (σ : Perm (Fin 315)) (k : Fin 315) : σ (σ⁻¹ k) = k := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem pIA (σ : Perm (Fin 315)) (k : Fin 315) : σ⁻¹ (σ k) = k := by
  rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]

theorem cJ_mul (x y : XJ) : cJ (x * y) = mulW 315 9 (cJ x) (cJ y) := by
  refine cJ_ext fun k => ?_
  rw [mulW, ofFnW_eq]
  by_cases hk : k < 315
  · rw [imgW_orW_of (fun i _ => imgW_lt _ _ _) (fun i _ j _ h => h) hk rfl]
    have e : imgW 9 (cJ y) k = (((y : Perm (Fin 315)) ⟨k, hk⟩ : Fin 315) : ℕ) :=
      imgW_cJ_fin y ⟨k, hk⟩
    rw [e, imgW_cJ_fin]
    simp [valsJ, hk]
  · rw [imgW_orW_none (fun i _ => imgW_lt _ _ _) (fun i hi h => hk (by omega))]
    simp [valsJ, hk]

theorem cJ_one : cJ 1 = oneW 315 9 := by
  refine cJ_ext fun k => ?_
  rw [oneW, ofFnW_eq]
  by_cases hk : k < 315
  · rw [imgW_orW_of (fun i hi => lt512 hi) (fun i _ j _ h => h) hk rfl]
    simp [valsJ, hk]
  · rw [imgW_orW_none (fun i hi => lt512 hi) (fun i hi h => hk (by omega))]
    simp [valsJ, hk]

theorem cJ_inv (x : XJ) : cJ x⁻¹ = invW 315 9 (cJ x) := by
  refine cJ_ext fun k => ?_
  rw [invW_eq]
  have hp : ∀ i < 315, ∀ j < 315, imgW 9 (cJ x) i = imgW 9 (cJ x) j → i = j := by
    intro i hi j hj h
    rw [imgW_cJ_fin x ⟨i, hi⟩, imgW_cJ_fin x ⟨j, hj⟩] at h
    have := (x : Perm (Fin 315)).injective (Fin.ext h)
    exact congrArg Fin.val this
  by_cases hk : k < 315
  · set i : Fin 315 := ((x : Perm (Fin 315))⁻¹ ⟨k, hk⟩) with hi
    have hpk : imgW 9 (cJ x) i = k := by
      rw [imgW_cJ_fin, hi, pAI]
    rw [imgW_orW_of (fun i hi => lt512 hi) hp i.isLt hpk]
    simp [valsJ, hk, hi]
  · have hn : ∀ i < 315, imgW 9 (cJ x) i ≠ k := fun i hi h => by
      rw [imgW_cJ_fin x ⟨i, hi⟩] at h
      exact hk (h ▸ Fin.isLt _)
    rw [imgW_orW_none (fun i hi => lt512 hi) hn]
    simp [valsJ, hk]

theorem cJ_injective : Function.Injective cJ := by
  intro x y h
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  rw [← imgW_cJ_fin, ← imgW_cJ_fin, h]

theorem enc_cJ (x : XJ) : enc x = encW 315 9 (cJ x) := by
  rw [encW_eq, enc, encPerm]
  congr 1
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  rw [imgW_cJ]
  simp only [List.length_map, List.length_range] at h2
  simp [valsJ, h2]

theorem cJ_permC (t r : Array ℕ) (h : PermArrOK t r) (hs : t.size = 315) (x : XJ)
    (hx : (x : Perm (Fin 315)) = permC t r h) : cJ x = arrCodeW 9 t.toList := by
  refine cJ_ext fun k => ?_
  have ht : ∀ v ∈ t.toList, v < 2 ^ 9 := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    rw [Array.length_toList, hs] at hj
    have := (h ⟨j, hj⟩).1
    rw [getElem!_pos t j (by rw [hs]; exact hj)] at this
    exact lt512 (by simpa using this)
  rw [imgW_arrCodeW ht]
  by_cases hk : k < 315
  · simp only [valsJ, hk, dite_true, hx, permC, Equiv.coe_fn_mk]
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem (by omega),
      Option.getD_some, getElem!_pos t k (by omega)]
  · simp only [valsJ, hk, dite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]

set_option maxRecDepth 100000 in
theorem cJ_paC : cJ paC = arrCodeW 9 (autStrong[0]!).toList :=
  cJ_permC _ _ permAc_ok (by decide +kernel) paC rfl

set_option maxRecDepth 100000 in
theorem cJ_pbC : cJ pbC = arrCodeW 9 (autStrong[1]!).toList :=
  cJ_permC _ _ permBc_ok (by decide +kernel) pbC rfl

theorem genW_map (S : List XJ) (i : ℕ) : genW 315 9 (S.map cJ) i = cJ (S.getD i 1) := by
  induction S generalizing i with
  | nil => exact cJ_one.symm
  | cons g S ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change genW 315 9 (S.map cJ) (Nat.sub (i + 1) 1) = _
      rw [List.getD_cons_succ]
      exact ih i

theorem letW_map (S : List XJ) (z : ℤ) : letW 315 9 (S.map cJ) z =
    cJ (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) := by
  rcases z with (_ | k) | k
  · change invW 315 9 (genW 315 9 (S.map cJ) 0) = _
    rw [genW_map, ← cJ_inv]
    rfl
  · change genW 315 9 (S.map cJ) k = _
    rw [genW_map]
    congr 1
    have h0 : (0 : ℤ) < Int.ofNat (k + 1) := Int.ofNat_lt.2 (Nat.succ_pos k)
    rw [ite_eq_left h0]
    simp
  · change invW 315 9 (genW 315 9 (S.map cJ) k) = _
    rw [genW_map, ← cJ_inv]
    congr 1

theorem cJ_evalW (S : List XJ) (w : List ℤ) : cJ (evalW S w) = evalZW 315 9 (S.map cJ) w := by
  induction w with
  | nil => exact cJ_one
  | cons z w ih =>
    change _ = mulW 315 9 (letW 315 9 (S.map cJ) z) (evalZW 315 9 (S.map cJ) w)
    rw [evalW, cJ_mul, ih, letW_map]

def indS (S : Finset (Fin 315)) (i : ℕ) : ℕ :=
  if h : i < 315 then (if (⟨i, h⟩ : Fin 315) ∈ S then 1 else 0) else 0

theorem indS_lt (S : Finset (Fin 315)) (i : ℕ) : indS S i < 2 ^ 1 := by
  unfold indS
  split_ifs <;> norm_num

theorem maskF_eq (S : Finset (Fin 315)) : maskF S = sumW 1 (indS S) 315 := by
  rw [maskF, sumW, ← Fin.sum_univ_eq_sum_range (fun i => indS S i * 2 ^ (1 * i)),
    ← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [indS, hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [indS, i.isLt, hi]

theorem imgW_maskF (S : Finset (Fin 315)) (k : ℕ) : imgW 1 (maskF S) k = indS S k := by
  rw [maskF_eq, imgW_sumW (fun i _ => indS_lt S i)]
  split_ifs with hk
  · rfl
  · simp [indS, hk]

theorem testBit_maskF (S : Finset (Fin 315)) (i : Fin 315) :
    (maskF S).testBit i = decide (i ∈ S) := by
  have h := testBit_imgW 1 (maskF S) i 0
  rw [imgW_maskF, Nat.one_mul, Nat.add_zero] at h
  have h2 : (maskF S).testBit i = (indS S i).testBit 0 := by
    rw [h]
    simp
  rw [h2]
  simp only [indS, i.isLt, dite_true, Fin.eta]
  split_ifs with hi <;> simp [hi]

theorem boolRec_eq (b : Bool) : Bool.rec (motive := fun _ => ℕ) 0 1 b = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem fix_mask (L : List XJ) {LC : List ℕ} (hL : (L.map cJ).Perm LC) :
    maskF (fixSetL L) = fixMaskW 315 9 LC := by
  apply eq_of_imgW (w := 1) (by norm_num)
  intro k
  rw [imgW_maskF, fixMaskW_eq]
  by_cases hk : k < 315
  · rw [imgW_orW_of (fun i _ => boolRec_lt _) (fun i _ j _ h => h) hk rfl, boolRec_eq]
    have key : CFSG.KC.LQT.P.allL LC (fun a => Nat.beq (imgW 9 a k) k) = true ↔
        (⟨k, hk⟩ : Fin 315) ∈ fixSetL L := by
      rw [CFSG.KC.LQT.P.allL_iff, mem_fixSetL]
      constructor
      · intro hA a ha
        have := Nat.eq_of_beq_eq_true (hA _ (hL.mem_iff.1 (List.mem_map_of_mem ha)))
        rw [imgW_cJ_fin a ⟨k, hk⟩] at this
        exact Fin.ext this
      · intro hA c hc
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (hL.mem_iff.2 hc)
        rw [imgW_cJ_fin a ⟨k, hk⟩]
        exact Nat.beq_eq_true_eq _ _ ▸ congrArg Fin.val (hA a ha)
    simp only [indS, hk, dite_true]
    by_cases hm : (⟨k, hk⟩ : Fin 315) ∈ fixSetL L
    · rw [if_pos hm, if_pos (key.2 hm)]
    · rw [if_neg hm, if_neg (fun h => hm (key.1 h))]
  · rw [imgW_orW_none (fun i _ => boolRec_lt _) (fun i hi h => hk (by omega))]
    simp [indS, hk]

theorem smul_mask (x : XJ) (S : Finset (Fin 315))
    (h : imgMaskW 315 9 (cJ x) (maskF S) = maskF S) : x • S = S := by
  have hp : ∀ i < 315, ∀ j < 315, imgW 9 (cJ x) i = imgW 9 (cJ x) j → i = j := by
    intro i hi j hj e
    rw [imgW_cJ_fin x ⟨i, hi⟩, imgW_cJ_fin x ⟨j, hj⟩] at e
    exact congrArg Fin.val ((x : Perm (Fin 315)).injective (Fin.ext e))
  have key : ∀ k : Fin 315, k ∈ S ↔ ((x : Perm (Fin 315))⁻¹ k) ∈ S := by
    intro k
    set i : Fin 315 := (x : Perm (Fin 315))⁻¹ k with hi
    have hpk : imgW 9 (cJ x) i = k := by rw [imgW_cJ_fin, hi, pAI]
    have e := congrArg (fun c => imgW 1 c k) h
    rw [imgMaskW_eq, imgW_orW_of (fun j _ => boolRec_lt _) hp i.isLt hpk, imgW_maskF] at e
    simp only [boolRec_eq, testBit_maskF, indS, k.isLt, dite_true, Fin.eta] at e
    by_cases h1 : k ∈ S <;> by_cases h2 : i ∈ S <;> simp [h1, h2] at e ⊢
  ext k
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [key]
    have : (x : Perm (Fin 315))⁻¹ (x • j) = j := by
      change (x : Perm (Fin 315))⁻¹ ((x : Perm (Fin 315)) j) = j
      exact pIA _ _
    rwa [this]
  · intro hk
    refine ⟨(x : Perm (Fin 315))⁻¹ k, (key k).1 hk, ?_⟩
    change (x : Perm (Fin 315)) ((x : Perm (Fin 315))⁻¹ k) = k
    exact pAI _ _

private theorem mem_smul_iff_inv (g : XJ) (T : Finset (Fin 315)) (i : Fin 315) :
    i ∈ g • T ↔ (g : Perm (Fin 315))⁻¹ i ∈ T := by
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have e : (g : Perm (Fin 315))⁻¹ (g • j) = j := by
      change (g : Perm (Fin 315))⁻¹ ((g : Perm (Fin 315)) j) = j
      exact pIA _ _
    rwa [e]
  · intro hi
    refine ⟨(g : Perm (Fin 315))⁻¹ i, hi, ?_⟩
    change (g : Perm (Fin 315)) ((g : Perm (Fin 315))⁻¹ i) = i
    exact pAI _ _

private theorem imgMaskW_cJ_maskF (g : XJ) (T : Finset (Fin 315)) :
    imgMaskW 315 9 (cJ g) (maskF T) = maskF (g • T) := by
  have hp : ∀ i < 315, ∀ j < 315, imgW 9 (cJ g) i = imgW 9 (cJ g) j → i = j := by
    intro i hi j hj e
    rw [imgW_cJ_fin g ⟨i, hi⟩, imgW_cJ_fin g ⟨j, hj⟩] at e
    exact congrArg Fin.val ((g : Perm (Fin 315)).injective (Fin.ext e))
  have hlt : ∀ i < 315, imgW 9 (cJ g) i < 315 := fun i hi =>
    lt_of_eq_of_lt (imgW_cJ_fin g ⟨i, hi⟩) ((g : Perm (Fin 315)) ⟨i, hi⟩).isLt
  apply eq_of_imgW (w := 1) (by norm_num)
  intro k
  rw [imgW_maskF, imgMaskW_eq]
  by_cases hk : k < 315
  · have hpk : imgW 9 (cJ g) (((g : Perm (Fin 315))⁻¹ ⟨k, hk⟩ : Fin 315) : ℕ) = k := by
      rw [imgW_cJ_fin, pAI] <;> rfl
    rw [imgW_orW_of (fun i _ => boolRec_lt ((maskF T).testBit i)) hp
      ((g : Perm (Fin 315))⁻¹ ⟨k, hk⟩).isLt hpk]
    simp only [boolRec_eq, testBit_maskF, indS, hk, dite_true, decide_eq_true_eq,
      mem_smul_iff_inv]
  · have hnone : ∀ i < 315, imgW 9 (cJ g) i ≠ k := fun i hi h => by
      have := hlt i hi
      omega
    rw [imgW_orW_none (fun i _ => boolRec_lt ((maskF T).testBit i)) hnone]
    simp [indS, hk]

private theorem maskF_inj_J2 : Function.Injective maskF := fun _ _ h => sum_two_pow_inj h

private theorem hkey_eq_hkW (x : XJ) : hkey x = hkW 315 9 (cJ x) := by
  unfold hkey hkW
  rw [enc_cJ]
  generalize encW 315 9 (cJ x) = n
  rfl

open CFSG.KC.LQT.Syl in
private theorem mem_dropLt {x y : ℕ} : ∀ {ys : List ℕ}, y ∈ dropLt x ys → y ∈ ys
  | [], h => h
  | z :: ys, h => by
    change y ∈ Bool.rec (motive := fun _ => List ℕ) (List.cons z ys) (dropLt x ys)
      (Nat.blt z x) at h
    revert h
    cases Nat.blt z x
    · exact id
    · exact fun h => List.mem_cons_of_mem _ (mem_dropLt h)

open CFSG.KC.LQT.Syl in
private theorem diffS_mem : ∀ (xs ys : List ℕ) {x : ℕ}, x ∈ xs → x ∉ diffS xs ys → x ∈ ys
  | [], _, _, hx, _ => absurd hx List.not_mem_nil
  | z :: xs, ys, x, hx, hn => by
    change x ∉ Bool.rec (motive := fun _ => List ℕ) (List.cons z (diffS xs (dropLt z ys)))
      (diffS xs (dropLt z ys))
      (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)) at hn
    have hz : z ∉ Bool.rec (motive := fun _ => List ℕ) (List.cons z (diffS xs (dropLt z ys)))
        (diffS xs (dropLt z ys))
        (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)) →
        z ∈ ys := by
      intro hz
      cases hd : dropLt z ys with
      | nil =>
        rw [hd] at hz
        exact absurd List.mem_cons_self hz
      | cons y t =>
        rw [hd] at hz
        change z ∉ Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq y z) at hz
        cases hb : Nat.beq y z
        · rw [hb] at hz
          exact absurd List.mem_cons_self hz
        · have : y ∈ dropLt z ys := by rw [hd]; exact List.mem_cons_self
          rw [Nat.eq_of_beq_eq_true hb] at this
          exact mem_dropLt this
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hz hn
    · have hn' : x ∉ diffS xs (dropLt z ys) := by
        intro h
        apply hn
        cases List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)
        · exact List.mem_cons_of_mem _ h
        · exact h
      exact mem_dropLt (diffS_mem xs (dropLt z ys) hx' hn')

private theorem nilK_nil {l : List ℕ} (h : nilK l = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t =>
    have e : nilK (a :: t) = false := rfl
    rw [e] at h
    exact absurd h (by decide)

theorem closedS_sound {g : ℕ} {E : List ℕ} {s k : ℕ} (h : closedS g E s k = true) :
    ∀ x ∈ List.take k (List.drop s E), mulW 315 9 g x ∈ E := by
  intro x hx
  have hnil := nilK_nil h
  have hm : mulW 315 9 g x ∈ CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
      (List.map (fun x => mulW 315 9 g x) (List.take k (List.drop s E)))) :=
    CFSG.KC.LQT.PH.mem_dedupS_sortN.2 (List.mem_map_of_mem hx)
  have := diffS_mem _ _ hm (by rw [hnil]; exact List.not_mem_nil)
  exact (CFSG.KC.LQT.PH.sortN_perm E).mem_iff.1 this

theorem closedE_sound {G E : List ℕ} (h : closedE G E = true) :
    ∀ g ∈ G, ∀ x ∈ E, mulW 315 9 g x ∈ E := by
  intro g hg x hx
  have h1 : closedG g E = true := (CFSG.KC.LQT.P.allL_iff G _).1 h g hg
  have h2 : closedS g E 0 E.length = true := by
    unfold closedS
    rw [List.drop_zero, List.take_length]
    exact h1
  exact closedS_sound h2 x (by simpa using hx)

private theorem closedM_sound {G E : List ℕ} (h : closedM G E = true) :
    ∀ g ∈ G, ∀ m ∈ E, imgMaskW 315 9 g m ∈ E := by
  intro g hg m hm
  have hnil := nilK_nil h
  have hmem : imgMaskW 315 9 g m ∈ CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
      (List.flatten (List.map (fun m => List.map (fun g => imgMaskW 315 9 g m) G) E))) :=
    CFSG.KC.LQT.PH.mem_dedupS_sortN.2
      (List.mem_flatten.2 ⟨_, List.mem_map_of_mem hm, List.mem_map_of_mem hg⟩)
  have := diffS_mem _ _ hmem (by rw [hnil]; exact List.not_mem_nil)
  exact (CFSG.KC.LQT.PH.sortN_perm E).mem_iff.1 this

private theorem lenA_eq_length {α : Type} (l : List α) : CFSG.KC.LQT.L.lenA l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : CFSG.KC.LQT.L.lenA (x :: t) = CFSG.KC.LQT.L.lenA t + 1 := rfl
    rw [e, ih]
    rfl

theorem grp_sound (gens : List XJ) {G : List ℕ} (hG : gens.map cJ = G) (P : List ℕ) (fuel : ℕ)
    (h1 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK P) = true)
    (h2 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (grpE G P)) = true)
    (h3 : ∀ g ∈ G, ∀ x ∈ grpE G P, mulW 315 9 g x ∈ grpE G P) (h4 : depthOK G P fuel = true)
    (h5 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) (grpE G P))) = true) :
    (closureListH tabX hkey gens fuel).Nodup ∧
      ((closureListH tabX hkey gens fuel).map cJ).Perm (grpE G P) ∧
      ∀ x, x ∈ closureListH tabX hkey gens fuel ↔ x ∈ Subgroup.closure {g | g ∈ gens} := by
  subst hG
  set par := CFSG.KC.LQT.Syl.pairUpK P with hpar
  set T : List XJ := CFSG.KC.LQT.PWSnd.bfsT (fun (x g : XJ) => g * x) 1 gens 1 par with hT
  have hdef : ∀ q ∈ par, (gens.map cJ).getD q.2 (oneW 315 9) = cJ (gens.getD q.2 1) := by
    intro q _
    rw [← cJ_one]
    exact List.getD_map gens 1 cJ
  have hE : grpE (gens.map cJ) P = T.map cJ := by
    have e1 : grpE (gens.map cJ) P = CFSG.KC.LQT.PWSnd.bfsT (fun x g => mulW 315 9 g x)
        (oneW 315 9) (gens.map cJ) (oneW 315 9) par :=
      CFSG.KC.LQT.T2.bfsQ_eq _ _ _ _ _ h1
    have e2 := CFSG.KC.LQT.PWSnd.bfsT_map cJ cJ (fun (x g : XJ) => g * x)
      (fun x g => mulW 315 9 g x) (fun x g => cJ_mul g x) 1 (oneW 315 9) gens 1 par hdef
    rw [e1, hT, e2, cJ_one]
  have hnd : (T.map cJ).Nodup := by
    rw [← hE]
    exact (CFSG.KC.LQT.PH.sortN_perm _).nodup_iff.1 (CFSG.KC.LQT.PH.sincK_nodup h2)
  have h1T : (1 : XJ) ∈ T := CFSG.KC.LQT.PWSnd.start_mem_bfsT _ _ _ _ _
  have hclT : ∀ g ∈ gens, ∀ x ∈ T, g * x ∈ T := by
    intro g hg x hx
    have hx' : cJ x ∈ grpE (gens.map cJ) P := by rw [hE]; exact List.mem_map_of_mem hx
    have hm := h3 (cJ g) (List.mem_map_of_mem hg) (cJ x) hx'
    rw [hE, ← cJ_mul] at hm
    obtain ⟨y, hy, hyc⟩ := List.mem_map.1 hm
    rw [cJ_injective hyc] at hy
    exact hy
  have hD : ∀ k ∈ CFSG.KC.LQT.PWSnd.bfsT (fun (n : ℕ) (_ : ℕ) => n + 1) 0 (gens.map cJ) 0 par,
      k ≤ fuel := by
    have e : CFSG.KC.LQT.T2.bfsQ (fun x _ => Nat.succ x) 0 (gens.map cJ) 0 par =
        CFSG.KC.LQT.PWSnd.bfsT (fun (n : ℕ) (_ : ℕ) => n + 1) 0 (gens.map cJ) 0 par :=
      CFSG.KC.LQT.T2.bfsQ_eq _ _ _ _ _ h1
    unfold depthOK at h4
    rw [CFSG.KC.LQT.P.allL_iff] at h4
    intro k hk
    have := h4 k (by rw [e]; exact hk)
    rw [Nat.ble_eq] at this
    exact this
  have hTball : ∀ y ∈ T, y ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel :=
    CFSG.KC.LQT.PWSnd.bfsT_subset_ball gens (gens.map cJ) 0 par fuel hD
  have hBT : ∀ y, y ∈ CFSG.KC.LQT.PWSnd.Ball gens fuel ↔ y ∈ T := fun y =>
    ⟨fun hy => CFSG.KC.LQT.PWSnd.ball_subset_of_closed gens {x | x ∈ T} h1T hclT fuel hy,
      hTball y⟩
  have hkinj : ∀ x ∈ T, ∀ y ∈ T, hkey x = hkey y → x = y := by
    have hh : ((T.map cJ).map (hkW 315 9)).Nodup := by
      rw [← hE]
      exact (CFSG.KC.LQT.PH.sortN_perm _).nodup_iff.1 (CFSG.KC.LQT.PH.sincK_nodup h5)
    intro x hx y hy e
    have e' : hkW 315 9 (cJ x) = hkW 315 9 (cJ y) :=
      (hkey_eq_hkW x).symm.trans (e.trans (hkey_eq_hkW y))
    exact cJ_injective (List.inj_on_of_nodup_map hh (List.mem_map_of_mem hx)
      (List.mem_map_of_mem hy) e')
  obtain ⟨hnd', hmem⟩ := CFSG.KC.LQT.PWSnd.closureListH_spec tabX tabX_eq hkey gens fuel
    (fun x hx y hy e => hkinj x ((hBT x).1 hx) y ((hBT y).1 hy) e)
  refine ⟨hnd', ?_, ?_⟩
  · rw [hE]
    refine (List.perm_ext_iff_of_nodup (hnd'.map cJ_injective) hnd).2 fun c => ?_
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hBT y).1 ((hmem y).1 hy), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hmem y).2 ((hBT y).2 hy), rfl⟩
  · intro x
    rw [hmem x, hBT x]
    constructor
    · intro hx
      exact CFSG.KC.LQT.PWSnd.ball_subset_closure gens fuel ((hBT x).2 hx)
    · intro hx
      exact CFSG.KC.LQT.PWSnd.closure_subset_of_closed gens {x | x ∈ T} h1T hclT hx

theorem orb_sound (S : Finset (Fin 315)) (fuel : ℕ) {G : List ℕ} (hG : gensA.map cJ = G)
    (P : List ℕ) (h1 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK P) = true)
    (hl : CFSG.KC.LQT.L.allA (CFSG.KC.LQT.Syl.pairUpK P)
      (fun q => Nat.blt q.2 (CFSG.KC.LQT.L.lenA G)) = true)
    (h2 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (orbE G (maskF S) P)) = true)
    (h3 : closedM G (orbE G (maskF S) P) = true)
    (hf : CFSG.KC.LQT.S.lenL (orbE G (maskF S) P) ≤ fuel) :
    ((bfsOrbit id maskF gensA S fuel).1.map maskF).Perm (orbE G (maskF S) P) := by
  subst hG
  set par := CFSG.KC.LQT.Syl.pairUpK P with hpar
  set Tr : List (Finset (Fin 315)) :=
    CFSG.KC.LQT.PWSnd.bfsT (fun (x : Finset (Fin 315)) (g : XJ) => g • x) 1 gensA S par with hTr
  have hlt : ∀ q ∈ par, q.2 < gensA.length := by
    intro q hq
    have := (CFSG.KC.LQT.L.allA_eq_true _ _).1 hl q hq
    rw [lenA_eq_length, List.length_map, Nat.blt_eq] at this
    exact this
  have hdef : ∀ q ∈ par, (gensA.map cJ).getD q.2 0 = cJ (gensA.getD q.2 1) := by
    intro q hq
    have h := hlt q hq
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h,
      List.getElem_map]
  have hE : orbE (gensA.map cJ) (maskF S) P = Tr.map maskF := by
    have e1 : orbE (gensA.map cJ) (maskF S) P = CFSG.KC.LQT.PWSnd.bfsT
        (fun m g => imgMaskW 315 9 g m) 0 (gensA.map cJ) (maskF S) par :=
      CFSG.KC.LQT.T2.bfsQ_eq _ _ _ _ _ h1
    have e2 := CFSG.KC.LQT.PWSnd.bfsT_map maskF cJ (fun (x : Finset (Fin 315)) (g : XJ) => g • x)
      (fun m g => imgMaskW 315 9 g m) (fun x g => (imgMaskW_cJ_maskF g x).symm) 1 0 gensA S
      par hdef
    rw [e1, hTr, e2]
  have hnd : (Tr.map maskF).Nodup := by
    rw [← hE]
    exact (CFSG.KC.LQT.PH.sortN_perm _).nodup_iff.1 (CFSG.KC.LQT.PH.sincK_nodup h2)
  have hTrnd : Tr.Nodup := hnd.of_map maskF
  have h0 : S ∈ Tr := CFSG.KC.LQT.PWSnd.start_mem_bfsT _ _ _ _ _
  have hcl : ∀ g ∈ gensA, ∀ x ∈ Tr, g • x ∈ Tr := by
    intro g hg x hx
    have hx' : maskF x ∈ orbE (gensA.map cJ) (maskF S) P := by
      rw [hE]
      exact List.mem_map_of_mem hx
    have hm := closedM_sound h3 (cJ g) (List.mem_map_of_mem hg) (maskF x) hx'
    rw [imgMaskW_cJ_maskF g x, hE] at hm
    obtain ⟨y, hy, hyc⟩ := List.mem_map.1 hm
    rw [maskF_inj_J2 hyc] at hy
    exact hy
  have hreach : ∀ y ∈ Tr, ∀ S' : Set (Finset (Fin 315)), S ∈ S' →
      (∀ g ∈ gensA, ∀ x ∈ S', g • x ∈ S') → y ∈ S' :=
    fun y hy S' h0' hcl' => CFSG.KC.LQT.PWSnd.bfsT_reach gensA S par S' h0' hcl' y hy
  have hf' : Tr.length ≤ fuel := by
    have := hf
    rw [CFSG.KC.LQT.PH.lenL_eq, hE, List.length_map] at this
    exact this
  have key := CFSG.KC.LQT.PWSnd.bfsOrbit_spec id (fun _ => rfl) maskF maskF_inj_J2 gensA S fuel Tr
    hTrnd h0 hcl hreach hf'
  rw [hE]
  exact key.map maskF

end CFSG.KC.LQT.PW

end
