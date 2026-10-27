module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Enum
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open scoped commutatorElement

theorem inv_mul_mem_of_mul_mem {G : Type*} [Group G] [Finite G] {E : Set G} {x : G}
    (hx : ∀ y ∈ E, x * y ∈ E) : ∀ y ∈ E, x⁻¹ * y ∈ E := by
  have hpow : ∀ m : ℕ, ∀ y ∈ E, x ^ m * y ∈ E := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hx _ (ih y hy)
  intro y hy
  have h1 : x ^ (orderOf x - 1) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [← h1]
  exact hpow _ y hy


section Basic

@[expose] def fElt (l : ℕ) : Pv := (fw[l]!.map hP).prod

@[expose] def F0 : Subgroup Pv := Subgroup.closure {fElt 0, fElt 1}

@[expose] def eElt (j : ℕ) : Pv := treeElt fElt fPar fLab j

theorem f_parts : treeOK 60 2 fStep base3 fPar fLab fIm = true ∧ fIm.size = 60 ∧
    distinctOK 60 fIm = true ∧ fClosedOK = true ∧ fNoZOK = true ∧ fFixOK = true ∧
    fCommOK = true := by
  have h := f_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem fw_letters : ∀ l < 2, ∀ a ∈ fw[l]!, a < 3 := by decide

theorem comm_letters : ∀ l < 2, (∀ a ∈ commX[l]!, a < 2) ∧ ∀ a ∈ commY[l]!, a < 2 := by decide

theorem map3_eq_pAct3 {f : ℕ → ℕ} {x : Pv} (hf : ∀ p < N, f p = pAct x p) {t : Pt3}
    (ht : Valid3 t) : map3 f t = pAct3 x t := by
  simp only [map3, pAct3, hf _ ht.1, hf _ ht.2.1, hf _ ht.2.2]

theorem evalW_fw {l : ℕ} (hl : l < 2) : ∀ p < N, evalW hArrs fw[l]! p = pAct (fElt l) p :=
  evalW_spec prep_hArrs _ (fw_letters l hl)

theorem fStep_eq : ∀ l < 2, ∀ t, Valid3 t → fStep l t = pAct3 (fElt l) t :=
  fun _ hl _ ht => map3_eq_pAct3 (evalW_fw hl) ht

theorem fIm_spec : ∀ j < 60, fIm[j]! = pAct3 (eElt j) base3 :=
  tree_spec f_parts.1 fElt valid3_base3 fStep_eq

theorem fElt_mem_F0 : ∀ l < 2, fElt l ∈ F0 := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem eElt_mem_F0 : ∀ j < 60, eElt j ∈ F0 := treeElt_mem f_parts.1 fElt F0 fElt_mem_F0

theorem eElt_inj {j j' : ℕ} (hj : j < 60) (hj' : j' < 60) (h : eElt j = eElt j') : j = j' :=
  distinct_spec f_parts.2.2.1 hj hj' (by rw [fIm_spec j hj, fIm_spec j' hj', h])

theorem eElt_closed : ∀ j < 60, ∀ l < 2, ∃ i < 60, eElt i = fElt l * eElt j := by
  intro j hj l hl
  have h := allBelowN_spec (allBelowN_spec f_parts.2.2.2.1 hj) hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hi, he⟩ := h
  refine ⟨_, hi, eq_of_pAct3 ?_⟩
  rw [← fIm_spec _ hi, he, fIm_spec j hj, fStep_eq l hl _ (valid3_pAct3 _ valid3_base3),
    ← pAct3_mul]

theorem exists_eElt {x : Pv} (hx : x ∈ F0) : ∃ j < 60, eElt j = x := by
  set E : Set Pv := {y | ∃ j < 60, eElt j = y} with hE
  have hgen : ∀ g ∈ ({fElt 0, fElt 1} : Set Pv), ∀ y ∈ E, g * y ∈ E := by
    have hmul : ∀ l < 2, ∀ y ∈ E, fElt l * y ∈ E := by
      rintro l hl y ⟨j, hj, rfl⟩
      exact eElt_closed j hj l hl
    rintro g (rfl | rfl)
    · exact hmul 0 (by norm_num)
    · exact hmul 1 (by norm_num)
  have h1 : (1 : Pv) ∈ E := ⟨0, by norm_num, treeElt_zero _ _ _⟩
  have key : x ∈ E := by
    induction hx using Subgroup.closure_induction_left with
    | one => exact h1
    | mul_left g hg y _ ih => exact hgen g hg y ih
    | inv_mul_cancel g hg y _ ih => exact inv_mul_mem_of_mul_mem (hgen g hg) y ih
  exact key

theorem card_F0 : Nat.card F0 = 60 := by
  let φ : Fin 60 → F0 := fun j => ⟨eElt j, eElt_mem_F0 j j.isLt⟩
  have hinj : Function.Injective φ := fun a b h =>
    Fin.ext (eElt_inj a.isLt b.isLt (congrArg Subtype.val h))
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨j, hj, hjx⟩ := exists_eElt hx
    exact ⟨⟨j, hj⟩, Subtype.ext hjx⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_fin]

theorem map3_zArr {t : Pt3} (ht : Valid3 t) : map3 (fun p => zArr[p]!) t = pAct3 zP t :=
  map3_eq_pAct3 (fun _ hp => getElem_eq_pAct prep_zArr hp) ht

theorem zP_not_mem_F0 : zP ∉ F0 := by
  intro h
  obtain ⟨j, hj, hjz⟩ := exists_eElt h
  have h1 : (fIm[j]! == zIm) = false := by
    simpa using allBelowN_spec f_parts.2.2.2.2.1 hj
  rw [beq_eq_false_iff_ne] at h1
  apply h1
  rw [fIm_spec j hj, hjz, zIm, map3_zArr valid3_base3]

end Basic

section Fix

theorem sigmaPv_fElt : ∀ l < 2, sigmaPv (fElt l) = fElt l := by
  intro l hl
  have h := allBelowN_spec f_parts.2.2.2.2.2.1 hl
  rw [beq_iff_eq] at h
  have e1 : ∀ p < N, evalW vArrs fw[l]! p = pAct (sigmaPv (fElt l)) p := by
    intro p hp
    rw [evalW_spec prep_vArrs _ (fw_letters l hl) p hp, fElt, map_list_prod, List.map_map]
    rfl
  rw [map3_eq_pAct3 e1 valid3_base3, map3_eq_pAct3 (evalW_fw hl) valid3_base3] at h
  exact eq_of_pAct3 h

theorem F0_le_CM : F0 ≤ CM := by
  rw [F0, Subgroup.closure_le]
  have hl : ∀ l < 2, fElt l ∈ CM := by
    intro l hl
    refine list_prod_mem fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hP_mem a (fw_letters l hl a ha)
  rintro _ (rfl | rfl)
  · exact hl 0 (by norm_num)
  · exact hl 1 (by norm_num)

theorem F0_fix : ∀ x ∈ F0, sigmaPv x = x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact sigmaPv_fElt 0 (by norm_num)
    · exact sigmaPv_fElt 1 (by norm_num)
  | one => exact map_one _
  | mul y y' _ _ hy hy' => rw [map_mul, hy, hy']
  | inv y _ hy => rw [map_inv, hy]

end Fix

section Alt

theorem evalFW_spec : ∀ w : List ℕ, (∀ a ∈ w, a < 2) → ∀ p < N,
    evalFW w p = pAct (w.map fElt).prod p
  | [], _, p, _ => by
    rw [List.map_nil, List.prod_nil, pAct_one]
    rfl
  | a :: w, hw, p, hp => by
    have ih := evalFW_spec w (fun b hb => hw b (List.mem_cons_of_mem a hb)) p hp
    have e : evalFW (a :: w) p = evalW hArrs fw[a]! (evalFW w p) := rfl
    rw [e, ih, evalW_fw (hw a (by simp)) _ (pAct_lt _ hp), ← pAct_mul, List.map_cons,
      List.prod_cons]

theorem wordF_mem (w : List ℕ) (hw : ∀ a ∈ w, a < 2) : (w.map fElt).prod ∈ F0 := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact fElt_mem_F0 a (hw a ha)

theorem fElt_eq_comm {l : ℕ} (hl : l < 2) :
    fElt l = ⁅(commX[l]!.map fElt).prod, (commY[l]!.map fElt).prod⁆ := by
  obtain ⟨hx, hy⟩ := comm_letters l hl
  set X := (commX[l]!.map fElt).prod
  set Y := (commY[l]!.map fElt).prod
  have h := allBelowN_spec f_parts.2.2.2.2.2.2 hl
  rw [beq_iff_eq] at h
  have e1 : ∀ p < N, evalFW commX[l]! (evalFW commY[l]! p) = pAct (X * Y) p := by
    intro p hp
    rw [evalFW_spec _ hy p hp, evalFW_spec _ hx _ (pAct_lt _ hp), ← pAct_mul]
  have e2 : ∀ p < N, evalW hArrs fw[l]! (evalFW commY[l]! (evalFW commX[l]! p)) =
      pAct (fElt l * Y * X) p := by
    intro p hp
    rw [evalFW_spec _ hx p hp, evalFW_spec _ hy _ (pAct_lt _ hp),
      evalW_fw hl _ (pAct_lt _ (pAct_lt _ hp)), ← pAct_mul, ← pAct_mul, mul_assoc]
  rw [map3_eq_pAct3 e1 valid3_base3, map3_eq_pAct3 e2 valid3_base3] at h
  have h' := eq_of_pAct3 h
  rw [commutatorElement_def]
  calc fElt l = fElt l * Y * X * X⁻¹ * Y⁻¹ := by group
    _ = X * Y * X⁻¹ * Y⁻¹ := by rw [← h']

theorem isPerfect_F0 : Group.IsPerfect F0 := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact F0.mul_mem (F0.mul_mem (F0.mul_mem ha hb) (F0.inv_mem ha)) (F0.inv_mem hb)
  · show Subgroup.closure {fElt 0, fElt 1} ≤ ⁅F0, F0⁆
    rw [Subgroup.closure_le]
    have hl : ∀ l < 2, fElt l ∈ ⁅F0, F0⁆ := by
      intro l hl
      rw [fElt_eq_comm hl]
      exact Subgroup.commutator_mem_commutator (wordF_mem _ (comm_letters l hl).1)
        (wordF_mem _ (comm_letters l hl).2)
    rintro _ (rfl | rfl)
    · exact hl 0 (by norm_num)
    · exact hl 1 (by norm_num)

theorem nonempty_F0_equiv : Nonempty (F0 ≃* alternatingGroup (Fin 5)) :=
  CFSG.Quasithin.A312J2.nonempty_mulEquiv_alt5_of_perfect isPerfect_F0 card_F0

end Alt

theorem cent_mem {x : Pv} (hx : x ∈ CM) (hσ : sigmaPv x = x) : x ∈ F0 ∨ zP⁻¹ * x ∈ F0 := by
  obtain ⟨k, hk, hkx⟩ := exists_mElt hx
  have hs : mSim[k]! = mIm[k]! := by rw [mSim_spec k hk, mIm_spec k hk, hkx, hσ]
  obtain ⟨j, hj, h | h⟩ := cover_spec hk hs
  · left
    have he : eElt j = x := eq_of_pAct3 (by rw [← fIm_spec j hj, h, mIm_spec k hk, hkx])
    rw [← he]
    exact eElt_mem_F0 j hj
  · right
    have hzf : zfIm[j]! = pAct3 (zP * eElt j) base3 := by
      rw [zfIm, getElem!_map' _ _ (by rw [f_parts.2.1]; exact hj), fIm_spec j hj,
        map3_zArr (valid3_pAct3 _ valid3_base3), pAct3_mul]
    have he : zP * eElt j = x := eq_of_pAct3 (by rw [← hzf, h, mIm_spec k hk, hkx])
    rw [← he, inv_mul_cancel_left]
    exact eElt_mem_F0 j hj

theorem card_cent_le : Nat.card {x : Pv // x ∈ CM ∧ sigmaPv x = x} ≤ 120 := by
  have hg : ∀ x : {x : Pv // x ∈ CM ∧ sigmaPv x = x}, ∃ jb : Fin 60 × Bool,
      (if jb.2 then zP * eElt jb.1 else eElt jb.1) = x.1 := by
    intro x
    rcases cent_mem x.2.1 x.2.2 with h | h
    · obtain ⟨j, hj, hjx⟩ := exists_eElt h
      exact ⟨(⟨j, hj⟩, false), by simpa using hjx⟩
    · obtain ⟨j, hj, hjx⟩ := exists_eElt h
      refine ⟨(⟨j, hj⟩, true), ?_⟩
      simp only [ite_true]
      rw [hjx, mul_inv_cancel_left]
  choose g hg using hg
  have hinj : Function.Injective g := by
    intro a b h
    have hb := hg b
    rw [← h] at hb
    exact Subtype.ext ((hg a).symm.trans hb)
  calc Nat.card _ ≤ Nat.card (Fin 60 × Bool) := Nat.card_le_card_of_injective g hinj
    _ = 120 := by rw [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]

end CFSG.ComponentClassification.SolMax.ONOut
