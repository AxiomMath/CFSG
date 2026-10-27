module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4ElemAbelian

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier CFSG.ONSchreier.Native Equiv

section Plus


theorem K4_le_CJ : K4 ≤ CJ := K4_le_S4.trans S4_le

@[expose] def c4K (s : ℕ) : K4 :=
  if h : s < 9 then ⟨c4G s, Subgroup.subset_closure ⟨⟨s, by rw [c4Nat_size]; exact h⟩, rfl⟩⟩ else 1

@[expose] def thetaK : K4 →* Perm (Fin 12) := thetaHom.comp (Subgroup.inclusion K4_le_HJ)

theorem thetaK_apply (x : K4) :
    thetaK x = (thetaJ (Subgroup.inclusion K4_le_HJ x) : Perm (Fin 12)) := rfl

theorem thetaK_injective : Function.Injective thetaK := by
  intro a b h
  rw [thetaK_apply, thetaK_apply] at h
  exact Subgroup.inclusion_injective _ (thetaJ.injective (Subtype.ext h))

theorem thetaK_c4K {s : ℕ} (hs : s < 9) :
    thetaK (c4K s) = (thetaJ ⟨c4G s, c4G_mem_HJ s⟩ : Perm (Fin 12)) := by
  rw [thetaK_apply]
  simp only [c4K, dif_pos hs]
  rfl

theorem s12_get {s : ℕ} (hs : s < 9) : s12[s]! = natArr InvData.c4Nat[s]! := by
  have h9 : s < InvData.c4Nat.size := by rw [c4Nat_size]; exact hs
  unfold s12 natArrs
  rw [getElem!_pos _ s (by simp [h9]), Array.getElem_map, getElem!_pos _ s h9]
  rfl

theorem prep_thetaK_gen {s : ℕ} (hs : s < 9) : PRep 12 s12[s]! (thetaK (c4K s)) := by
  rw [s12_get hs, thetaK_c4K hs]
  exact nat_c4G hs

theorem prep_thetaK_gen_inv {s : ℕ} (hs : s < 9) :
    PRep 12 (pinvs 12 s12)[s]! (thetaK (c4K s))⁻¹ :=
  prep_inv_of_pisInv (prep_thetaK_gen hs) ((sideF4PlusOK_parts sideF4PlusOK_true).2.2.2.1 s hs)

theorem prep_thetaK_word {w : List ℤ} (hw : plettersOK 9 w = true) :
    PRep 12 (pword 12 s12 (pinvs 12 s12) w)
      (thetaK (CFSG.Sporadic.LySchreier.evalWord c4K w)) :=
  prep_pword_hom thetaK c4K (fun h hh => prep_thetaK_gen hh) (fun h hh => prep_thetaK_gen_inv hh)
    w hw

theorem incl_c4K {s : ℕ} (hs : s < 9) : Subgroup.inclusion K4_le_CJ (c4K s) = gJn s := by
  apply Subtype.ext
  simp only [c4K, dif_pos hs, gJn, dif_pos (show s < 10 by omega), gJ, g4, if_pos hs]
  rfl

theorem letterIdx_lt {w : List ℤ} (hw : plettersOK 9 w = true) {l : ℤ} (hl : l ∈ w) :
    CFSG.Sporadic.LySchreier.letterIdx l < 9 := by
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hw
  obtain ⟨h0, h9⟩ := hw l hl
  unfold CFSG.Sporadic.LySchreier.letterIdx
  split_ifs <;> omega

theorem incl_evalWord {w : List ℤ} (hw : plettersOK 9 w = true) :
    Subgroup.inclusion K4_le_CJ (CFSG.Sporadic.LySchreier.evalWord c4K w) =
      CFSG.Sporadic.LySchreier.evalWord gJn w := by
  rw [CFSG.Sporadic.LySchreier.map_evalWord]
  apply CFSG.Sporadic.LySchreier.evalWord_congr
  intro l hl
  exact incl_c4K (letterIdx_lt hw hl)

@[expose] def eK (i : ℕ) : K4 := CFSG.Sporadic.LySchreier.evalWord c4K eWords[i]!

theorem evArr_get {i : ℕ} (hi : i < 5) : evArr[i]! = pword 12 s12 (pinvs 12 s12) eWords[i]! := by
  have hsz : eWords.size = 5 := (sideF4PlusOK_parts sideF4PlusOK_true).2.1
  unfold evArr
  rw [getElem!_pos _ i (by simp [hsz, hi]), Array.getElem_map, getElem!_pos _ i (by rw [hsz]; exact hi)]

theorem prep_evArr {i : ℕ} (hi : i < 5) : PRep 12 evArr[i]! (thetaK (eK i)) := by
  rw [evArr_get hi]
  exact prep_thetaK_word ((sideF4PlusOK_parts sideF4PlusOK_true).2.2.2.2.1 i hi).1

theorem prep_subProd_foldl (m : ℕ) :
    ∀ (L : List ℕ) (acc : Array ℕ) (σ : Perm (Fin 12)), PRep 12 acc σ → (∀ i ∈ L, i < 5) →
      PRep 12 (L.foldl (fun acc i => if m.testBit i then pcomp 12 acc evArr[i]! else acc) acc)
        (L.foldl (fun σ i => if m.testBit i then σ * thetaK (eK i) else σ) σ)
  | [], acc, σ, hp, _ => hp
  | i :: L, acc, σ, hp, hL => by
    have hi : i < 5 := hL i List.mem_cons_self
    have hL' : ∀ j ∈ L, j < 5 := fun j hj => hL j (List.mem_cons_of_mem _ hj)
    by_cases hb : m.testBit i = true
    · simp only [List.foldl_cons, hb, ite_true]
      exact prep_subProd_foldl m L _ _ (prep_pcomp hp (prep_evArr hi)) hL'
    · simp only [List.foldl_cons, hb]
      exact prep_subProd_foldl m L _ _ hp hL'

theorem evArr_size : evArr.size = 5 := by
  unfold evArr
  rw [Array.size_map]
  exact (sideF4PlusOK_parts sideF4PlusOK_true).2.1

theorem prep_subProd (m : ℕ) :
    PRep 12 (subProd12 evArr m)
      ((List.range 5).foldl (fun σ i => if m.testBit i then σ * thetaK (eK i) else σ) 1) := by
  unfold subProd12
  rw [evArr_size]
  exact prep_subProd_foldl m _ _ _ prep_pid fun i hi => List.mem_range.1 hi

theorem exists_E_K4 :
    ∃ E : Subgroup CJ, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 ∧
      E = Subgroup.closure (Subgroup.inclusion K4_le_CJ ∘ eK '' {i | i < 5}) := by
  obtain ⟨-, -, -, -, -, -, -, -, hcomm, hsq, hdist, -⟩ := sideF4PlusOK_parts sideF4PlusOK_true
  refine exists_isElemAbelian_card_thirtyTwo thetaK thetaK_injective (Subgroup.inclusion K4_le_CJ)
    (Subgroup.inclusion_injective _) eK ?_ ?_ ?_
  · intro i hi j hj
    exact (peq_iff (prep_pcomp (prep_evArr hi) (prep_evArr hj))
      (prep_pcomp (prep_evArr hj) (prep_evArr hi))).1 (hcomm i hi j hj)
  · intro i hi
    have h := (peq_iff (prep_pcomp (prep_evArr hi) (prep_evArr hi)) prep_pid).1 (hsq i hi)
    exact h
  · intro a ha b hb hab
    have h1 : peq 12 (subProd12 evArr a) (subProd12 evArr b) = true :=
      (peq_iff (prep_subProd a) (prep_subProd b)).2 hab
    have h2 : peq 12 (subProd12 evArr b) (subProd12 evArr a) = true :=
      (peq_iff (prep_subProd b) (prep_subProd a)).2 hab.symm
    have h3 : b ≤ a := (hdist a ha b hb).resolve_right (by rw [h1]; simp)
    have h4 : a ≤ b := (hdist b hb a ha).resolve_right (by rw [h2]; simp)
    omega

theorem rhoJ_word_eq_qb {w : List ℤ} {mask : ℕ} (hw : plettersOK 10 w = true) (hm : mask < 256)
    (hp : peq 800 (pword 800 s800 (pinvs 800 s800) w) (qbList 800 InvData.qPerms)[mask]! = true) :
    rhoJ (CFSG.Sporadic.LySchreier.evalWord gJn w) = qb mask :=
  eq_of_peq (prep_rhoJ_word hw) (qb_spec hm).2 hp

theorem word_mem_QJ {w : List ℤ} {mask : ℕ} (hw : plettersOK 10 w = true) (hm : mask < 256)
    (hp : peq 800 (pword 800 s800 (pinvs 800 s800) w) (qbList 800 InvData.qPerms)[mask]! = true) :
    CFSG.Sporadic.LySchreier.evalWord gJn w ∈ QJ := by
  rw [mem_QJ, rhoJ_word_eq_qb hw hm hp]
  exact (qb_spec hm).1

theorem eK_mem_QJ {i : ℕ} (hi : i < 5) : Subgroup.inclusion K4_le_CJ (eK i) ∈ QJ := by
  obtain ⟨hw, hm, hp⟩ := (sideF4PlusOK_parts sideF4PlusOK_true).2.2.2.2.1 i hi
  rw [eK, incl_evalWord hw]
  exact word_mem_QJ (plettersOK_mono (by norm_num) hw) hm hp

theorem exists_E_le_QJ :
    ∃ E : Subgroup CJ, E ≤ QJ ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 := by
  obtain ⟨E, hE, hcard, rfl⟩ := exists_E_K4
  refine ⟨_, ?_, hE, hcard⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact eK_mem_QJ hi

theorem exists_noncomm_QJ : ∃ x ∈ QJ, ∃ y ∈ QJ, x * y ≠ y * x := by
  obtain ⟨-, -, -, -, hE, hbw, hbm, hbp, -, -, -, hnc⟩ := sideF4PlusOK_parts sideF4PlusOK_true
  obtain ⟨hw3, hm3, hp3⟩ := hE 3 (by norm_num)
  refine ⟨Subgroup.inclusion K4_le_CJ (eK 3), eK_mem_QJ (by norm_num),
    Subgroup.inclusion K4_le_CJ (CFSG.Sporadic.LySchreier.evalWord c4K bWord), ?_, ?_⟩
  · rw [incl_evalWord hbw]
    exact word_mem_QJ (plettersOK_mono (by norm_num) hbw) hbm hbp
  · intro h
    rw [← map_mul, ← map_mul] at h
    have h2 := Subgroup.inclusion_injective K4_le_CJ h
    have hb : PRep 12 bvArr (thetaK (CFSG.Sporadic.LySchreier.evalWord c4K bWord)) :=
      prep_thetaK_word hbw
    have h3 := congrArg thetaK h2
    rw [map_mul, map_mul] at h3
    have h4 := (peq_iff (prep_pcomp (prep_evArr (i := 3) (by norm_num)) hb)
      (prep_pcomp hb (prep_evArr (i := 3) (by norm_num)))).2 h3
    rw [hnc] at h4
    exact Bool.false_ne_true h4

end Plus

end CFSG.EvenSporadicStandard.HNRecog.SideF4
