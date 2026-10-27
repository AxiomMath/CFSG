module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native
open CFSG.EvenSmallLie.OmegaEight (wordsOf pushWords_getElem! chain_strong_spec chain_word_mem
  permOfArr_eq_of_rep getElem!_rawInvs' zpowers_le_normalizer_of_commute letters_of_all
  getD_mem_of_lt matMulM idCode matMulM_lt idCode_lt conjW)

theorem sylowW_spec {w : List ℤ} (hw : lettersOK 9 w = true) :
    Rep 136 (sylowW w) (permOfArr 136 (sylowW w)) ∧ permOfArr 136 (sylowW w) ∈ sylowT :=
  chain_word_mem (hn := by norm_num) (hk := by rw [sylowS_size]; norm_num) (hb := by decide)
    sylowChain_ok.1 w (by rw [sylowS_size]; exact hw)

theorem omegaW_spec {w : List ℤ} (hw : lettersOK 18 w = true) :
    Rep 136 (omegaW w) (permOfArr 136 (omegaW w)) ∧ permOfArr 136 (omegaW w) ∈ omegaT :=
  chain_word_mem (hn := by norm_num) (hk := by rw [omegaS_size]; norm_num) (hb := by decide)
    omegaChain_ok.1 w (by rw [omegaS_size]; exact hw)

theorem autW_spec {w : List ℤ} (hw : lettersOK 19 w = true) :
    Rep 136 (autW w) (permOfArr 136 (autW w)) ∧ permOfArr 136 (autW w) ∈ autT :=
  chain_word_mem (hn := by norm_num) (hk := by rw [autS_size]; norm_num) (hb := by decide)
    autChain_ok.1 w (by rw [autS_size]; exact hw)

theorem card_sylowT_subgroupOf
    : Nat.card (sylowT.subgroupOf autT) = 8192 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowT_le_autT).toEquiv, card_sylowT]

theorem index_sylowT : (sylowT.subgroupOf autT).index = 48195 := by
  have h := (sylowT.subgroupOf autT).card_mul_index
  rw [card_sylowT_subgroupOf, card_autT] at h
  omega

@[expose] def sylowA : Sylow 2 autT :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card (n := 13) (by rw [card_sylowT_subgroupOf]; norm_num) :
    IsPGroup 2 (sylowT.subgroupOf autT)).toSylow (by rw [index_sylowT]; norm_num)

theorem coe_sylowA
    : (sylowA : Subgroup autT) = sylowT.subgroupOf autT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe _ (by rw [index_sylowT]; norm_num)

theorem exists_conj_mem_sylowT
    {x b : Equiv.Perm (Fin 136)} (hx : x ∈ autT) (hb : b ∈ autT)
    (hxb : x * b = b * x) (hx2 : orderOf x = 2) (hb4 : orderOf b = 4) :
    ∃ a ∈ autT, a * x * a⁻¹ ∈ sylowT ∧ a * b * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : autT := ⟨x, hx⟩
  set b' : autT := ⟨b, hb⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  have hB : IsPGroup 2 (Subgroup.zpowers b') := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb4]; norm_num)
  have hE := hX.to_sup_of_normal_right' hB
    (zpowers_le_normalizer_of_commute (Subtype.ext hxb : x' * b' = b' * x'))
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autT sylowA Q
  have key : ∀ y ∈ Subgroup.zpowers x' ⊔ Subgroup.zpowers b',
      ((g⁻¹ * y * g : autT) : Equiv.Perm (Fin 136)) ∈ sylowT := by
    intro y hy
    have h1 : y ∈ (Q : Subgroup autT) := hQ hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, coe_sylowA,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  refine ⟨(g⁻¹ : autT), (g⁻¹ : autT).2, ?_, ?_⟩
  · have := key x' (Subgroup.mem_sup_left (Subgroup.mem_zpowers x'))
    simpa using this
  · have := key b' (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))
    simpa using this

theorem repWords_length : repWords.length = 36 := rfl

theorem repWords_letters : repWords.all (lettersOK 9) = true := by decide

@[expose] def repPerm (j : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 (repArrs.getD j #[])

theorem repArrs_getD {j : ℕ} (hj : j < 36) : repArrs.getD j #[] = sylowW (repWords.getD j []) := by
  rw [repArrs, List.getD_eq_getElem _ _ (by simpa [repWords_length] using hj), List.getElem_map,
    ← List.getD_eq_getElem _ [] (by rw [repWords_length]; exact hj)]

theorem repPerm_spec {j : ℕ} (hj : j < 36) :
    Rep 136 (repArrs.getD j #[]) (repPerm j) ∧ repPerm j ∈ sylowT := by
  rw [repPerm, repArrs_getD hj]
  exact sylowW_spec (letters_of_all repWords_letters j)

theorem sylowReps_ok :
    (repArrs.all fun r => ordTest 136 2 (arrTable 136 r)) = true := by
  have h := sylowReps_check
  simp only [sylowRepsLitCheck, Bool.and_eq_true] at h
  exact h.1

theorem orderOf_repPerm
    {j : ℕ} (hj : j < 36) : orderOf (repPerm j) = 2 := by
  have hn : (136 : ℕ) < 2 ^ 32 := by norm_num
  have h := List.all_eq_true.1 sylowReps_ok (repArrs.getD j #[]) (by
    rw [List.getD_eq_getElem _ _ (by simpa [repArrs, repWords_length] using hj)]
    exact List.getElem_mem _)
  exact (ordTest_iff perm_faithful (rep_arrTable hn (repPerm_spec hj).1) (by norm_num)).1 h

theorem exists_rep_of_involution
    {u : Equiv.Perm (Fin 136)} (hu : u ∈ sylowT)
    (hu2 : orderOf u = 2) : ∃ j < 36, ∃ c ∈ sylowT, u = c * repPerm j * c⁻¹ := by
  have hs := sa_facts
  obtain ⟨i, hi, rfl, au⟩ := exists_acts hs hu
  have hsq : matMulM (saMat i) (saMat i) = idCode := by
    have h1 := acts_mul au au
    have e1 : saElt i * saElt i = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
    rw [e1] at h1
    exact acts_unique hs (matMulM_lt _ _) idCode_lt h1 acts_one
  have hi0 : i ≠ 0 := by
    rintro rfl
    have e : saElt 0 = 1 := by
      rw [saElt]
      split
      · next h => exact absurd h.1 (Nat.lt_irrefl 0)
      · rfl
    rw [e, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  obtain ⟨hj, hc, hci, hcc, hconj⟩ := hs.invol i hi hi0 hsq
  set j := (invW i).1
  set c := (invW i).2.1
  set ci := (invW i).2.2
  obtain ⟨mc, ac⟩ := saElt_spec hs c hc
  obtain ⟨mci, aci⟩ := saElt_spec hs ci hci
  have ay : Acts (repPerm j) (saMat (yIdx j)) :=
    acts_of_rep (repPerm_spec hj).1 (hs.reps j hj).2
  have hinv : saElt ci = (saElt c)⁻¹ := by
    have e := eq_of_acts hs (sylowT.mul_mem mc mci) sylowT.one_mem idCode_lt
      (hcc ▸ acts_mul ac aci) acts_one
    exact eq_inv_of_mul_eq_one_right e
  refine ⟨j, hj, saElt c, mc, ?_⟩
  rw [← hinv]
  exact eq_of_acts hs hu (sylowT.mul_mem (sylowT.mul_mem mc (repPerm_spec hj).2) mci)
    (saMat_lt i) au (hconj ▸ acts_mul (acts_mul ac ay) aci)

theorem mainWords_letters : mainWords.all (lettersOK 9) = true := by decide

theorem conjWords_letters : conjWords.all (lettersOK 19) = true := by decide

theorem cent0Words_letters : (cent0Words.all fun ws => ws.all (lettersOK 18)) = true := by decide

theorem conjWords_length : conjWords.length = 36 := rfl

theorem repTypes_lt {j : ℕ} (hj : j < 36) : repTypes.getD j 0 < 5 := by
  interval_cases j <;> decide

@[expose] def mainPerm (i : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 (mainArrs.getD i #[])

theorem mainWords_length : mainWords.length = 5 := rfl

theorem mainArrs_getD {i : ℕ} (hi : i < 5) :
    mainArrs.getD i #[] = sylowW (mainWords.getD i []) := by
  rw [mainArrs, List.getD_eq_getElem _ _ (by simpa [mainWords_length] using hi), List.getElem_map,
    ← List.getD_eq_getElem _ [] (by rw [mainWords_length]; exact hi)]

theorem mainPerm_spec {i : ℕ} (hi : i < 5) :
    Rep 136 (mainArrs.getD i #[]) (mainPerm i) ∧ mainPerm i ∈ sylowT := by
  rw [mainPerm, mainArrs_getD hi]
  exact sylowW_spec (letters_of_all mainWords_letters i)

@[expose] def conjPerm (j : ℕ) : Equiv.Perm (Fin 136) := permOfArr 136 (conjArrs.getD j #[])

theorem conjArrs_getD {j : ℕ} (hj : j < 36) : conjArrs.getD j #[] = autW (conjWords.getD j []) := by
  rw [conjArrs, List.getD_eq_getElem _ _ (by simpa [conjWords_length] using hj),
    List.getElem_map, ← List.getD_eq_getElem _ [] (by rw [conjWords_length]; exact hj)]

theorem conjPerm_spec {j : ℕ} (hj : j < 36) :
    Rep 136 (conjArrs.getD j #[]) (conjPerm j) ∧ conjPerm j ∈ autT := by
  rw [conjPerm, conjArrs_getD hj]
  exact autW_spec (letters_of_all conjWords_letters j)

@[expose] def centPerm (i k : ℕ) : Equiv.Perm (Fin 136) :=
  permOfArr 136 (omegaW ((cent0Words.getD i []).getD k []))

theorem cent0Words_length : cent0Words.length = 5 := rfl

theorem centPerm_spec {i : ℕ} (hi : i < 5) (k : ℕ) :
    Rep 136 (omegaW ((cent0Words.getD i []).getD k [])) (centPerm i k) ∧ centPerm i k ∈ omegaT := by
  apply omegaW_spec
  have h := List.all_eq_true.1 cent0Words_letters
  rw [List.getD_eq_getElem cent0Words [] (by rw [cent0Words_length]; exact hi)]
  exact letters_of_all (h _ (List.getElem_mem _)) k

theorem le_ncard_conjClass_of_list {H : Subgroup (Equiv.Perm (Fin 136))}
    {b : Equiv.Perm (Fin 136)} {E : List (Equiv.Perm (Fin 136))} (hnodup : E.Nodup)
    (hE : ∀ y ∈ E, y ∈ conjClass H b) : E.length ≤ (conjClass H b).ncard := by
  have hfin : Finite H := Subtype.finite
  calc E.length = E.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = (E.toFinset : Set (Equiv.Perm (Fin 136))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (conjClass H b).ncard :=
      Set.ncard_le_ncard (fun y hy => hE y (List.mem_toFinset.1 hy)) (conjClass_finite H b)

theorem invs_ok :
    (∀ j < 36, ∀ t ∈ repGens j, isInvA 136 t (invCand 136 t) = true) ∧
      (∀ t ∈ conjArrs ++ mainArrs ++ repArrs, isInvA 136 t (invCand 136 t) = true) ∧
      (∀ ws ∈ cent0Words, ∀ w ∈ ws, isInvA 136 (omegaW w) (invCand 136 (omegaW w)) = true) ∧
      ∀ w ∈ fgWords, isInvA 136 (omegaW w) (invCand 136 (omegaW w)) = true := by
  have h := invs_check
  simp only [invsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem sylowRepsCheck_ok : ∀ j < 36,
    siftA 136 (rawLevels 136 omegaS (omegaBase.map Fin.val).toArray)
        (omegaBase.map Fin.val).toArray 0 (repArrs.getD j #[]) = decide (repTypes.getD j 0 < 3) ∧
      eqA 136 (conjArr (conjArrs.getD j #[]) (mainArrs.getD (repTypes.getD j 0) #[]))
        (repArrs.getD j #[]) = true := by
  have h := sylowReps_check
  simp only [sylowRepsLitCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact h.2

theorem conjPerm_inv_spec {j : ℕ} (hj : j < 36) :
    Rep 136 (invCand 136 (conjArrs.getD j #[])) (conjPerm j)⁻¹ :=
  rep_inv_of_isInvA (conjPerm_spec hj).1 (invs_ok.2.1 _ (List.mem_append_left _
    (List.mem_append_left _ (getD_mem_of_lt (by simpa [conjArrs, conjWords_length] using hj)))))

theorem conj_mainPerm {j : ℕ} (hj : j < 36) :
    conjPerm j * mainPerm (repTypes.getD j 0) * (conjPerm j)⁻¹ = repPerm j :=
  eq_of_eqA (rep_conjArr (conjPerm_spec hj).1 (conjPerm_inv_spec hj)
    (mainPerm_spec (repTypes_lt hj)).1) (repPerm_spec hj).1 (sylowRepsCheck_ok j hj).2

theorem repPerm_mem_omegaT_iff {j : ℕ} (hj : j < 36) :
    repPerm j ∈ omegaT ↔ repTypes.getD j 0 < 3 := by
  have h := (sylowRepsCheck_ok j hj).1
  rw [omegaT, omegaQ, ← ofArrays_mem_iff (by norm_num) omegaChain_ok.1 (repPerm_spec hj).1, h,
    decide_eq_true_iff]

theorem cent0_ok : ∀ i < 5, ∀ w ∈ cent0Words.getD i [],
    commArr (omegaW w) (mainArrs.getD i #[]) = true := by
  have h := cent0_check
  simp only [cent0Check, List.all_eq_true, List.mem_range] at h
  exact h

theorem centPerm_comm
    {i : ℕ} (hi : i < 5) {k : ℕ} (hk : k < (cent0Words.getD i []).length) :
    centPerm i k * mainPerm i = mainPerm i * centPerm i k :=
  eq_of_eqA (rep_compA (centPerm_spec hi k).1 (mainPerm_spec hi).1)
    (rep_compA (mainPerm_spec hi).1 (centPerm_spec hi k).1)
    (cent0_ok i hi _ (getD_mem_of_lt hk))

@[expose] def dGroup (x : Equiv.Perm (Fin 136)) : Subgroup (Equiv.Perm (Fin 136)) :=
  (omegaT ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer {x}

theorem repGens_length (j : ℕ) :
    (repGens j).length = (cent0Words.getD (repTypes.getD j 0) []).length + 1 := by
  simp [repGens]

theorem repGens_getD_lt {j l : ℕ} (hl : l < (cent0Words.getD (repTypes.getD j 0) []).length) :
    (repGens j).getD l #[] = conjArr (conjArrs.getD j #[])
      (omegaW ((cent0Words.getD (repTypes.getD j 0) []).getD l [])) := by
  rw [repGens, List.getD_append _ _ _ _ (by simpa using hl),
    List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem repGens_getD_last (j : ℕ) :
    (repGens j).getD (cent0Words.getD (repTypes.getD j 0) []).length #[] = repArrs.getD j #[] := by
  rw [repGens, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem repGens_spec
    {j : ℕ} (hj : j < 36) {l : ℕ} (hl : l < (repGens j).length) :
    Rep 136 ((repGens j).getD l #[]) (permOfArr 136 ((repGens j).getD l #[])) ∧
      Rep 136 (invCand 136 ((repGens j).getD l #[]))
        (permOfArr 136 ((repGens j).getD l #[]))⁻¹ ∧
      permOfArr 136 ((repGens j).getD l #[]) ∈ dGroup (repPerm j) := by
  have hinv := invs_ok.1 j hj _ (getD_mem_of_lt (d := #[]) hl)
  obtain ⟨h1, h2⟩ := rep_permOfArr hinv
  refine ⟨h1, h2, ?_⟩
  rw [repGens_length] at hl
  set i := repTypes.getD j 0 with hi
  have hi5 : i < 5 := repTypes_lt hj
  rcases Nat.lt_or_ge l (cent0Words.getD i []).length with hlt | hge
  · rw [repGens_getD_lt hlt]
    have hrep := rep_conjArr (conjPerm_spec hj).1 (conjPerm_inv_spec hj) (centPerm_spec hi5 l).1
    rw [permOfArr_eq_of_rep hrep]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left ((conj_mem_omegaT (conjPerm_spec hj).2).1
      (centPerm_spec hi5 l).2), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← conj_mainPerm hj]
    have hc := centPerm_comm hi5 hlt
    calc conjPerm j * centPerm i l * (conjPerm j)⁻¹ *
          (conjPerm j * mainPerm i * (conjPerm j)⁻¹) =
          conjPerm j * (centPerm i l * mainPerm i) * (conjPerm j)⁻¹ := by group
      _ = conjPerm j * (mainPerm i * centPerm i l) * (conjPerm j)⁻¹ := by rw [hc]
      _ = conjPerm j * mainPerm i * (conjPerm j)⁻¹ *
          (conjPerm j * centPerm i l * (conjPerm j)⁻¹) := by group
  · have hleq : l = (cent0Words.getD i []).length := by omega
    rw [hleq, repGens_getD_last]
    change repPerm j ∈ dGroup (repPerm j)
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
      Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def rgPerm (j : ℕ) (w : List ℕ) : Equiv.Perm (Fin 136) :=
  w.foldr (fun l acc => permOfArr 136 ((repGens j).getD l #[]) * acc) 1

theorem rgPerm_nil (j : ℕ) : rgPerm j [] = 1 := rfl

theorem rgPerm_cons (j l : ℕ) (w : List ℕ) :
    rgPerm j (l :: w) = permOfArr 136 ((repGens j).getD l #[]) * rgPerm j w := rfl

theorem rgConj_nil (j b : ℕ) : rgConj j [] b = b := rfl

theorem rgConj_cons (j l : ℕ) (w : List ℕ) (b : ℕ) :
    rgConj j (l :: w) b = matMulM (matMulM (rgCode j l) (rgConj j w b)) (rgInv j l) := by
  simp only [rgConj, conjW, List.foldr_cons]

theorem rgConj_lt (j : ℕ) (w : List ℕ) {b : ℕ} (hb : b < 2 ^ 64) : rgConj j w b < 2 ^ 64 := by
  cases w with
  | nil => rwa [rgConj_nil]
  | cons l w =>
    rw [rgConj_cons]
    exact matMulM_lt _ _

attribute [local irreducible] repGens matMulM

theorem rgPerm_spec {j : ℕ} (hj : j < 36)
    {b : Equiv.Perm (Fin 136)} {B : ℕ} (hb : Acts b B) (w : List ℕ)
    (hw : ∀ l ∈ w, l < (repGens j).length) :
    rgPerm j w ∈ dGroup (repPerm j) ∧ Acts (rgPerm j w * b * (rgPerm j w)⁻¹) (rgConj j w B) := by
  induction w with
  | nil =>
    rw [rgPerm_nil, rgConj_nil, inv_one, one_mul, mul_one]
    exact ⟨one_mem _, hb⟩
  | cons l w ih =>
    obtain ⟨m, a1⟩ := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hl := hw l List.mem_cons_self
    obtain ⟨r1, r2, r3⟩ := repGens_spec hj hl
    have g1 := acts_of_rep r1 (sa_facts.rg j hj l hl).1
    have g2 := acts_of_rep r2 (sa_facts.rg j hj l hl).2
    rw [rgPerm_cons, rgConj_cons]
    refine ⟨mul_mem r3 m, ?_⟩
    have e : permOfArr 136 ((repGens j).getD l #[]) * rgPerm j w * b *
        (permOfArr 136 ((repGens j).getD l #[]) * rgPerm j w)⁻¹ =
        permOfArr 136 ((repGens j).getD l #[]) * (rgPerm j w * b * (rgPerm j w)⁻¹) *
          (permOfArr 136 ((repGens j).getD l #[]))⁻¹ := by
      group
    rw [e]
    exact acts_mul (acts_mul g1 a1) g2

theorem five_conj_rep
    {j : ℕ} (hj : j < 36) {b : Equiv.Perm (Fin 136)} (hb : b ∈ sylowT)
    (hb4 : orderOf b = 4) (hbc : b * repPerm j = repPerm j * b) :
    5 ≤ (conjClass (dGroup (repPerm j)) b).ncard := by
  have hs := sa_facts
  obtain ⟨i, hi, rfl, ab⟩ := exists_acts hs hb
  have ay := acts_of_rep (repPerm_spec hj).1 (hs.reps j hj).2
  have h4 : saElt i ^ 4 = 1 := hb4 ▸ pow_orderOf_eq_one _
  have hsq : matMulM (saMat i) (saMat i) ≠ idCode := by
    intro h
    have e := eq_of_acts hs (sylowT.mul_mem hb hb) sylowT.one_mem idCode_lt
      (h ▸ acts_mul ab ab) acts_one
    have hd : orderOf (saElt i) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact e)
    rw [hb4] at hd
    exact absurd hd (by norm_num)
  have hq : matMulM (matMulM (saMat i) (saMat i)) (matMulM (saMat i) (saMat i)) = idCode := by
    have a := acts_mul (acts_mul ab ab) (acts_mul ab ab)
    have e : saElt i * saElt i * (saElt i * saElt i) = 1 := by
      rw [← h4, pow_succ, pow_succ, pow_two]
      simp only [mul_assoc]
    rw [e] at a
    exact acts_unique hs (matMulM_lt _ _) idCode_lt a acts_one
  have hcm : matMulM (saMat i) (saMat (yIdx j)) = matMulM (saMat (yIdx j)) (saMat i) := by
    have a1 := acts_mul ab ay
    rw [hbc] at a1
    exact acts_unique hs (matMulM_lt _ _) (matMulM_lt _ _) a1 (acts_mul ay ab)
  obtain ⟨ws, hlen, hlet, hpw⟩ := hs.five j hj i hi hsq hq hcm
  let e : List ℕ → Equiv.Perm (Fin 136) := fun w => rgPerm j w * saElt i * (rgPerm j w)⁻¹
  have he : ∀ w ∈ ws, e w ∈ conjClass (dGroup (repPerm j)) (saElt i) ∧
      Acts (e w) (rgConj j w (saMat i)) := fun w hw => by
    obtain ⟨m, a⟩ := rgPerm_spec hj ab w (hlet w hw)
    exact ⟨⟨_, m, rfl⟩, a⟩
  have hnd : (ws.map e).Nodup := by
    refine List.pairwise_map.2 (hpw.imp_of_mem fun hw hw' hne heq => hne ?_)
    have a := (he _ hw).2
    rw [heq] at a
    exact acts_unique hs (rgConj_lt _ _ (saMat_lt i)) (rgConj_lt _ _ (saMat_lt i)) a (he _ hw').2
  have := le_ncard_conjClass_of_list hnd fun y hy => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    exact (he w hw).1
  rwa [List.length_map, hlen] at this

theorem conj_mem_dGroup
    {g y d : Equiv.Perm (Fin 136)} (hg : g ∈ autT) (hd : d ∈ dGroup y) :
    g * d * g⁻¹ ∈ dGroup (g * y * g⁻¹) := by
  obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.1 hd
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hle : (omegaT ⊔ Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom ≤
        omegaT ⊔ Subgroup.zpowers (g * y * g⁻¹) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le_sup ?_ le_rfl
      rintro _ ⟨h, hh, rfl⟩
      exact (conj_mem_omegaT hg).1 hh
    exact hle ⟨d, hd1, rfl⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hd2 ⊢
    calc g * d * g⁻¹ * (g * y * g⁻¹) = g * (d * y) * g⁻¹ := by group
      _ = g * (y * d) * g⁻¹ := by rw [hd2]
      _ = g * y * g⁻¹ * (g * d * g⁻¹) := by group

theorem ncard_conjClass_dGroup_le
    {g y b : Equiv.Perm (Fin 136)} (hg : g ∈ autT) :
    (conjClass (dGroup y) b).ncard ≤ (conjClass (dGroup (g * y * g⁻¹)) (g * b * g⁻¹)).ncard := by
  have hfin : Finite (dGroup (g * y * g⁻¹)) := Subtype.finite
  rw [← Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  refine Set.ncard_le_ncard ?_ (conjClass_finite _ _)
  rintro _ ⟨z, ⟨d, hd, rfl⟩, rfl⟩
  refine ⟨g * d * g⁻¹, conj_mem_dGroup hg hd, ?_⟩
  rw [MulAut.conj_apply]
  group

theorem five_conj
    {x b : Equiv.Perm (Fin 136)} (hx : x ∈ autT) (hx2 : orderOf x = 2)
    (hb : b ∈ autT) (hb4 : orderOf b = 4) (hxb : x * b = b * x) :
    5 ≤ (conjClass (dGroup x) b).ncard := by
  obtain ⟨a, ha, hxa, hba⟩ := exists_conj_mem_sylowT hx hb hxb hx2 hb4
  have hx2' : orderOf (a * x * a⁻¹) = 2 := by
    rw [show a * x * a⁻¹ = MulAut.conj a x from rfl, MulEquiv.orderOf_eq, hx2]
  obtain ⟨j, hj, c, hc, hcj⟩ := exists_rep_of_involution hxa hx2'
  set b'' := c⁻¹ * (a * b * a⁻¹) * c with hb''
  have hb''S : b'' ∈ sylowT := sylowT.mul_mem (sylowT.mul_mem (sylowT.inv_mem hc) hba) hc
  have hb''4 : orderOf b'' = 4 := by
    rw [hb'', show c⁻¹ * (a * b * a⁻¹) * c = MulAut.conj (c⁻¹ * a) b by
      rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq, hb4]
  have hcomm : b'' * repPerm j = repPerm j * b'' := by
    have e : repPerm j = c⁻¹ * (a * x * a⁻¹) * c := by rw [hcj]; group
    rw [e, hb'']
    calc c⁻¹ * (a * b * a⁻¹) * c * (c⁻¹ * (a * x * a⁻¹) * c) = c⁻¹ * a * (b * x) * a⁻¹ * c := by
          group
      _ = c⁻¹ * a * (x * b) * a⁻¹ * c := by rw [hxb]
      _ = c⁻¹ * (a * x * a⁻¹) * c * (c⁻¹ * (a * b * a⁻¹) * c) := by group
  have h5 := five_conj_rep hj hb''S hb''4 hcomm
  have hg : a⁻¹ * c ∈ autT := autT.mul_mem (autT.inv_mem ha) (sylowT_le_autT hc)
  have e1 : (a⁻¹ * c) * repPerm j * (a⁻¹ * c)⁻¹ = x := by
    rw [show (a⁻¹ * c) * repPerm j * (a⁻¹ * c)⁻¹ = a⁻¹ * (c * repPerm j * c⁻¹) * a by group,
      ← hcj]
    group
  have e2 : (a⁻¹ * c) * b'' * (a⁻¹ * c)⁻¹ = b := by
    rw [hb'']
    group
  calc 5 ≤ _ := h5
    _ ≤ _ := ncard_conjClass_dGroup_le hg
    _ = _ := by rw [e1, e2]

end CFSG.EvenSmallLie.OmegaEightMinus
