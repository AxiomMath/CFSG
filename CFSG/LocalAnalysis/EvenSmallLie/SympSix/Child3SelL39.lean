module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Model

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.SelL39

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.J2Cover
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf chain_word_mem getElem!_rawInvs')

theorem index_sylowT : (sylowT.subgroupOf autT).index = 331695 := by
  have h := (sylowT.subgroupOf autT).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowT_le_autT).toEquiv, card_sylowT,
    card_autT] at h
  omega

theorem exists_conj_sylowT :
    ∀ τ ∈ autT, orderOf τ = 2 → ∃ g ∈ autT, g * τ * g⁻¹ ∈ sylowT :=
  exists_conj_mem_of_index sylowT_le_autT (k := 9) (by rw [card_sylowT]; norm_num)
    (by rw [index_sylowT]; decide)

theorem repWords_length : repWords.length = 11 := rfl

theorem wit_ok :
    repWords.all (lettersOK sylowS.size) = true ∧ witWords.all (lettersOK tS.size) = true ∧
      ∀ j < 11, witOK 182 (repArrs.getD j #[]) (tW (witWords.getD j [])) = true := by
  have h := wit_check
  simp only [witCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨List.all_eq_true.2 h.1.1.1.1, List.all_eq_true.2 h.1.1.1.2, h.2⟩

theorem letters_of_all {k : ℕ} {L : List (List ℤ)} (h : L.all (lettersOK k) = true) (i : ℕ) :
    lettersOK k (L.getD i []) = true := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.1 h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

@[expose] def repPerm (j : ℕ) : Equiv.Perm (Fin 182) := permOfArr 182 (repArrs.getD j #[])

@[expose] def witPerm (j : ℕ) : Equiv.Perm (Fin 182) := permOfArr 182 (tW (witWords.getD j []))

theorem repArrs_getD {j : ℕ} (hj : j < 11) :
    repArrs.getD j #[] = sylowW (repWords.getD j []) := by
  rw [repArrs, List.getD_eq_getElem _ _ (by simpa [repWords_length] using hj), List.getElem_map,
    ← List.getD_eq_getElem _ [] (by rw [repWords_length]; exact hj)]

theorem repPerm_spec {j : ℕ} (hj : j < 11) :
    Rep 182 (repArrs.getD j #[]) (repPerm j) ∧ repPerm j ∈ sylowT := by
  rw [repPerm, repArrs_getD hj]
  exact chain_word_mem (hn := by norm_num) (hk := by rw [sylowS_size]; norm_num)
    (hb := by decide) sylowChain_ok.2.1 _ (letters_of_all wit_ok.1 j)

theorem witPerm_spec (j : ℕ) :
    Rep 182 (tW (witWords.getD j [])) (witPerm j) ∧ witPerm j ∈ tT :=
  chain_word_mem (hn := by norm_num) (hk := by rw [tS_size]; norm_num) (hb := by decide)
    tChain_ok.2.1.1 _ (letters_of_all wit_ok.2.1 j)

theorem isWit_rep {j : ℕ}
    (hj : j < 11) : IsWit tT (repPerm j) (witPerm j) := by
  obtain ⟨h1, h2, h3, h4⟩ := witOK_spec (repPerm_spec hj).1 (witPerm_spec j).1 (wit_ok.2.2 j hj)
  exact ⟨(witPerm_spec j).2, h1, h2, h3, h4⟩

theorem sylowGens_rep {l : ℕ} (hl : l < 4) :
    Rep 182 sylowGens[l]! (permOfArr 182 sylowGens[l]!) ∧
      Rep 182 (invCand 182 sylowGens[l]!) (permOfArr 182 sylowGens[l]!)⁻¹ ∧
      permOfArr 182 sylowGens[l]! ∈ sylowT := by
  have h := sylowS_spec l (by rw [sylowS_size]; omega)
  rw [getElem!_rawInvs' (by rw [sylowS_size]; omega), sylowS_getElem! hl] at h
  exact h

theorem sylowGensT_getElem! {l : ℕ} (hl : l < 4) :
    sylowGensT[l]! = arrTable 182 sylowGens[l]! := by
  rw [sylowGensT, getElem!_pos _ l (by simpa [sylowGens_size] using hl), Array.getElem_map,
    getElem!_pos sylowGens l (by rw [sylowGens_size]; exact hl)]

theorem sylowGensInvT_getElem! {l : ℕ} (hl : l < 4) :
    sylowGensInvT[l]! = arrTable 182 (invCand 182 sylowGens[l]!) := by
  rw [sylowGensInvT, getElem!_pos _ l (by simpa [sylowGens_size] using hl), Array.getElem_map,
    getElem!_pos sylowGens l (by rw [sylowGens_size]; exact hl)]

theorem reps_ok :
    repsOK 182 sylowGensT sylowGensInvT invList (repArrs.map (arrTable 182)) 100 = true ∧
      (repArrs.all fun r => ordTest 182 2 (arrTable 182 r)) = true := by
  have h := reps_check
  simp only [repsCheck, Bool.and_eq_true] at h
  exact h

theorem cosetOrderTables_sylowQ (m : ℕ) :
    cosetOrderTables sylowQ 1 m = filterProducts 182 (ordTest 182 m) sylowTables (idT 182) [] := by
  rw [cosetOrderTables, sylowQ, ofArrays_levelTables sylowChain_ok.2.1]
  rfl

theorem orderOf_repPerm {j : ℕ} (hj : j < 11) :
    orderOf (repPerm j) = 2 := by
  have hn : (182 : ℕ) < 2 ^ 32 := by norm_num
  have h := List.all_eq_true.1 reps_ok.2 (repArrs.getD j #[]) (by
    rw [List.getD_eq_getElem _ _ (by simpa [repArrs, repWords_length] using hj)]
    exact List.getElem_mem _)
  exact (ordTest_iff perm_faithful (rep_arrTable hn (repPerm_spec hj).1) (by norm_num)).1 h

theorem exists_rep_of_involution
    {u : Equiv.Perm (Fin 182)} (hu : u ∈ sylowT) (hu2 : orderOf u = 2) :
    ∃ j < 11, ∃ c ∈ sylowT, u = c * repPerm j * c⁻¹ := by
  have hn : (182 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier sylowQ := ofArrays_valid (by norm_num) sylowChain_ok.2.1
  set reps := (List.range 11).map repPerm with hreps_def
  have hmap : reps.map CFSG.Sporadic.Schreier.toTable = repArrs.map (arrTable 182) := by
    rw [hreps_def, List.map_map]
    apply List.ext_getElem (by simp [repArrs, repWords_length])
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply,
      toTable_eq_arrTable (repPerm_spec h1).1, List.getD_eq_getElem]
  have hg : ∀ l < sylowGensT.size,
      CFSG.Sporadic.Th.Rep 182 sylowGensT[l]! (permOfArr 182 sylowGens[l]!) ∧
        CFSG.Sporadic.Th.Rep 182 sylowGensInvT[l]! (permOfArr 182 sylowGens[l]!)⁻¹ ∧
        permOfArr 182 sylowGens[l]! ∈ sylowQ.originalSubgroup := by
    intro l hl
    have hl4 : l < 4 := by simpa [sylowGensT, sylowGens_size] using hl
    obtain ⟨h1, h2, h3⟩ := sylowGens_rep hl4
    exact ⟨sylowGensT_getElem! hl4 ▸ rep_arrTable hn h1,
      sylowGensInvT_getElem! hl4 ▸ rep_arrTable hn h2, h3⟩
  have hreps : ∀ r ∈ reps, (1 : Equiv.Perm (Fin 182))⁻¹ * r ∈ sylowQ.originalSubgroup ∧
      orderOf r = 2 := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
    rw [List.mem_range] at hj
    exact ⟨by rw [inv_one, one_mul]; exact (repPerm_spec hj).2, orderOf_repPerm hj⟩
  have hok : repsOK 182 sylowGensT sylowGensInvT (cosetOrderTables sylowQ 1 2)
      (reps.map CFSG.Sporadic.Schreier.toTable) 100 = true := by
    rw [cosetOrderTables_sylowQ, hmap]
    exact reps_ok.1
  obtain ⟨r, hr, c, hc, e⟩ := (exists_conj_of_repsOK hn sylowQ hQ hg 1 (by simp) (by norm_num)
    reps hreps 100 hok).1 u (by rw [inv_one, one_mul]; exact hu) hu2
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
  exact ⟨j, List.mem_range.1 hj, c, hc, e⟩

theorem witness_all :
    ∀ τ ∈ autT, orderOf τ = 2 → ∃ w, IsWit tT τ w := by
  refine forall_witness_of_reps (fun g hg t ht => ?_) sylowT_le_autT exists_conj_sylowT 11
    repPerm (fun u hu hu2 => exists_rep_of_involution hu hu2) fun j hj => ⟨witPerm j, isWit_rep hj⟩
  exact (Subgroup.mem_normalizer_iff.1 (autT_le_normalizer hg) t).1 ht

theorem nonempty_mulEquiv_of_lieModel {D : Type} [Group D]
    (hT : CFSG.Blueprint.LieModel D .PSL 3 3 2) : Nonempty (D ≃* projectiveSL 3 F9) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hT
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]
    norm_num
  exact ⟨e.trans (projectiveSLCongr (FiniteField.ringEquivOfCardEq hc))⟩

theorem excluded_psl39 : ExcludedLie .PSL 3 3 2 := by
  intro Y _ _ D a J h hT
  have := h.normal
  obtain ⟨ψ⟩ := h.gl3
  obtain ⟨e⟩ := nonempty_mulEquiv_of_lieModel hT
  obtain ⟨M, hP, hA⟩ := exists_autModel e
  refine false_of_autModel_witness h.centralizer_eq h.orderOf_eq h.sup_eq.symm ψ M ?_
  intro τ hτ ho
  rw [hA] at hτ
  obtain ⟨w, hw⟩ := witness_all τ hτ ho
  exact ⟨w, hP ▸ hw.1, hw.2⟩

end CFSG.EvenSmallLie.Child3.SelL39
