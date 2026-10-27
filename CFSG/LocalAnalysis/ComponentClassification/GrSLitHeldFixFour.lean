module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFourCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowFacts
public import CFSG.GH74.KGroups.Generic

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier

theorem hfPointTreeOK_spec {n : ℕ} {gens : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gens.size, Rep n gens[j]! (f j)) {M : Subgroup (Equiv.Perm (Fin n))}
    (hM : ∀ j < gens.size, f j ∈ M) {root : Fin n} {pts par lab pos : Array ℕ}
    (h : hfPointTreeOK n gens root pts par lab pos = true) :
    ∀ x : Fin n, ∃ g ∈ M, g root = x := by
  simp only [hfPointTreeOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  have h0 : pts[0]! = root := h.1.1.2
  have htree := h.1.2
  have hpos := h.2
  have key : ∀ i < n, ∃ g ∈ M, (g root : ℕ) = pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases htree i hi with h1 | ⟨⟨hpar, hlab⟩, hstep⟩
      · subst h1
        exact ⟨1, M.one_mem, by rw [h0]; rfl⟩
      · obtain ⟨g, hg, hgr⟩ := ih _ hpar (hpar.trans hi)
        refine ⟨f lab[i]! * g, M.mul_mem (hM _ hlab) hg, ?_⟩
        rw [Equiv.Perm.mul_apply, ← hgs _ hlab, hgr, hstep]
  intro x
  obtain ⟨hlt, hx⟩ := hpos x x.2
  obtain ⟨g, hg, hgr⟩ := key _ hlt
  exact ⟨g, hg, Fin.ext (hgr.trans hx)⟩

@[expose] def hfK : Equiv.Perm (Fin 8330) := evalSignedWord [heGenPerm 0, heGenPerm 1] hfKWord

theorem rep_hfK : Rep 8330 hfKTab hfK :=
  rep_wordA_evalSignedWord (fun h hh => (rep_heAB h hh).1) (fun h hh => (rep_heAB h hh).2)
    hfFour_check.1

theorem rep_hfK_inv : Rep 8330 (invCand 8330 hfKTab) hfK⁻¹ :=
  rep_inv_of_isInvA rep_hfK hfFour_check.2.2.1

theorem hfK_mem : hfK ∈ heP := by
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)

theorem hfK_zero : hfK 0 = 7750 := by
  apply Fin.ext
  rw [← rep_hfK 0]
  exact hfFour_check.2.2.2.1

@[expose] def hfB (i : ℕ) : Equiv.Perm (Fin 8330) := ((hfB1Words.getD i []).map hfTL).prod

theorem hfB_mem {i : ℕ} (hi : i < 2) : hfB i ∈ hfT :=
  hfWord_mem (hfFour_check.2.2.2.2.1 i hi)

theorem tabRep_hfB {i : ℕ} (hi : i < 2) : TabRep hfB1Tabs[i]! (hfB i) := by
  rw [hfB1Tabs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hfTTabs _ fun j hj => by
    rw [hfTTabs_size]
    exact hfFour_check.2.2.2.2.1 i hi j hj

@[expose] def hfB1 : Subgroup (Equiv.Perm (Fin 8330)) := closure {hfB 0, hfB 1}

theorem hfB1_facts : hfB1 ≤ hfT ∧ Nat.card hfB1 = 4 ∧ ∀ x ∈ hfB1, x * x = 1 := by
  obtain ⟨-, -, -, -, -, -, h00, h11, h01, h0, h1, h10, -⟩ := hfFour_check
  have t0 := tabRep_hfB (i := 0) (by norm_num)
  have t1 := tabRep_hfB (i := 1) (by norm_num)
  obtain ⟨-, hsq, hcard⟩ := klein_closure (((t0.comp t0).eq_iff TabRep.idTab).1 h00)
    (((t1.comp t1).eq_iff TabRep.idTab).1 h11) (((t0.comp t1).eq_iff (t1.comp t0)).1 h01)
    (fun h => h0 ((t0.eq_iff TabRep.idTab).2 h)) (fun h => h1 ((t1.eq_iff TabRep.idTab).2 h))
    (fun h => h10 ((t1.eq_iff t0).2 h))
  refine ⟨?_, hcard, hsq⟩
  rw [hfB1, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hfB_mem (by norm_num)
  · exact hfB_mem (by norm_num)

theorem rep_heStrong_inv {j : ℕ} (hj : j < 9) :
    Rep 8330 (invCand 8330 (heStrong j)) (heStrongPerm j)⁻¹ :=
  rep_inv_of_isInvA (rep_heStrong hj) (hfFour_check.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj)

theorem rep_hfConjK {s : Tab} {g : Equiv.Perm (Fin 8330)} (hs : Rep 8330 s g) :
    Rep 8330 (hfConjK s) (hfK * g * hfK⁻¹) :=
  rep_comp (rep_comp rep_hfK hs) rep_hfK_inv

theorem conj_mem_normalizer_hfB1 {j : ℕ} (hj : j ∈ heStabIdx) :
    hfK * heStrongPerm j * hfK⁻¹ ∈ normalizer (hfB1 : Set (Equiv.Perm (Fin 8330))) := by
  obtain ⟨hj9, hconj⟩ := hfFour_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  set σ := hfK * heStrongPerm j * hfK⁻¹
  have hσ : Rep 8330 (hfConjK (heStrong j)) σ := rep_hfConjK (rep_heStrong hj9)
  have hσi : Rep 8330 (hfConjK (invCand 8330 (heStrong j))) σ⁻¹ := by
    have := rep_hfConjK (rep_heStrong_inv hj9)
    rwa [show hfK * (heStrongPerm j)⁻¹ * hfK⁻¹ = σ⁻¹ by simp only [σ]; group] at this
  have hgen : ∀ i < 2, σ * hfB i * σ⁻¹ ∈ hfB1 := by
    intro i hi
    have hmem := hconj i hi
    have hrep : TabRep (comp 8330 (comp 8330 (hfConjK (heStrong j)) hfB1Tabs[i]!)
        (hfConjK (invCand 8330 (heStrong j)))) (σ * hfB i * σ⁻¹) :=
      tabRep_comp_of_rep (rep_comp hσ (tabRep_hfB hi).2) hσi
    have t0 := tabRep_hfB (i := 0) (by norm_num)
    have t1 := tabRep_hfB (i := 1) (by norm_num)
    have hb0 : hfB 0 ∈ hfB1 := subset_closure (by simp)
    have hb1 : hfB 1 ∈ hfB1 := subset_closure (by simp)
    simp only [hfB1Elems, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h
    · rw [(hrep.eq_iff TabRep.idTab).1 h]; exact hfB1.one_mem
    · rw [(hrep.eq_iff t0).1 h]; exact hb0
    · rw [(hrep.eq_iff t1).1 h]; exact hb1
    · rw [(hrep.eq_iff (t0.comp t1)).1 h]; exact hfB1.mul_mem hb0 hb1
  refine CFSG.GH74.KGroups.mem_normalizer_of_conj_mem hfB1 σ fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hgen 0 (by norm_num)
    · exact hgen 1 (by norm_num)
  | one => simp
  | mul y z _ _ hy hz =>
    have := hfB1.mul_mem hy hz
    rwa [show σ * y * σ⁻¹ * (σ * z * σ⁻¹) = σ * (y * z) * σ⁻¹ by group] at this
  | inv y _ hy =>
    have := hfB1.inv_mem hy
    rwa [show (σ * y * σ⁻¹)⁻¹ = σ * y⁻¹ * σ⁻¹ by group] at this

theorem mem_levelGenerators_one {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heChain.levelGenerators 1) :
    ∃ j ∈ heStabIdx, s = heStrongPerm j := by
  rw [RawSchreierDatum.levelGenerators, List.mem_filter] at hs
  obtain ⟨hmem, hfix⟩ := hs
  have hst : heChain.strong.toList = List.ofFn fun j : Fin 9 => heStrongPerm j := by
    change (Vector.ofFn fun j : Fin 9 => heStrongPerm j).toList = _
    rw [Vector.toList_ofFn]
  rw [hst, List.mem_ofFn] at hmem
  obtain ⟨⟨j, hj⟩, hjs⟩ := hmem
  dsimp only at hjs
  subst hjs
  refine ⟨j, hfFour_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj ?_, rfl⟩
  have hb : heChain.base.toList.take 1 = [0] := by decide
  rw [hb, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hfix
  have := rep_heStrong hj 0
  rw [hfix] at this
  simpa using this

theorem stab_le_normalizer_hfB1 {p : Equiv.Perm (Fin 8330)} (hp : p ∈ heP) (hpω : p 7750 = 7750) :
    p ∈ normalizer (hfB1 : Set (Equiv.Perm (Fin 8330))) := by
  have hq : hfK⁻¹ * p * hfK ∈ heChain.levelSubgroup 1 := by
    rw [heChain.mem_levelSubgroup_iff heChain_valid.1 1 (by decide)]
    refine ⟨?_, fun b hb => ?_⟩
    · rw [← heP_eq_originalSubgroup]
      exact heP.mul_mem (heP.mul_mem (heP.inv_mem hfK_mem) hp) hfK_mem
    · have hb' : heChain.base.toList.take 1 = [0] := by decide
      rw [hb', List.mem_singleton] at hb
      subst hb
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hfK_zero, hpω, ← hfK_zero]
      simp
  have hle : heChain.levelSubgroup 1 ≤
      (normalizer (hfB1 : Set (Equiv.Perm (Fin 8330)))).comap (MulAut.conj hfK).toMonoidHom := by
    rw [RawSchreierDatum.levelSubgroup, closure_le]
    intro s hs
    obtain ⟨j, hj, rfl⟩ := mem_levelGenerators_one hs
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_mem_normalizer_hfB1 hj
  have := hle hq
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rwa [show hfK * (hfK⁻¹ * p * hfK) * hfK⁻¹ = p by group] at this

@[expose] def hfE2 : Equiv.Perm (Fin 8330) := (hfE2Word.map hfTL).prod

theorem hfE2_mem : hfE2 ∈ hfT := hfWord_mem hfFour_check.2.2.2.2.2.1

theorem tabRep_hfE2 : TabRep hfE2Tab hfE2 :=
  tabRep_wordTabS tabRep_hfTTabs _ fun j hj => by
    rw [hfTTabs_size]
    exact hfFour_check.2.2.2.2.2.1 j hj

@[expose] def hfB2 : Subgroup (Equiv.Perm (Fin 8330)) := closure {heT1P, hfE2}

theorem hfT_le_centralizer : ∀ t ∈ hfT, t * heT1P = heT1P * t := by
  intro t ht
  have := (mem_inf.1 (heInnerGrp1_le (hfT_le_grp1 ht))).2
  exact mem_centralizer_singleton_iff.1 this

theorem hfB2_facts : hfB2 ≤ hfT ∧ Nat.card hfB2 = 4 ∧ (∀ x ∈ hfB2, x * x = 1) ∧
    hfT ≤ normalizer (hfB2 : Set (Equiv.Perm (Fin 8330))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hee, he1, het, hgen, -⟩ := hfFour_check
  have te := tabRep_hfE2
  have tt := tabRep_of_rep rep_heT1 hfSylow_check.2.1
  have ht1 : heT1P * heT1P = 1 := by rw [← pow_two, ← orderOf_heT1P, pow_orderOf_eq_one]
  have hecomm : heT1P * hfE2 = hfE2 * heT1P := (hfT_le_centralizer _ hfE2_mem).symm
  obtain ⟨-, hsq, hcard⟩ := klein_closure ht1 (((te.comp te).eq_iff TabRep.idTab).1 hee) hecomm
    heT1P_ne_one (fun h => he1 ((te.eq_iff TabRep.idTab).2 h)) (fun h => het ((te.eq_iff tt).2 h))
  have hT1 : heT1P ∈ hfT := by
    have := hfTL_mem_hfT (j := 0) (by norm_num)
    simpa only [hfTL, ↓reduceIte] using this
  refine ⟨?_, hcard, hsq, ?_⟩
  · rw [hfB2, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hT1
    · exact hfE2_mem
  · rw [hfT, genGroup, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg5 : g < 5 := hfTTabs_size ▸ hg
    obtain ⟨hinv, hconj⟩ := hgen g hg5
    have tg := tabRep_hfTTabs g hg
    have tgi : Rep 8330 (invCand 8330 hfTTabs[g]!) (hfTL g)⁻¹ := rep_inv_of_isInvA tg.2 hinv
    have hgT : hfTL g ∈ hfT := hfTL_mem_hfT hg5
    have hb1 : heT1P ∈ hfB2 := subset_closure (by simp)
    have hbe : hfE2 ∈ hfB2 := subset_closure (by simp)
    have hgenB : ∀ y ∈ ({heT1P, hfE2} : Set (Equiv.Perm (Fin 8330))),
        hfTL g * y * (hfTL g)⁻¹ ∈ hfB2 := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [hfT_le_centralizer _ hgT, mul_assoc, mul_inv_cancel, mul_one]
        exact hb1
      · have hrep : TabRep (comp 8330 (comp 8330 hfTTabs[g]! hfE2Tab) (invCand 8330 hfTTabs[g]!))
            (hfTL g * hfE2 * (hfTL g)⁻¹) :=
          tabRep_comp_of_rep (rep_comp tg.2 te.2) tgi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hconj
        rcases hconj with h | h
        · rw [(hrep.eq_iff te).1 h]; exact hbe
        · rw [(hrep.eq_iff (te.comp tt)).1 h]; exact hfB2.mul_mem hbe hb1
    refine CFSG.GH74.KGroups.mem_normalizer_of_conj_mem hfB2 _ fun x hx => ?_
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hgenB y hy
    | one => simp
    | mul y z _ _ hy hz =>
      have := hfB2.mul_mem hy hz
      rwa [show hfTL g * y * (hfTL g)⁻¹ * (hfTL g * z * (hfTL g)⁻¹) =
        hfTL g * (y * z) * (hfTL g)⁻¹ by group] at this
    | inv y _ hy =>
      have := hfB2.inv_mem hy
      rwa [show (hfTL g * y * (hfTL g)⁻¹)⁻¹ = hfTL g * y⁻¹ * (hfTL g)⁻¹ by group] at this

@[expose] def hfOrbL (i : ℕ) : Equiv.Perm (Fin 8330) :=
  if i < 8 then hfK * heStrongPerm (heStabIdx.getD i 0) * hfK⁻¹ else hfTL (i - 8)

theorem hfOrbGens_size : hfOrbGens.size = 13 := by
  simp [hfOrbGens, hfTTabs_size, heStabIdx]

theorem rep_hfOrbGens : ∀ i < hfOrbGens.size, Rep 8330 hfOrbGens[i]! (hfOrbL i) := by
  intro i hi
  have hi13 : i < 13 := hfOrbGens_size ▸ hi
  simp only [hfOrbL]
  by_cases h8 : i < 8
  · simp only [h8, ↓reduceIte]
    have hlen : (heStabIdx.map fun j => hfConjK (heStrong j)).toArray.size = 8 := by
      simp [heStabIdx]
    have e : hfOrbGens[i]! = hfConjK (heStrong (heStabIdx.getD i 0)) := by
      rw [getElem!_pos _ i hi]
      simp only [hfOrbGens]
      rw [Array.getElem_append_left (by rw [hlen]; exact h8)]
      simp only [List.getElem_toArray, List.getElem_map]
      rw [List.getD_eq_getElem _ _ (by simpa [heStabIdx] using h8)]
    rw [e]
    have hj : heStabIdx.getD i 0 < 9 := by
      interval_cases i <;> decide
    exact rep_hfConjK (rep_heStrong hj)
  · simp only [h8, ↓reduceIte]
    have hlen : (heStabIdx.map fun j => hfConjK (heStrong j)).toArray.size = 8 := by
      simp [heStabIdx]
    have e : hfOrbGens[i]! = hfTTabs[i - 8]! := by
      rw [getElem!_pos _ i hi]
      simp only [hfOrbGens]
      rw [Array.getElem_append_right (by rw [hlen]; omega)]
      simp only [hlen]
      rw [getElem!_pos _ (i - 8) (by rw [hfTTabs_size]; omega)]
    rw [e]
    exact (tabRep_hfTTabs (i - 8) (by rw [hfTTabs_size]; omega)).2

theorem hfFour_gen :
    (⨆ (B : Subgroup (Equiv.Perm (Fin 8330))) (_ : B ≤ hfT) (_ : Nat.card B = 4)
      (_ : ∀ x ∈ B, x * x = 1), heP ⊓ normalizer (B : Set _)) = heP := by
  set M := ⨆ (B : Subgroup (Equiv.Perm (Fin 8330))) (_ : B ≤ hfT) (_ : Nat.card B = 4)
      (_ : ∀ x ∈ B, x * x = 1), heP ⊓ normalizer (B : Set (Equiv.Perm (Fin 8330))) with hM
  have hMle : M ≤ heP := iSup_le fun B => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    inf_le_left
  have hterm : ∀ B : Subgroup (Equiv.Perm (Fin 8330)), B ≤ hfT → Nat.card B = 4 →
      (∀ x ∈ B, x * x = 1) → heP ⊓ normalizer (B : Set (Equiv.Perm (Fin 8330))) ≤ M :=
    fun B h1 h2 h3 => le_iSup_of_le B (le_iSup_of_le h1 (le_iSup_of_le h2 (le_iSup_of_le h3
      le_rfl)))
  obtain ⟨hB1T, hB1c, hB1s⟩ := hfB1_facts
  obtain ⟨hB2T, hB2c, hB2s, hTN⟩ := hfB2_facts
  have hstab : ∀ p ∈ heP, p 7750 = 7750 → p ∈ M := fun p hp hpω =>
    hterm _ hB1T hB1c hB1s (mem_inf.2 ⟨hp, stab_le_normalizer_hfB1 hp hpω⟩)
  have hTM : hfT ≤ M := fun t ht =>
    hterm _ hB2T hB2c hB2s (mem_inf.2 ⟨hfT_le_heP ht, hTN ht⟩)
  have hgens : ∀ i < hfOrbGens.size, hfOrbL i ∈ M := by
    intro i hi
    have hi13 : i < 13 := hfOrbGens_size ▸ hi
    simp only [hfOrbL]
    split_ifs with h8
    · have hj : heStabIdx.getD i 0 < 9 := by interval_cases i <;> decide
      have hfix : heStrongPerm (heStabIdx.getD i 0) 0 = 0 := by
        have hmem : heStabIdx.getD i 0 ∈ heStabIdx := by interval_cases i <;> decide
        exact heStab_fix0 hmem
      refine hstab _ (heP.mul_mem (heP.mul_mem hfK_mem (heStrongPerm_mem hj))
        (heP.inv_mem hfK_mem)) ?_
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hfK_zero,
        show hfK⁻¹ (hfK 0) = 0 by simp, hfix]
    · exact hTM (hfTL_mem_hfT (by omega))
  have htrans := hfPointTreeOK_spec rep_hfOrbGens hgens (root := 7750)
    hfFour_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine le_antisymm hMle fun p hp => ?_
  obtain ⟨g, hgM, hg⟩ := htrans (p 7750)
  have h1 : g⁻¹ * p ∈ M := hstab _ (heP.mul_mem (heP.inv_mem (hMle hgM)) hp) (by
    rw [Equiv.Perm.mul_apply, ← hg]
    simp)
  have := M.mul_mem hgM h1
  rwa [mul_inv_cancel_left] at this

end CFSG.ComponentClassification.GrSLit.HeldFix
