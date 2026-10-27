module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowRows
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import Certificates.Certificate25371

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open scoped commutatorElement
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SmallOddCore.Native (natArr)

theorem factsData_parts :
    tablesOK = true ∧ u1OK = true ∧ u2bOK = true ∧ t0OK = true ∧ perfOK = true := by
  have h := Certificates.certificate25371
  simp only [factsData, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

noncomputable abbrev facW : Equiv.Perm (Fin 3850) := tp 3850 (factsTbl 0)

noncomputable abbrev facH : Equiv.Perm (Fin 3850) := tp 3850 (factsTbl 1)

theorem size_natArr_factsTbl (k : ℕ) : (natArr (factsTbl k)).size = 3850 := by
  simp [natArr, factsTbl, CFSG.Sporadic.SmallOddCore.Native.hexT]

theorem tables_spec :
    facW ∈ hsR ∧ facW ∉ hsP ∧ facW * hsT1 = hsT1 * facW ∧ facH ∈ hsP ∧
      TabRep (natArr (factsTbl 0)) facW ∧ TabRep (natArr (factsTbl 1)) facH ∧
      TabRep (natArr (hsCentTbl 5)) hsT1 ∧ TabRep hInvTab facH⁻¹ := by
  have h := factsData_parts.1
  simp only [tablesOK, outerCommOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    and_assoc] at h
  obtain ⟨hu, ht, hw1, hw2, hw3, hw4, hh1, hh2, hh3, hh4⟩ := h
  have rU : Rep 3850 hsOuterTbl hsU := rep_tp hu
  have rW : Rep 3850 (factsTbl 0) facW := rep_tp hw1
  have rT : Rep 3850 (hsCentTbl 5) hsT1 := rep_tp ht
  have rH : Rep 3850 (factsTbl 1) facH := rep_tp hh1
  have hwP : facW ∉ hsP := fun hmem => by
    have := (hs_groupData.sift _ _ rW).2 hmem
    rw [this] at hw2
    exact absurd hw2 (by simp)
  have hwuP : facW * hsU ∈ hsP := (hs_groupData.sift _ _ (Rep.compT rW rU)).1 hw3
  have hwR : facW ∈ hsR := (hs_normalizing_model.2.2.2.2.2.1 facW).2 (Or.inr hwuP)
  have hHP : facH ∈ hsP := (hs_groupData.sift _ _ rH).1 hh2
  have tW : TabRep (natArr (factsTbl 0)) facW := tabRep_natArr hw1 (size_natArr_factsTbl 0)
  have tH : TabRep (natArr (factsTbl 1)) facH := tabRep_natArr hh1 (size_natArr_factsTbl 1)
  have tT : TabRep (natArr (hsCentTbl 5)) hsT1 :=
    tabRep_natArr ht (by simp [natArr, hsCentTbl, CFSG.Sporadic.SmallOddCore.Native.hexT])
  exact ⟨hwR, hwP, (commTT_iff rW rT).1 hw4, hHP, tW, tH, tT, tH.inv hh3 hh4⟩

theorem hsT1_mem_ord :
    hsT1 ∈ hsP ∧ orderOf hsT1 = 2 := by
  obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
  obtain ⟨-, h2, hout, -⟩ := hrows _ List.mem_cons_self
  dsimp only at h2 hout
  refine ⟨?_, h2⟩
  by_contra h
  exact Bool.false_ne_true (hout.2 h)

theorem hsT2_mem_ord :
    hsT2 ∈ hsP ∧ orderOf hsT2 = 2 := by
  obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
  obtain ⟨-, h2, hout, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h2 hout
  refine ⟨?_, h2⟩
  by_contra h
  exact Bool.false_ne_true (hout.2 h)

theorem hsT1_mem_hsC1 :
    hsT1 ∈ hsC1 :=
  mem_inf.2 ⟨hsT1_mem_ord.1, mem_centralizer_singleton_iff.2 rfl⟩

theorem hsC1_enum :
    Enumerates hsC1 hsC1Enum.tabs.toList := by
  rw [← hsC1_eq]
  exact hsC1_enumerates

theorem wordPerm_mem_hsC1
    {w : List ℕ}
    (hw : ∀ j ∈ w, j < 2) : (w.map hsC1Perm).prod ∈ hsC1 := by
  rw [← hsC1_eq]
  refine (genGroup 3850 hsC1Tabs hsC1Perm).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact subset_closure ⟨j, by simpa [hsC1Tabs] using hw j hj, rfl⟩

theorem wordPerm_mem_hsC2
    {w : List ℕ}
    (hw : ∀ j ∈ w, j < 4) : (w.map hsC2Perm).prod ∈ hsC2 := by
  rw [← hsC2_eq]
  refine (genGroup 3850 hsC2Tabs hsC2Perm).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact subset_closure ⟨j, by simpa [hsC2Tabs] using hw j hj, rfl⟩

theorem sq_of_check
    {gs : Array Tab} {G : ℕ → Equiv.Perm (Fin 3850)} (hgs : ∀ j < gs.size, TabRep gs[j]! (G j))
    (hchk : sqCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) gs = true)
    {y : Equiv.Perm (Fin 3850)} (hy : y ∈ hsR) (hyt : y * hsT1 = hsT1 * y)
    (hG : ∀ j < gs.size, y * G j = G j * y) : y * y = 1 := by
  obtain ⟨hwR, hwP, hwt, -, tW, -⟩ := tables_spec
  obtain ⟨h1, h2⟩ := sqCheck_spec hsC1_enum tW hgs hchk
  by_cases hyP : y ∈ hsP
  · exact h1 y (mem_inf.2 ⟨hyP, mem_centralizer_singleton_iff.2 hyt⟩) hG
  · obtain ⟨hU2, -, -, hmap, -⟩ := hs_normalizing_model
    have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
      rw [← hmap]
      exact ⟨p, hp, rfl⟩
    have hc : facW⁻¹ * y ∈ hsP := HypOne.index_two_of_normalizing hU2 hUn facW hwR hwP y hy hyP
    have hcomm : Commute (facW⁻¹ * y) hsT1 :=
      (Commute.inv_left (show Commute facW hsT1 from hwt)).mul_left (show Commute y hsT1 from hyt)
    have e : facW * (facW⁻¹ * y) = y := mul_inv_cancel_left _ _
    have := h2 (facW⁻¹ * y) (mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hcomm⟩)
      (fun j hj => by rw [e]; exact hG j hj)
    rwa [e] at this

theorem hs_u1 :
    ∀ y ∈ hsR, (∀ c ∈ hsC1, y * c = c * y) → y * y = 1 := by
  intro y hy hc
  refine sq_of_check (gs := hsC1Tabs) (G := hsC1Perm) tabRep_hsC1Tabs factsData_parts.2.1 hy
    (hc hsT1 hsT1_mem_hsC1) fun j hj => hc _ ?_
  rw [← hsC1_eq]
  exact subset_closure ⟨j, hj, rfl⟩

noncomputable abbrev hsOddA : Equiv.Perm (Fin 3850) := ([2, 2].map hsC2Perm).prod

noncomputable abbrev hsOddB : Equiv.Perm (Fin 3850) := ([1, 0].map hsC2Perm).prod

theorem tabRep_oddA : TabRep oddA hsOddA :=
  tabRep_wordTabS tabRep_hsC2Tabs _ fun j hj => by
    have : j = 2 := by simpa using hj
    subst this
    simp [hsC2Tabs]

theorem tabRep_oddB : TabRep oddB hsOddB :=
  tabRep_wordTabS tabRep_hsC2Tabs _ fun j hj => by
    have : j = 1 ∨ j = 0 := by simpa using hj
    simp only [hsC2Tabs, Array.size_ofFn]
    omega

theorem oddConj_get0 : oddConj[0]! = comp 3850 (comp 3850 hInvTab oddA) (natArr (factsTbl 1)) := by
  simp [oddConj]

theorem oddConj_get1 : oddConj[1]! = comp 3850 (comp 3850 hInvTab oddB) (natArr (factsTbl 1)) := by
  simp [oddConj]

theorem hsOddA_mem :
    hsOddA ∈ hsC2 :=
  wordPerm_mem_hsC2 (by decide)

theorem hsOddB_mem :
    hsOddB ∈ hsC2 :=
  wordPerm_mem_hsC2 (by decide)

theorem tabRep_word2 {m : ℕ} {a b : Tab} {A B : Equiv.Perm (Fin m)} (ha : TabRep a A)
    (hb : TabRep b B) (w : List ℕ) (hw : ∀ j ∈ w, j < 2) :
    TabRep (wordTabS m #[a, b] w) ((w.map fun j => if j = 0 then A else B).prod) := by
  refine tabRep_wordTabS (f := fun j => if j = 0 then A else B) (fun j hj => ?_) w
    (by simpa using hw)
  have : j < 2 := by simpa using hj
  interval_cases j <;> simpa using ‹_›

theorem u2b_parts :
    wordTabS 3850 #[oddA] (List.replicate 5 0) = idTab 3850 ∧
      wordTabS 3850 #[oddB] (List.replicate 3 0) = idTab 3850 ∧
      comp 3850 (comp 3850 hInvTab (wordTabS 3850 #[oddA, oddB] [1, 0, 1, 0]))
        (natArr (factsTbl 1)) = natArr (hsCentTbl 5) ∧
      sqCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) oddConj = true := by
  have h2 := factsData_parts.2.2.1
  simp only [u2bOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h2
  exact h2

theorem hsOddA_pow :
    hsOddA ^ 5 = 1 := by
  have h := (u2b_parts).1
  have t := tabRep_wordTabS (gs := #[oddA]) (f := fun _ => hsOddA)
    (fun j hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have e : #[oddA][0]! = oddA := by simp
      rw [e]
      exact tabRep_oddA) (List.replicate 5 0) (by simp)
  have := (t.eq_iff TabRep.idTab).1 h
  rwa [List.map_replicate, List.prod_replicate] at this

theorem hsOddB_pow :
    hsOddB ^ 3 = 1 := by
  have h := (u2b_parts).2.1
  have t := tabRep_wordTabS (gs := #[oddB]) (f := fun _ => hsOddB)
    (fun j hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have e : #[oddB][0]! = oddB := by simp
      rw [e]
      exact tabRep_oddB) (List.replicate 3 0) (by simp)
  have := (t.eq_iff TabRep.idTab).1 h
  rwa [List.map_replicate, List.prod_replicate] at this

theorem hs_u2b :
    ∀ y ∈ hsR, y * hsOddA = hsOddA * y → y * hsOddB = hsOddB * y → y * y = 1 := by
  intro y hy hA hB
  obtain ⟨-, -, -, hHP, -, tH, tT, tHi⟩ := tables_spec
  have hHR : facH ∈ hsR := (hs_normalizing_model.2.2.2.2.2.1 facH).2 (Or.inl hHP)
  obtain ⟨-, -, hS, hsq⟩ := u2b_parts
  have tS := tabRep_word2 (tabRep_oddA) (tabRep_oddB) [1, 0, 1, 0] (by decide)
  have hS' : facH⁻¹ * (hsOddB * hsOddA * hsOddB * hsOddA) * facH = hsT1 := by
    have := ((tHi.comp tS).comp tH).eq_iff tT |>.1 hS
    simpa [mul_assoc] using this
  have hyS : y * (hsOddB * hsOddA * hsOddB * hsOddA) = (hsOddB * hsOddA * hsOddB * hsOddA) * y := by
    have hA' : Commute y hsOddA := hA
    have hB' : Commute y hsOddB := hB
    exact ((hB'.mul_right hA').mul_right hB').mul_right hA'
  have hyt : (facH⁻¹ * y * facH) * hsT1 = hsT1 * (facH⁻¹ * y * facH) := by
    rw [← hS']
    calc facH⁻¹ * y * facH * (facH⁻¹ * (hsOddB * hsOddA * hsOddB * hsOddA) * facH)
        = facH⁻¹ * (y * (hsOddB * hsOddA * hsOddB * hsOddA)) * facH := by group
      _ = facH⁻¹ * ((hsOddB * hsOddA * hsOddB * hsOddA) * y) * facH := by rw [hyS]
      _ = facH⁻¹ * (hsOddB * hsOddA * hsOddB * hsOddA) * facH * (facH⁻¹ * y * facH) := by group
  have e0 : TabRep oddConj[0]! (facH⁻¹ * hsOddA * facH) := by
    rw [oddConj_get0]
    exact (tHi.comp tabRep_oddA).comp tH
  have e1 : TabRep oddConj[1]! (facH⁻¹ * hsOddB * facH) := by
    rw [oddConj_get1]
    exact (tHi.comp tabRep_oddB).comp tH
  have hsq' : (facH⁻¹ * y * facH) * (facH⁻¹ * y * facH) = 1 := by
    refine sq_of_check (gs := oddConj) (G := fun j => if j = 0 then facH⁻¹ * hsOddA * facH
      else facH⁻¹ * hsOddB * facH) (fun j hj => ?_) hsq
      (hsR.mul_mem (hsR.mul_mem (hsR.inv_mem hHR) hy) hHR) hyt (fun j hj => ?_)
    · have hj2 : j < 2 := by simpa [oddConj] using hj
      interval_cases j
      · simpa using e0
      · simpa using e1
    · have hj2 : j < 2 := by simpa [oddConj] using hj
      interval_cases j
      · simp only [↓reduceIte]
        calc facH⁻¹ * y * facH * (facH⁻¹ * hsOddA * facH)
            = facH⁻¹ * (y * hsOddA) * facH := by group
          _ = facH⁻¹ * (hsOddA * y) * facH := by rw [hA]
          _ = facH⁻¹ * hsOddA * facH * (facH⁻¹ * y * facH) := by group
      · simp only [one_ne_zero, ↓reduceIte]
        calc facH⁻¹ * y * facH * (facH⁻¹ * hsOddB * facH)
            = facH⁻¹ * (y * hsOddB) * facH := by group
          _ = facH⁻¹ * (hsOddB * y) * facH := by rw [hB]
          _ = facH⁻¹ * hsOddB * facH * (facH⁻¹ * y * facH) := by group
  calc y * y = facH * ((facH⁻¹ * y * facH) * (facH⁻¹ * y * facH)) * facH⁻¹ := by group
    _ = 1 := by rw [hsq']; group

noncomputable abbrev hsT0Perm (j : ℕ) : Equiv.Perm (Fin 3850) :=
  ((hsT0Words.getD j []).map hsC1Perm).prod

theorem hsT0Words_lt : ∀ j < 3, ∀ i ∈ hsT0Words.getD j [], i < 2 := by decide

theorem tabRep_hsT0Gens :
    ∀ j < hsT0Gens.size, TabRep hsT0Gens[j]! (hsT0Perm j) := by
  intro j hj
  have hj3 : j < 3 := by simpa [hsT0Gens] using hj
  rw [hsT0Gens, getElem!_pos _ j (by simpa using hj3), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsC1Tabs _ fun i hi => by
    have := hsT0Words_lt j hj3 i hi
    simpa [hsC1Tabs] using this

noncomputable abbrev hsT0 : Subgroup (Equiv.Perm (Fin 3850)) := genGroup 3850 hsT0Gens hsT0Perm

theorem hs_t0_spec :
    Nat.card hsT0 = 512 ∧ hsT0 ≤ hsC1 ∧
      hsP ⊓ centralizer (hsT0 : Set (Equiv.Perm (Fin 3850))) = zpowers hsT1 := by
  have h := factsData_parts.2.2.2.1
  simp only [t0OK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hEnum, hsize, hcont, hlen⟩ := h
  have hE : Enumerates hsT0 hsT0Enum.tabs.toList :=
    enumerates_closure (genGroup_hA tabRep_hsT0Gens) (genGroup_hgens tabRep_hsT0Gens) hEnum
  have hT0C1 : hsT0 ≤ hsC1 := by
    refine (closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact wordPerm_mem_hsC1 fun i hi =>
      hsT0Words_lt j (by simpa [hsT0Gens] using hj) i hi
  have hT1T0 : hsT1 ∈ hsT0 := by
    have hm : natArr (hsCentTbl 5) ∈ hsT0Enum.tabs.toList := by
      rw [Array.mem_toList_iff, ← Array.contains_iff_mem]
      exact hcont
    obtain ⟨g, hg, hgr⟩ := hE.sound _ hm
    obtain ⟨-, -, -, -, -, -, tT, -⟩ := tables_spec
    rwa [← hgr.perm_eq tT]
  have hF : Enumerates (centralizer (hsT0 : Set (Equiv.Perm (Fin 3850))) ⊓ hsC1)
      (hsC1Enum.tabs.toList.filter (fun x => hsT0Gens.all (commPt 3850 x))) := by
    refine hsC1_enum.filter _ fun t g hr => ?_
    rw [gs_all_iff tabRep_hsT0Gens hr, Subgroup.centralizer_closure, mem_centralizer_iff]
    constructor
    · rintro hc _ ⟨j, hj, rfl⟩
      exact (hc j hj).symm
    · intro hc j hj
      exact (hc _ ⟨j, hj, rfl⟩).symm
  have hle : zpowers hsT1 ≤ centralizer (hsT0 : Set (Equiv.Perm (Fin 3850))) ⊓ hsC1 := by
    rw [zpowers_le]
    refine mem_inf.2 ⟨?_, hsT1_mem_hsC1⟩
    rw [mem_centralizer_iff]
    intro t ht
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 (hT0C1 ht)).2
  have heq : zpowers hsT1 = centralizer (hsT0 : Set (Equiv.Perm (Fin 3850))) ⊓ hsC1 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hF.card, hlen, Nat.card_zpowers, hsT1_mem_ord.2])
  refine ⟨by rw [hE.card, Array.length_toList, hsize], hT0C1, le_antisymm (fun x hx => ?_) ?_⟩
  · rw [heq]
    refine mem_inf.2 ⟨hx.2, mem_inf.2 ⟨hx.1, mem_centralizer_singleton_iff.2 ?_⟩⟩
    exact (mem_centralizer_iff.1 hx.2 hsT1 hT1T0).symm
  · rw [heq]
    exact le_inf (inf_le_right.trans (inf_le_left)) inf_le_left

noncomputable abbrev hsPerfPerm (j : ℕ) : Equiv.Perm (Fin 3850) :=
  ((hsPerfWords.getD j []).map hsC1Perm).prod

theorem hsPerfWords_lt : ∀ j < 2, ∀ i ∈ hsPerfWords.getD j [], i < 2 := by decide

theorem hsPerfComm_lt : ∀ j < 2, (∀ i ∈ (hsPerfComm.getD j ([], [])).1, i < 2) ∧
    ∀ i ∈ (hsPerfComm.getD j ([], [])).2, i < 2 := by decide

theorem tabRep_hsPerfGens :
    ∀ j < hsPerfGens.size, TabRep hsPerfGens[j]! (hsPerfPerm j) := by
  intro j hj
  have hj2 : j < 2 := by simpa [hsPerfGens] using hj
  rw [hsPerfGens, getElem!_pos _ j (by simpa using hj2), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsC1Tabs _ fun i hi => by
    have := hsPerfWords_lt j hj2 i hi
    simpa [hsC1Tabs] using this

noncomputable abbrev hsPerf : Subgroup (Equiv.Perm (Fin 3850)) :=
  genGroup 3850 hsPerfGens hsPerfPerm

theorem hs_perfect_spec :
    hsPerf ≤ hsC1 ∧ ⁅hsPerf, hsPerf⁆ = hsPerf ∧ hsT1 ∈ hsPerf := by
  have h := factsData_parts.2.2.2.2
  simp only [perfOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨hcomm, hpow⟩ := h
  obtain ⟨-, -, -, -, -, -, tT, -⟩ := tables_spec
  have hsz : hsPerfGens.size = 2 := by simp [hsPerfGens]
  have hword : ∀ w : List ℕ, (∀ i ∈ w, i < 2) → (w.map hsPerfPerm).prod ∈ hsPerf := by
    intro w hw
    refine (genGroup 3850 hsPerfGens hsPerfPerm).list_prod_mem fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact subset_closure ⟨j, by rw [hsz]; exact hw j hj, rfl⟩
  have hgen : ∀ i < 2, hsPerfPerm i ∈ ⁅hsPerf, hsPerf⁆ := by
    intro i hi
    have hc := hcomm i hi
    obtain ⟨hX, hY⟩ := hsPerfComm_lt i hi
    set X := (hsPerfComm.getD i ([], [])).1
    set Y := (hsPerfComm.getD i ([], [])).2
    have tX := tabRep_wordTabS tabRep_hsPerfGens X (fun j hj => by rw [hsz]; exact hX j hj)
    have tY := tabRep_wordTabS tabRep_hsPerfGens Y (fun j hj => by rw [hsz]; exact hY j hj)
    have tq : TabRep hsPerfGens[i]! (hsPerfPerm i) := tabRep_hsPerfGens i (by rw [hsz]; exact hi)
    have e := ((tq.comp tY).comp tX).eq_iff (tX.comp tY) |>.1 (by simpa [commRel] using hc)
    have hq : hsPerfPerm i = ⁅(X.map hsPerfPerm).prod, (Y.map hsPerfPerm).prod⁆ := by
      rw [commutatorElement_def]
      calc hsPerfPerm i = (hsPerfPerm i * (Y.map hsPerfPerm).prod * (X.map hsPerfPerm).prod) *
            (X.map hsPerfPerm).prod⁻¹ * (Y.map hsPerfPerm).prod⁻¹ := by group
        _ = _ := by rw [e]
    rw [hq]
    exact commutator_mem_commutator (hword X hX) (hword Y hY)
  refine ⟨?_, le_antisymm ?_ ?_, ?_⟩
  · refine (closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact wordPerm_mem_hsC1 fun i hi => hsPerfWords_lt j (by simpa [hsPerfGens] using hj) i hi
  · rw [commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact hsPerf.mul_mem (hsPerf.mul_mem (hsPerf.mul_mem h₁ h₂) (hsPerf.inv_mem h₁))
      (hsPerf.inv_mem h₂)
  · refine (closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hgen j (by simpa [hsPerfGens] using hj)
  · have tw := tabRep_wordTabS tabRep_hsPerfGens (List.replicate 6 0)
      (fun i hi => by simp [hsPerfGens, (List.eq_of_mem_replicate hi)])
    have e := (tw.eq_iff tT).1 hpow
    simp only [List.map_replicate, List.prod_replicate] at e
    rw [← e]
    have h0 : hsPerfPerm 0 ∈ hsPerf := subset_closure ⟨0, by simp [hsPerfGens], rfl⟩
    exact pow_mem h0 6

end CFSG.EvenSporadicStandard.HSStd
