module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerTransport
public import Certificates.Certificate117011

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.Sporadic.SmallOddCore.Native (natArr)

theorem innerOK_parts :
    memOK = true ∧ orderOK = true ∧ filterOK = true ∧ eOK = true ∧ presOK = true ∧
      classOK = true ∧ stabOK = true := by
  have h := Certificates.certificate117011
  simp only [innerOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

noncomputable def tpA (t : Tab) : Equiv.Perm (Fin 3850) := by
  classical
  exact if h : ∃ g, TabRep t g then h.choose else 1

theorem tpA_eq {t : Tab} {g : Equiv.Perm (Fin 3850)} (h : TabRep t g) : tpA t = g := by
  classical
  have h' : ∃ g, TabRep t g := ⟨g, h⟩
  unfold tpA
  simp only [h', ↓reduceDIte]
  exact h'.choose_spec.perm_eq h

@[expose] def fixC (g : Equiv.Perm (Fin 3850)) : ℕ := ∑ i : Fin 3850, if g i = i then 1 else 0

theorem fixC_conj (g x : Equiv.Perm (Fin 3850)) : fixC (g * x * g⁻¹) = fixC x := by
  unfold fixC
  rw [← Equiv.sum_comp g (fun i => if (g * x * g⁻¹) i = i then 1 else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]

theorem fixC_one : fixC (1 : Equiv.Perm (Fin 3850)) = 3850 := by
  simp [fixC]

theorem countP_range_sum (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ∑ i : Fin n, if p i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Fin.sum_univ_castSucc]
    simp

theorem fixN_eq {T : Tab} {X : Equiv.Perm (Fin 3850)} (h : TabRep T X) : fixN T = fixC X := by
  rw [fixN, countP_range_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (T[i.val]! == i.val) = true ↔ X i = i := by
    rw [beq_iff_eq, h.apply i]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  by_cases hh : X i = i
  · simp [h1.2 hh, hh]
  · have : ¬ (T[i.val]! == i.val) = true := fun h' => hh (h1.1 h')
    simp [this, hh]

theorem ne_one_of_fixC {g : Equiv.Perm (Fin 3850)} {k : ℕ} (h : fixC g = k) (hk : k < 3850) :
    g ≠ 1 := fun h1 => by
  rw [h1, fixC_one] at h
  omega

section Words

variable {G Y : Equiv.Perm (Fin 3850)} {g gi y : Tab}

theorem tabRep_wordTab (hg : TabRep g G) (hgi : TabRep gi G⁻¹) (hy : TabRep y Y) :
    ∀ w : List ℕ, TabRep (wordTab g gi y w) (wordEval G Y (w.map letterOfCode))
  | [] => by simpa [wordTab, innerWordEval_nil] using (TabRep.idTab (n := 3850))
  | c :: w => by
    have h1 : wordTab g gi y (c :: w) = comp 3850 (codeTab g gi y c) (wordTab g gi y w) := by
      simp only [wordTab, List.foldr_cons]
    rw [h1, List.map_cons, innerWordEval_cons]
    refine TabRep.comp ?_ (tabRep_wordTab hg hgi hy w)
    rcases c with _ | _ | c <;> simp [codeTab, letterOfCode, Letter.eval, hg, hgi, hy]

end Words

theorem arr_all_mem {α : Type*} {as : Array α} {p : α → Bool} :
    as.all p = true ↔ ∀ x ∈ as, p x = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact h i hi
  · intro h i hi
    exact h _ (Array.getElem_mem hi)

theorem arr_any_mem {α : Type*} {as : Array α} {p : α → Bool} :
    as.any p = true ↔ ∃ x ∈ as, p x = true := by
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨_, Array.getElem_mem hi, h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact ⟨i, hi, h⟩

section Data

set_option linter.unusedSectionVars false

theorem c1_mem_iff {t : Tab} : inC1 t = true ↔ t ∈ hsC1Enum.tabs.toList := by
  rw [Array.mem_toList_iff, ← Array.contains_iff_mem, inC1, c1Tabs_def]

theorem c1_spec {t : Tab} (h : inC1 t = true) : TabRep t (tpA t) ∧ tpA t ∈ hsC1 := by
  obtain ⟨g, hg, hr⟩ := hsC1_enum.sound t (c1_mem_iff.1 h)
  rw [tpA_eq hr]
  exact ⟨hr, hg⟩

theorem perm_spec {k : ℕ} (hp : permOK 3850 (innerTbl k) = true)
    (hs : hsSift (innerTbl k) = true) : TabRep (itab k) (tpA (itab k)) ∧ tpA (itab k) ∈ hsP := by
  have hsz : (natArr (innerTbl k)).size = 3850 := by
    simp [natArr, innerTbl, CFSG.Sporadic.SmallOddCore.Native.hexT]
  have hr : TabRep (itab k) (tp 3850 (innerTbl k)) := tabRep_natArr hp hsz
  rw [tpA_eq hr]
  exact ⟨hr, (hs_groupData.sift _ _ (rep_tp hp)).1 hs⟩

theorem memOK_parts : inC1 tG = true ∧ inC1 tA = true ∧ inC1 tH = true ∧
    (∀ i < 4, inC1 (tY i) = true) ∧ (∀ i < 2, inC1 (tCP i) = true) ∧ inC1 (tCS 2) = true ∧
    inC1 (tCS 3) = true ∧ permOK 3850 (innerTbl 9) = true ∧ hsSift (innerTbl 9) = true ∧
    permOK 3850 (innerTbl 10) = true ∧ hsSift (innerTbl 10) = true ∧
    permOK 3850 (innerTbl 11) = true ∧ hsSift (innerTbl 11) = true ∧
    permOK 3850 (hsCentTbl 5) = true ∧ tGi.size = 3850 ∧ comp 3850 tGi tG = idTab 3850 := by
  have h := innerOK_parts.1
  simpa only [memOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] using h

noncomputable abbrev eG : Equiv.Perm (Fin 3850) := tpA tG
noncomputable abbrev eA : Equiv.Perm (Fin 3850) := tpA tA
noncomputable abbrev eH : Equiv.Perm (Fin 3850) := tpA tH
noncomputable abbrev eY (i : ℕ) : Equiv.Perm (Fin 3850) := tpA (tY i)
noncomputable abbrev eCP (i : ℕ) : Equiv.Perm (Fin 3850) := tpA (tCP i)
noncomputable abbrev eCS (i : ℕ) : Equiv.Perm (Fin 3850) := tpA (tCS i)
noncomputable abbrev eU : Equiv.Perm (Fin 3850) := tpA tU
noncomputable abbrev eGS (j : ℕ) : Equiv.Perm (Fin 3850) := tpA (tGS j)

theorem rep_G : TabRep tG eG ∧ eG ∈ hsC1 := c1_spec memOK_parts.1
theorem rep_A : TabRep tA eA ∧ eA ∈ hsC1 := c1_spec memOK_parts.2.1
theorem rep_H : TabRep tH eH ∧ eH ∈ hsC1 := c1_spec memOK_parts.2.2.1
theorem rep_Y {i : ℕ} (hi : i < 4) : TabRep (tY i) (eY i) ∧ eY i ∈ hsC1 :=
  c1_spec (memOK_parts.2.2.2.1 i hi)
theorem rep_CP {i : ℕ} (hi : i < 2) : TabRep (tCP i) (eCP i) ∧ eCP i ∈ hsC1 :=
  c1_spec (memOK_parts.2.2.2.2.1 i hi)
theorem rep_CS2 : TabRep (tCS 2) (eCS 2) ∧ eCS 2 ∈ hsC1 := c1_spec memOK_parts.2.2.2.2.2.1
theorem rep_CS3 : TabRep (tCS 3) (eCS 3) ∧ eCS 3 ∈ hsC1 := c1_spec memOK_parts.2.2.2.2.2.2.1
theorem rep_CS {i : ℕ} (hi : 2 ≤ i ∧ i < 4) : TabRep (tCS i) (eCS i) ∧ eCS i ∈ hsC1 := by
  obtain ⟨h1, h2⟩ := hi
  interval_cases i
  · exact rep_CS2
  · exact rep_CS3
theorem rep_U : TabRep tU eU ∧ eU ∈ hsP :=
  perm_spec (k := 9) memOK_parts.2.2.2.2.2.2.2.1 memOK_parts.2.2.2.2.2.2.2.2.1
theorem rep_GS0 : TabRep (tGS 0) (eGS 0) ∧ eGS 0 ∈ hsP :=
  perm_spec (k := 10) memOK_parts.2.2.2.2.2.2.2.2.2.1 memOK_parts.2.2.2.2.2.2.2.2.2.2.1
theorem rep_GS1 : TabRep (tGS 1) (eGS 1) ∧ eGS 1 ∈ hsP :=
  perm_spec (k := 11) memOK_parts.2.2.2.2.2.2.2.2.2.2.2.1
    memOK_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rep_GS {j : ℕ} (hj : j < 2) : TabRep (tGS j) (eGS j) ∧ eGS j ∈ hsP := by
  interval_cases j
  · exact rep_GS0
  · exact rep_GS1

theorem rep_Gi : TabRep tGi eG⁻¹ :=
  rep_G.1.inv memOK_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    memOK_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem rep_T1 : TabRep tT1 hsT1 := tables_spec.2.2.2.2.2.2.1

theorem tabRep_wT {y : Tab} {Y : Equiv.Perm (Fin 3850)} (hy : TabRep y Y) (w : List ℕ) :
    TabRep (wT y w) (wordEval eG Y (w.map letterOfCode)) :=
  tabRep_wordTab rep_G.1 rep_Gi hy w

theorem isInv_iff {t : Tab} {X : Equiv.Perm (Fin 3850)} (h : TabRep t X) :
    isInv t = true ↔ X * X = 1 :=
  (h.comp h).beq_iff TabRep.idTab

theorem comp_eq_iff {s t u v : Tab} {S T U V : Equiv.Perm (Fin 3850)} (hs : TabRep s S)
    (ht : TabRep t T) (hu : TabRep u U) (hv : TabRep v V) :
    comp 3850 s t = comp 3850 u v ↔ S * T = U * V :=
  (hs.comp ht).eq_iff (hu.comp hv)

theorem tabRep_pow5 {t : Tab} {X : Equiv.Perm (Fin 3850)} (h : TabRep t X) :
    TabRep (pow5 t) (X ^ 5) := by
  have := ((h.comp h).comp (h.comp h)).comp h
  rw [show X ^ 5 = X * X * (X * X) * X by simp [pow_succ, mul_assoc]]
  exact this

theorem orderOK_parts : pow5 tG = idTab 3850 ∧ tG ≠ idTab 3850 ∧
    comp 3850 tH tG = comp 3850 tG tH ∧ ∀ t ∈ hsC1Enum.tabs.toList,
      (pow5 t = idTab 3850 ∧ t ≠ idTab 3850) →
        ∃ c ∈ hsC1Enum.tabs.toList, comp 3850 c t = comp 3850 tG c := by
  have h := innerOK_parts.2.1
  simp only [orderOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rw [c1Tabs_def] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun t ht hp => ?_⟩
  have h5 := arr_all_mem.1 h4 t (Array.mem_toList_iff.1 ht)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h5
  rcases h5 with h5 | h5
  · exact absurd hp (by simpa using h5)
  · obtain ⟨c, hc, hce⟩ := arr_any_mem.1 h5
    exact ⟨c, Array.mem_toList_iff.2 hc, by simpa using hce⟩

theorem eG_pow : eG ^ 5 = 1 :=
  ((tabRep_pow5 rep_G.1).eq_iff TabRep.idTab).1 orderOK_parts.1

theorem eG_ne : eG ≠ 1 := fun h => orderOK_parts.2.1 ((rep_G.1.eq_iff TabRep.idTab).2 h)

theorem orderOf_eG : orderOf eG = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime eG_pow eG_ne

theorem eH_comm : eH * eG = eG * eH :=
  (comp_eq_iff rep_H.1 rep_G.1 rep_G.1 rep_H.1).1 orderOK_parts.2.2.1

theorem order_five_perm {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsC1) (h5 : orderOf x = 5) :
    ∃ c ∈ hsC1, c * x * c⁻¹ = eG := by
  obtain ⟨k, hk, hr⟩ := hsC1_enum.exists_pos hx
  rw [getElem!_pos _ k hk] at hr
  have hx5 : x ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at h5
  obtain ⟨c, hc, hce⟩ := orderOK_parts.2.2.2 _ (Array.mem_toList_iff.2 (Array.getElem_mem hk))
    ⟨((tabRep_pow5 hr).eq_iff TabRep.idTab).2 hx5,
      fun h => hx1 ((hr.eq_iff TabRep.idTab).1 h)⟩
  obtain ⟨c', hc', hcr⟩ := hsC1_enum.sound c hc
  refine ⟨c', hc', ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact (comp_eq_iff hcr hr rep_G.1 hcr).1 hce

theorem filterOK_parts : patOK tA = true ∧
    ∀ y ∈ hsC1Enum.tabs.toList, patOK y = true → hitOK y = true := by
  have h := innerOK_parts.2.2.1
  simp only [filterOK, Bool.and_eq_true] at h
  rw [c1Tabs_def] at h
  refine ⟨h.1, fun y hy hp => ?_⟩
  have := arr_all_mem.1 h.2 y (Array.mem_toList_iff.1 hy)
  simpa [hp] using this

theorem hPow_rep (k : ℕ) : TabRep (hPow k) (eH ^ k) := by
  induction k with
  | zero => simpa [hPow] using (TabRep.idTab (n := 3850))
  | succ k ih =>
    rw [pow_succ']
    exact rep_H.1.comp ih

theorem filter_perm {y : Equiv.Perm (Fin 3850)} (hy : y ∈ hsC1)
    (hyp : ∀ w : List Letter, wordEval eG y w = 1 ↔ wordEval eG eA w = 1) :
    ∃ (k i : ℕ), i < 4 ∧ eH ^ k * y * (eH ^ k)⁻¹ = eY i := by
  obtain ⟨k, hk, hr⟩ := hsC1_enum.exists_pos hy
  rw [getElem!_pos _ k hk] at hr
  have hmem : hsC1Enum.tabs[k] ∈ hsC1Enum.tabs.toList :=
    Array.mem_toList_iff.2 (Array.getElem_mem hk)
  have hpat : patOK hsC1Enum.tabs[k] = true := by
    simp only [patOK, List.all_eq_true]
    intro p hp
    have hA := List.all_eq_true.1 (show patOK tA = true from filterOK_parts.1) p hp
    have e : (wT hsC1Enum.tabs[k] p.1 == idTab 3850) = (wT tA p.1 == idTab 3850) :=
      Bool.eq_iff_iff.2 (((tabRep_wT hr p.1).beq_iff TabRep.idTab).trans
        ((hyp _).trans ((tabRep_wT rep_A.1 p.1).beq_iff TabRep.idTab).symm))
    rw [e]
    exact hA
  have hhit := filterOK_parts.2 _ hmem hpat
  simp only [hitOK, hPows, arr_any_mem, Array.mem_map, Array.mem_range, List.any_eq_true,
    List.mem_range, beq_iff_eq] at hhit
  obtain ⟨_, ⟨m, -, rfl⟩, i, hi, he⟩ := hhit
  refine ⟨m, i, hi, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact (comp_eq_iff (hPow_rep m) hr (rep_Y hi).1 (hPow_rep m)).1 he

@[expose] def eWF (j : Fin 4) : List Letter := (eWc.getD j.val []).map letterOfCode

noncomputable abbrev Ep : Subgroup (Equiv.Perm (Fin 3850)) :=
  closure (Set.range fun j : Fin 4 => wordEval eG eA (eWF j))

theorem eGens_size : (eGens tA).size = 4 := by simp [eGens]

theorem tabRep_eGens {j : ℕ} (hj4 : j < 4) :
    TabRep (eGens tA)[j]! (wordEval eG eA (eWF ⟨j, hj4⟩)) := by
  rw [eGens, getElem!_pos _ j (by simpa using hj4), Array.getElem_ofFn]
  exact tabRep_wT rep_A.1 _

theorem eOK_parts : enumOK 3850 (eGens tA) eEnum = true ∧ eEnum.tabs.size = 16 ∧
    (∀ x ∈ eEnum.tabs, ∀ y ∈ eEnum.tabs, comp 3850 x y = comp 3850 y x) ∧
    (∀ x ∈ eEnum.tabs, isInv x = true) ∧ tT1 ∈ eEnum.tabs ∧
    ∀ x ∈ eEnum.tabs, x = idTab 3850 ∨ fixN x = 170 := by
  have h := innerOK_parts.2.2.2.1
  simp only [eOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have := arr_all_mem.1 (arr_all_mem.1 h3 x hx) y hy
    simpa using this
  · exact fun x hx => arr_all_mem.1 h4 x hx
  · exact Array.contains_iff_mem.1 h5
  · intro x hx
    have := arr_all_mem.1 h6 x hx
    simpa [Bool.or_eq_true] using this

theorem eEnum_spec : Enumerates Ep eEnum.tabs.toList := by
  refine enumerates_closure (gens := eGens tA) ?_ ?_ eOK_parts.1
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.val, by rw [eGens_size]; exact j.2, tabRep_eGens j.2⟩
  · intro j hj
    rw [eGens_size] at hj
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, tabRep_eGens hj⟩

theorem Ep_card : Nat.card Ep = 16 := by
  rw [eEnum_spec.card, Array.length_toList, eOK_parts.2.1]

theorem Ep_spec {x : Equiv.Perm (Fin 3850)} (hx : x ∈ Ep) :
    ∃ t ∈ eEnum.tabs, TabRep t x := by
  obtain ⟨t, ht, hr⟩ := eEnum_spec.complete x hx
  exact ⟨t, Array.mem_toList_iff.1 ht, hr⟩

theorem Ep_comm {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ Ep) (hy : y ∈ Ep) : x * y = y * x := by
  obtain ⟨t, ht, hr⟩ := Ep_spec hx
  obtain ⟨t', ht', hr'⟩ := Ep_spec hy
  exact (comp_eq_iff hr hr' hr' hr).1 (eOK_parts.2.2.1 t ht t' ht')

theorem Ep_sq {x : Equiv.Perm (Fin 3850)} (hx : x ∈ Ep) : x * x = 1 := by
  obtain ⟨t, ht, hr⟩ := Ep_spec hx
  exact (isInv_iff hr).1 (eOK_parts.2.2.2.1 t ht)

theorem hsT1_mem_Ep : hsT1 ∈ Ep := by
  obtain ⟨g, hg, hr⟩ := eEnum_spec.sound tT1 (Array.mem_toList_iff.2 eOK_parts.2.2.2.2.1)
  rwa [← hr.perm_eq rep_T1]

theorem Ep_fix {x : Equiv.Perm (Fin 3850)} (hx : x ∈ Ep) (hx1 : x ≠ 1) : fixC x = 170 := by
  obtain ⟨t, ht, hr⟩ := Ep_spec hx
  rcases eOK_parts.2.2.2.2.2 t ht with h | h
  · exact absurd ((hr.eq_iff TabRep.idTab).1 h) hx1
  · rw [← fixN_eq hr, h]

theorem presOK_parts :
    (∀ i < 2, isInv (tY i) = true ∧ fixN (tY i) = 170 ∧ ∀ j < 4,
      eEnum.tabs.any (fun x => comp 3850 (tCP i) (wT (tY i) (eWc.getD j [])) ==
        comp 3850 x (tCP i)) = true) ∧
    ∀ i < 2, isInv (tY (i + 2)) = true ∧ fixN (tY (i + 2)) = 30 := by
  have h := innerOK_parts.2.2.2.2.1
  simpa only [presOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] using h

theorem pres_perm {i : ℕ} (hi : i < 2) : eY i * eY i = 1 ∧ fixC (eY i) = 170 ∧
    ∃ c ∈ hsC1, ∀ j : Fin 4, c * wordEval eG (eY i) (eWF j) * c⁻¹ ∈ Ep := by
  obtain ⟨h1, h2, h3⟩ := presOK_parts.1 i hi
  have hi4 : i < 4 := by omega
  have hY := rep_Y hi4
  refine ⟨(isInv_iff hY.1).1 h1, by rw [← fixN_eq hY.1, h2], eCP i, (rep_CP hi).2, fun j => ?_⟩
  obtain ⟨x, hx, hxe⟩ := arr_any_mem.1 (h3 j.val j.2)
  obtain ⟨x', hx', hxr⟩ := eEnum_spec.sound x (Array.mem_toList_iff.2 hx)
  have hw := tabRep_wT hY.1 (eWc.getD j.val [])
  have := (comp_eq_iff (rep_CP hi).1 hw hxr (rep_CP hi).1).1 (by simpa using hxe)
  have e : eCP i * wordEval eG (eY i) (eWF j) * (eCP i)⁻¹ = x' := mul_inv_eq_iff_eq_mul.2 this
  rw [e]
  exact hx'

theorem classOK_parts :
    permOK 3850 (hsCentTbl 12) = true ∧ fixN (natArr (hsCentTbl 12)) = 30 ∧ fixN tT1 = 170 ∧
    fixN tA = 170 ∧ isInv tA = true ∧ isInv tB = true ∧ fixN tB = 30 ∧ isInv tU = true ∧
    fixN tU = 30 ∧ comp 3850 tU tB = comp 3850 tB tU ∧ fixN (comp 3850 tU tB) = 30 ∧
    ∀ i < 2, isInv (wT (tY (i + 2)) wbc) = true ∧ fixN (wT (tY (i + 2)) wbc) = 170 := by
  have h := innerOK_parts.2.2.2.2.2.1
  simpa only [classOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] using h

theorem rep_T2 : TabRep (natArr (hsCentTbl 12)) hsT2 :=
  tabRep_natArr classOK_parts.1
    (by simp [natArr, hsCentTbl, CFSG.Sporadic.SmallOddCore.Native.hexT])

theorem fixC_hsT1 : fixC hsT1 = 170 := by
  rw [← fixN_eq rep_T1]
  exact classOK_parts.2.2.1

theorem fixC_hsT2 : fixC hsT2 = 30 := by
  rw [← fixN_eq rep_T2]
  exact classOK_parts.2.1

theorem inv_conj_cases {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsP) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    (∃ g ∈ hsP, g * hsT1 * g⁻¹ = x) ∨ ∃ g ∈ hsP, g * hsT2 * g⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf x = 2 := orderOf_eq_prime (by rwa [sq]) hx1
  obtain ⟨r, hr, g, hg, hrg⟩ := hs_reps.2.2.2.2 x hx h2
  rcases hr with rfl | rfl
  · exact Or.inl ⟨g, hg, hrg.symm⟩
  · exact Or.inr ⟨g, hg, hrg.symm⟩

theorem conj_t1_of_fix {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsP) (h2 : x * x = 1)
    (hf : fixC x = 170) : ∃ g ∈ hsP, g * hsT1 * g⁻¹ = x := by
  rcases inv_conj_cases hx (ne_one_of_fixC hf (by norm_num)) h2 with h | ⟨g, hg, e⟩
  · exact h
  · rw [← e, fixC_conj, fixC_hsT2] at hf
    omega

theorem conj_t2_of_fix {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsP) (h2 : x * x = 1)
    (hf : fixC x = 30) : ∃ g ∈ hsP, g * hsT2 * g⁻¹ = x := by
  rcases inv_conj_cases hx (ne_one_of_fixC hf (by norm_num)) h2 with ⟨g, hg, e⟩ | h
  · rw [← e, fixC_conj, fixC_hsT1] at hf
    omega
  · exact h

@[expose] def wbL : List Letter := wbc.map letterOfCode

noncomputable abbrev eB : Equiv.Perm (Fin 3850) := wordEval eG eA wbL

theorem rep_B : TabRep tB eB := tabRep_wT rep_A.1 wbc

theorem eA_facts : eA * eA = 1 ∧ fixC eA = 170 :=
  ⟨(isInv_iff rep_A.1).1 classOK_parts.2.2.2.2.1, by
    rw [← fixN_eq rep_A.1]; exact classOK_parts.2.2.2.1⟩

theorem eB_facts : eB * eB = 1 ∧ fixC eB = 30 :=
  ⟨(isInv_iff rep_B).1 classOK_parts.2.2.2.2.2.1, by
    rw [← fixN_eq rep_B]; exact classOK_parts.2.2.2.2.2.2.1⟩

theorem eU_facts : eU * eU = 1 ∧ fixC eU = 30 ∧ eU * eB = eB * eU ∧ fixC (eU * eB) = 30 := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2, h3, h4, -⟩ := classOK_parts
  exact ⟨(isInv_iff rep_U.1).1 h1, by rw [← fixN_eq rep_U.1]; exact h2,
    (comp_eq_iff rep_U.1 rep_B rep_B rep_U.1).1 h3, by
      rw [← fixN_eq (rep_U.1.comp rep_B)]; exact h4⟩

theorem eYB_facts {i : ℕ} (hi : i < 2) :
    wordEval eG (eY (i + 2)) wbL * wordEval eG (eY (i + 2)) wbL = 1 ∧
      fixC (wordEval eG (eY (i + 2)) wbL) = 170 := by
  obtain ⟨h1, h2⟩ := classOK_parts.2.2.2.2.2.2.2.2.2.2.2 i hi
  have hr : TabRep (wT (tY (i + 2)) wbc) (wordEval eG (eY (i + 2)) wbL) :=
    tabRep_wT (rep_Y (show i + 2 < 4 by omega)).1 wbc
  exact ⟨(isInv_iff hr).1 h1, by rw [← fixN_eq hr]; exact h2⟩

theorem eY23_facts {i : ℕ} (hi : i < 2) : eY (i + 2) * eY (i + 2) = 1 ∧ fixC (eY (i + 2)) = 30 := by
  obtain ⟨h1, h2⟩ := presOK_parts.2 i hi
  have hr := (rep_Y (show i + 2 < 4 by omega)).1
  exact ⟨(isInv_iff hr).1 h1, by rw [← fixN_eq hr]; exact h2⟩

theorem stabOK_parts :
    (∀ e < 8, comp 3850 (tE8 e) tT1 = tE8 (zmulL.getD e 0)) ∧ tE8 0 = idTab 3850 ∧ tE8 1 = tA ∧
    (∀ j < 2, ∀ e < 8, comp 3850 (tGS j) (tE8 e) =
      comp 3850 (tE8 ((sigmaL.getD j []).getD e 0)) (tGS j)) ∧
    ∀ i < 2, ∀ e < 8, comp 3850 (tCS (i + 2)) (tE8Y (i + 2) e) =
      comp 3850 (tE8 ((psiL.getD i []).getD e 0)) (tCS (i + 2)) := by
  have h := innerOK_parts.2.2.2.2.2.2
  simpa only [stabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] using h

@[expose] def yWL (e : ℕ) : List Letter := (yWc.getD e []).map letterOfCode

noncomputable abbrev eE8 (e : ℕ) : Equiv.Perm (Fin 3850) := wordEval eG eA (yWL e)

theorem rep_E8 (e : ℕ) : TabRep (tE8 e) (eE8 e) := tabRep_wT rep_A.1 _

theorem zmul_perm {e : ℕ} (he : e < 8) : eE8 e * hsT1 = eE8 (zmulL.getD e 0) :=
  (((rep_E8 e).comp rep_T1).eq_iff (rep_E8 _)).1 (stabOK_parts.1 e he)

theorem eE8_zero : eE8 0 = 1 :=
  ((rep_E8 0).eq_iff TabRep.idTab).1 stabOK_parts.2.1

theorem eE8_one : eE8 1 = eA :=
  ((rep_E8 1).eq_iff rep_A.1).1 stabOK_parts.2.2.1

theorem gs_perm {j e : ℕ} (hj : j < 2) (he : e < 8) :
    eGS j * eE8 e * (eGS j)⁻¹ = eE8 ((sigmaL.getD j []).getD e 0) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact (((rep_GS hj).1.comp (rep_E8 e)).eq_iff ((rep_E8 _).comp (rep_GS hj).1)).1
    (stabOK_parts.2.2.2.1 j hj e he)

theorem cs_perm {i e : ℕ} (hi : i < 2) (he : e < 8) :
    eCS (i + 2) * wordEval eG (eY (i + 2)) (yWL e) * (eCS (i + 2))⁻¹ =
      eE8 ((psiL.getD i []).getD e 0) := by
  have hc := rep_CS (i := i + 2) ⟨by omega, by omega⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact ((hc.1.comp (tabRep_wT (rep_Y (show i + 2 < 4 by omega)).1 _)).eq_iff
    ((rep_E8 _).comp hc.1)).1 (stabOK_parts.2.2.2.2 i hi e he)

end Data

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert
