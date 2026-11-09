module

public import Certificates.Data.Kernel.SporLatDcTW
public import CFSG.Certificates.Kernel.SporLatDcTSound

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem omTKw_sound {n w wi wk : Nat} {ts : Array (Array Nat)} {x0 : List Nat}
    {pts ci li lbl rows : List (List Nat)} {par via ord : List Nat}
    (h : omTKw n w wi wk ts x0 pts ci li ord lbl rows par via (packDc w (pts.map (encodeSet n)))
      (ci.map (packDc wi)) = true) :
    lbl.getD 0 [] = x0 ∧ 0 < lbl.length ∧
    (∀ l < ts.size, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = codeSetT n (ts.getD l #[]) (lbl.getD i [])) ∧
    (∀ i < lbl.length, i = 0 ∨ (par.getD i 0 < i ∧ via.getD i 0 < ts.size ∧
      (rows.getD (via.getD i 0) []).getD (par.getD i 0) 0 = i)) ∧
    lbl.Nodup := by
  unfold omTKw at h
  simp only [allRc_eq, zipAllRc_eq, incRc_eq, mapRc_eq, encRc_fun, insNRc_eq, eqLRc_iff,
    Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpts, hinc⟩, hcw⟩, hwi⟩, hcil⟩, htab⟩, h0⟩, hll⟩, htie⟩, hpk⟩ := h
  rw [tabTD_eq] at htab
  obtain ⟨-, hn, hact, htree, hnd⟩ := omPKo_sound hpk
  set N := pts.length with hN
  set cs := pts.map (encodeSet n) with hcs
  set F : Nat → Nat := fun k => cs.getD k 0 with hF
  have hPf : slotDc w (packDc w cs) = F := funext (slotDc_packDc w cs hcw)
  have hmono : ∀ a < N, ∀ b < N, a < b → F a < F b := by
    intro a ha b hb hab
    have hp := List.pairwise_iff_getElem.1 (incDc_pairwise _ hinc) a b
      (by simpa [hcs] using ha) (by simpa [hcs] using hb) hab
    simp only [hF]
    rw [List.getD_eq_getElem _ _ (by simpa [hcs] using ha),
      List.getD_eq_getElem _ _ (by simpa [hcs] using hb)]
    exact hp
  have hinj : ∀ a < N, ∀ b < N, F a = F b → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e (Nat.ne_of_lt (hmono a ha b hb h))
    · exact h
    · exact absurd e (Nat.ne_of_gt (hmono b hb a ha h))
  have htab' : ∀ l < ts.size, ∀ k < N, (ci.getD l []).getD k 0 < N ∧
      codeAT n (ts.getD l #[]) (F k) = F ((ci.getD l []).getD k 0) := by
    intro l hl k hk
    have hl' : l < ci.length := by omega
    have e := (allIdx_iff _ 0 ci).1 htab l hl'
    simp only [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at e
    obtain ⟨erl, ez⟩ := e
    have e2 := zipAllDc (d := 0) (e := []) ez erl k hk
    beta_reduce at e2
    rw [← List.getD_eq_getElem ci [] hl'] at e2
    obtain ⟨e3, e4⟩ := e2
    refine ⟨e3, ?_⟩
    have hpk : ∀ q ∈ pts.getD k [], q < n := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hpts _ (List.getElem_mem hk)
    have hFk : F k = encodeSet n (pts.getD k []) := getD_mapT _ pts [] 0 hk
    rw [hFk, codeAT_encodeSet n _ _ hpk, e4, hPf]
  have hCI : ∀ l < ts.size, slotDc wi ((ci.map (packDc wi)).getD l 0) =
      fun k => (ci.getD l []).getD k 0 := by
    intro l hl
    have hl' : l < ci.length := by omega
    have hrl : (ci.getD l []).length = N := by
      have e := (allIdx_iff _ 0 ci).1 htab l hl'
      simp only [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq] at e
      rw [List.getD_eq_getElem _ _ hl']
      exact e.1
    rw [getD_mapT _ ci [] 0 hl']
    refine funext (slotDc_packDc wi _ fun a ha => ?_)
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
    have hk2 := (htab' l hl k (by omega)).1
    rw [List.getD_eq_getElem _ _ hk] at hk2
    exact Nat.lt_of_lt_of_le hk2 hwi
  have hlt : ∀ i < li.length, ∀ q ∈ li.getD i [], q < N := fun i hi =>
    (zipAllDc (d := []) (e := []) htie hll i (by omega)).1
  have hlbl : ∀ i < lbl.length, lbl.getD i [] = (li.getD i []).map F := by
    intro i hi
    have e := (zipAllDc (d := []) (e := []) htie hll i hi).2
    rw [hPf] at e
    exact e.symm
  have hmemli : ∀ x ∈ li, ∀ q ∈ x, q < N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [← List.getD_eq_getElem li [] hi]
    exact hlt i hi
  have hlblEq : lbl = li.map (List.map F) := by
    refine List.ext_getElem (by simp [hll]) fun i h1 h2 => ?_
    rw [← List.getD_eq_getElem lbl [] h1, hlbl i h1, List.getElem_map,
      List.getD_eq_getElem li [] (by simpa using h2)]
  refine ⟨?_, by omega, fun l hl i hi => ?_, fun i hi => htree i (by omega), ?_⟩
  · rw [← h0]
    cases lbl with
    | nil =>
      simp only [List.length_nil, List.length_eq_zero_iff] at hll
      simp [hll] at hn
    | cons a l => rfl
  · have hi' : i < li.length := by omega
    obtain ⟨hr, he⟩ := hact l hl i hi'
    refine ⟨by omega, ?_⟩
    rw [hlbl ((rows.getD l []).getD i 0) (by omega), hlbl i hi, he, hCI l hl]
    have hx := hlt i hi'
    have hcx : ∀ a ∈ (li.getD i []).map (fun k => (ci.getD l []).getD k 0), a < N := by
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
      exact (htab' l hl k (hx k hk)).1
    rw [← insN_map_mono hmono _ hcx, List.map_map]
    change _ = insN (((li.getD i []).map F).map (codeAT n (ts.getD l #[])))
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact ((htab' l hl k (hx k hk)).2).symm
  · rw [hlblEq]
    exact List.Nodup.map_on (fun x hx y hy e => map_injOn_lt hinj x y (hmemli x hx)
      (hmemli y hy) e) hnd

theorem omOKTw_omOKG {n w wi wk : Nat} {ts : Array (Array Nat)} {x0 : List Nat}
    {pts ci li : List (List Nat)} {ord : List Nat} {O : OmegaData (List Nat)}
    (h : omOKTw n w wi wk ts x0 pts ci li ord O = true) :
    omOKG (fun l x => codeSetT n (ts.getD l #[]) x) x0 ts.size O = true := by
  obtain ⟨h0, hn, hact, htree, hnd⟩ := omTKw_sound h
  have eR : ∀ l, ((O.pn.toList.map Array.toList).getD l []) =
      (O.pn.toList.getD l default).toList := by
    intro l
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases O.pn.toList[l]? <;> rfl
  simp only [eR] at hact htree
  rw [← omOKL_eq]
  unfold omOKL
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨h0, hn⟩, fun l hl i hi => ⟨(hact l hl i hi).1, (hact l hl i hi).2⟩⟩,
    fun i hi => ?_⟩, hnd⟩
  rcases htree i hi with e | ⟨e1, e2, e3⟩
  · exact Or.inl e
  · exact Or.inr ⟨⟨e1, e2⟩, e3⟩

theorem omCodeTw_sound {n w wi wk : ℕ} {ts : Array (Array ℕ)} {x0 : List ℕ}
    {pts ci li : List (List ℕ)} {ord : List ℕ} {O : OmegaData (List ℕ)}
    (h : omOKTw n w wi wk ts x0 pts ci li ord O = true) : OmegaSpec (codeSetAct n) ts x0 O :=
  omCode_sound (omOKTw_omOKG h)

end CFSG.KC.SLDc

end
