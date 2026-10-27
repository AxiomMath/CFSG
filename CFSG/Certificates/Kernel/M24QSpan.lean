
module

public import Certificates.Data.Kernel.M24QSpan
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Gen

public section

namespace CFSG.KC.TabSpan

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {n : ℕ}

def IsTab (n : ℕ) (t : List ℕ) : Prop := t.length = n ∧ ∀ x ∈ t, x < n

theorem tabOK_iff {t : List ℕ} : tabOK n t = true ↔ IsTab n t := by
  simp [tabOK, IsTab, List.all_eq_true]

theorem range_isTab : IsTab n (List.range n) :=
  ⟨List.length_range, fun _ hx => List.mem_range.1 hx⟩

theorem compTab_length (s t : List ℕ) : (compTab s t).length = t.length := by
  simp [compTab]

theorem compTab_assoc (a b c : List ℕ) (h : ∀ x ∈ c, x < b.length) :
    compTab (compTab a b) c = compTab a (compTab b c) := by
  simp only [compTab, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h j hj)]

theorem compTab_isTab {s t : List ℕ} (hs : IsTab n s) (ht : IsTab n t) :
    IsTab n (compTab s t) := by
  refine ⟨by rw [compTab_length, ht.1], ?_⟩
  intro x hx
  simp only [compTab, List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hj' : j < s.length := hs.1 ▸ ht.2 j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
  exact hs.2 _ (List.getElem_mem hj')

theorem compTab_range_left {t : List ℕ} (h : ∀ x ∈ t, x < n) : compTab (List.range n) t = t := by
  unfold compTab
  conv_rhs => rw [← List.map_id t]
  apply List.map_congr_left
  intro j hj
  simp [List.getD_eq_getElem?_getD, h j hj]

theorem compTab_range_right {t : List ℕ} (h : t.length = n) : compTab t (List.range n) = t := by
  apply List.ext_getElem (by simp [compTab, h])
  intro i _ h2
  simp [compTab, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem spanTabs_cons (g : List ℕ) (gs : List (List ℕ)) :
    spanTabs n (g :: gs) = spanTabs n gs ++ (spanTabs n gs).map (compTab g) := rfl

theorem range_mem_spanTabs (gs : List (List ℕ)) : List.range n ∈ spanTabs n gs := by
  induction gs with
  | nil => exact List.mem_singleton_self _
  | cons g gs ih => rw [spanTabs_cons]; exact List.mem_append_left _ ih

theorem mem_spanTabs {gs : List (List ℕ)} {f : List ℕ} (hf : f ∈ spanTabs n gs) :
    ∃ ws : List (List ℕ), (∀ w ∈ ws, w ∈ gs) ∧ f = ws.foldr compTab (List.range n) := by
  induction gs generalizing f with
  | nil => exact ⟨[], by simp, List.mem_singleton.1 hf⟩
  | cons g gs ih =>
    rw [spanTabs_cons, List.mem_append, List.mem_map] at hf
    rcases hf with hf | ⟨f0, hf0, rfl⟩
    · obtain ⟨ws, hws, rfl⟩ := ih hf
      exact ⟨ws, fun w hw => List.mem_cons_of_mem _ (hws w hw), rfl⟩
    · obtain ⟨ws, hws, rfl⟩ := ih hf0
      refine ⟨g :: ws, ?_, rfl⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hws w hw)

theorem foldr_isTab {ws : List (List ℕ)} (h : ∀ w ∈ ws, IsTab n w) :
    IsTab n (ws.foldr compTab (List.range n)) := by
  induction ws with
  | nil => exact range_isTab
  | cons w ws ih =>
    exact compTab_isTab (h w List.mem_cons_self) (ih fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem spanTabs_isTab {gs : List (List ℕ)} (hg : ∀ g ∈ gs, IsTab n g) :
    ∀ f ∈ spanTabs n gs, IsTab n f := by
  intro f hf
  obtain ⟨ws, hws, rfl⟩ := mem_spanTabs hf
  exact foldr_isTab fun w hw => hg w (hws w hw)

theorem span_mul {gs : List (List ℕ)} (hg : ∀ g ∈ gs, IsTab n g)
    (hcl : ∀ g ∈ gs, ∀ f ∈ spanTabs n gs, compTab g f ∈ spanTabs n gs) :
    ∀ f ∈ spanTabs n gs, ∀ f' ∈ spanTabs n gs, compTab f f' ∈ spanTabs n gs := by
  intro f hf f' hf'
  have hT := spanTabs_isTab hg f' hf'
  obtain ⟨ws, hws, rfl⟩ := mem_spanTabs hf
  clear hf
  induction ws with
  | nil => rw [List.foldr_nil, compTab_range_left hT.2]; exact hf'
  | cons w ws ih =>
    have hws' : ∀ v ∈ ws, v ∈ gs := fun v hv => hws v (List.mem_cons_of_mem _ hv)
    have hW := foldr_isTab (n := n) fun v hv => hg v (hws' v hv)
    rw [List.foldr_cons, compTab_assoc _ _ _ (by rw [hW.1]; exact hT.2)]
    exact hcl w (hws w List.mem_cons_self) _ (ih hws')

theorem span_conj {gs ns : List (List ℕ)} (hg : ∀ g ∈ gs, IsTab n g) (hn : ∀ t ∈ ns, IsTab n t)
    (hcl : ∀ g ∈ gs, ∀ f ∈ spanTabs n gs, compTab g f ∈ spanTabs n gs)
    (hc : ∀ t ∈ ns, ∀ g ∈ gs, ∃ f ∈ spanTabs n gs, compTab t g = compTab f t) :
    ∀ t ∈ ns, ∀ f ∈ spanTabs n gs, ∃ f' ∈ spanTabs n gs, compTab t f = compTab f' t := by
  intro t ht f hf
  have hT := hn t ht
  obtain ⟨ws, hws, rfl⟩ := mem_spanTabs hf
  clear hf
  induction ws with
  | nil =>
    refine ⟨List.range n, range_mem_spanTabs gs, ?_⟩
    rw [List.foldr_nil, compTab_range_right hT.1, compTab_range_left hT.2]
  | cons w ws ih =>
    have hw : w ∈ gs := hws w List.mem_cons_self
    have hws' : ∀ v ∈ ws, v ∈ gs := fun v hv => hws v (List.mem_cons_of_mem _ hv)
    have hW := foldr_isTab (n := n) fun v hv => hg v (hws' v hv)
    obtain ⟨f1, hf1, e1⟩ := ih hws'
    obtain ⟨fw, hfw, ew⟩ := hc t ht w hw
    refine ⟨compTab fw f1, span_mul hg hcl fw hfw f1 hf1, ?_⟩
    rw [List.foldr_cons, ← compTab_assoc t w _ (by rw [(hg w hw).1]; exact hW.2), ew,
      compTab_assoc fw t _ (by rw [hT.1]; exact hW.2), e1,
      compTab_assoc fw f1 t (by rw [(spanTabs_isTab hg f1 hf1).1]; exact hT.2)]

theorem spanOK_sound {gs ns L : List (List ℕ)} (h : spanOK n gs ns L = true) :
    (∀ g ∈ gs, IsTab n g) ∧ (∀ t ∈ ns, IsTab n t) ∧ (∀ g ∈ gs, ∀ f ∈ L, compTab g f ∈ L) ∧
      ∀ t ∈ ns, ∀ g ∈ gs, ∃ f ∈ L, compTab t g = compTab f t := by
  simp only [spanOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    beq_iff_eq, tabOK_iff, and_assoc] at h
  exact h

end CFSG.KC.TabSpan

namespace CFSG.Quasithin.H13.S125KG.M24

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.TabSpan

theorem letTab_isTab (l : ℕ) : IsTab 24 (letTab l) := by
  unfold letTab
  split
  · exact tabOK_iff.1 (by decide)
  · split
    · exact tabOK_iff.1 (by decide)
    · exact range_isTab

theorem wTab_isTab (w : List ℕ) : IsTab 24 (wTab w) := by
  induction w with
  | nil => exact range_isTab
  | cons l w ih => rw [wTab.eq_2]; exact compTab_isTab (letTab_isTab l) ih

theorem wTab_append (u v : List ℕ) : wTab (u ++ v) = compTab (wTab u) (wTab v) := by
  induction u with
  | nil => rw [List.nil_append, wTab.eq_1, compTab_range_left (wTab_isTab v).2]
  | cons l u ih =>
    rw [List.cons_append, wTab.eq_2, wTab.eq_2, ih,
      compTab_assoc _ _ _ (by rw [(wTab_isTab u).1]; exact (wTab_isTab v).2)]

theorem prods_map_wTab (ws : List (List ℕ)) :
    (ws.foldr (fun q acc => acc ++ acc.map (q ++ ·)) [[]]).map wTab =
      spanTabs 24 (ws.map wTab) := by
  induction ws with
  | nil => rfl
  | cons q ws ih =>
    rw [List.foldr_cons, List.map_append, List.map_cons, spanTabs_cons, ← ih, List.map_map,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    exact wTab_append q w

theorem qTabs_eq : qTabs = spanTabs 24 (qws.map wTab) := prods_map_wTab qws

theorem sTabs_eq : m24STabs.map Array.toList = sTabsK := by
  have e : sTabsK = CFSG.Quasithin.A312M24.sTL := rfl
  rw [e, ← CFSG.Quasithin.A312M24.sTL_eq]
  simp only [m24STabs, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro p _
  rw [CFSG.Quasithin.A312M24.getElem!_toList_aux]
  unfold m24SLP
  rw [CFSG.Quasithin.A312M24.slpTabsA_eq]

theorem nTabs_eq : nTabs = sTabsK ++ [wTab w2w] := by
  unfold nTabs
  rw [sTabs_eq]

theorem chkQK_of_chkQF (h : chkQF () = true) : chkQK () = true := by
  simp only [chkQF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hg, hn, hcl, hc⟩ := spanOK_sound h5
  unfold chkQK
  rw [qTabs_eq, nTabs_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem,
    List.any_eq_true, beq_iff_eq, and_assoc]
  exact ⟨h1, fun q hq => h2 _ (List.mem_map_of_mem hq), h3, h4, span_mul hg hcl,
    span_conj hg hn hcl hc⟩

end CFSG.Quasithin.H13.S125KG.M24
