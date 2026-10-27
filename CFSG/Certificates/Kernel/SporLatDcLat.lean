module

public import CFSG.Certificates.Kernel.SporLatDcCoset

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

@[expose] def Y (j : ℕ) : Subgroup Γ :=
  Subgroup.closure {x | x ∈ P.sl.take P.C.ng ++ (P.D.mw.getD j []).map (wordElt P.a P.b)}

private theorem S_le_Y (j : ℕ) : P.S ≤ P.Y j := by
  rw [S, Y, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure (List.mem_append_left _ hx)

private theorem S_le_sup_Y (j j' : ℕ) : P.S ≤ P.Y j ⊔ P.Y j' :=
  le_trans (S_le_Y P j) le_sup_left

private theorem Y_le_sup_left (j j' : ℕ) : P.Y j ≤ P.Y j ⊔ P.Y j' := le_sup_left

private theorem Y_le_sup_right (j j' : ℕ) : P.Y j' ≤ P.Y j ⊔ P.Y j' := le_sup_right

private theorem mul_mem_sup_Y (j j' : ℕ) {a b : Γ} (ha : a ∈ P.Y j ⊔ P.Y j')
    (hb : b ∈ P.Y j ⊔ P.Y j') : a * b ∈ P.Y j ⊔ P.Y j' :=
  Subgroup.mul_mem _ ha hb

private theorem Y_zero : P.Y 0 = P.S := by
  unfold Y
  rw [mw_zero P, List.map_nil, List.append_nil]
  rfl

private theorem mw_all : (P.D.mw.all fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) = true :=
  (global_parts P).2.2.2.2.2.2.2.2.2.1

private theorem mw_letters {j : ℕ} {w : List ℕ} (hw : w ∈ P.D.mw.getD j []) : ∀ l ∈ w, l < 2 := by
  by_cases hj : j < P.D.mw.length
  · have hd : P.D.mw.getD j [] = P.D.mw[j] := List.getD_eq_getElem _ _ hj
    rw [hd] at hw
    have h1 := (List.all_eq_true.mp (mw_all P)) (P.D.mw[j]) (List.getElem_mem hj)
    have h2 := (List.all_eq_true.mp h1) w hw
    intro l hl
    have h3 := (List.all_eq_true.mp h2) l hl
    rwa [Nat.blt_eq] at h3
  · have h0 : P.D.mw.length ≤ j := Nat.le_of_not_lt hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h0] at hw
    exact absurd hw (by simp)

private theorem els_getD_two_add (i : ℕ) : P.els.getD (Nat.add 2 i) 1 = P.sl.getD i 1 := by
  rw [show Nat.add 2 i = 2 + i from rfl, P.els_getD_sl (Nat.le_add_right 2 i)]
  exact congrArg (fun k => P.sl.getD k 1) (Nat.add_sub_cancel_left 2 i)

private theorem sLet_mem_closure (i : ℕ) (hi : i < P.C.ns) :
    evalElt P.els [Nat.add 2 i] ∈ P.S := by
  have hsl : i < P.sl.length := by
    have := P.hsl
    omega
  have he : evalElt P.els [Nat.add 2 i] = P.sl[i] := by
    rw [evalElt_cons, evalElt_nil, mul_one, els_getD_two_add P i, List.getD_eq_getElem P.sl 1 hsl]
  rw [he]
  exact P.hS _ (List.getElem_mem hsl)

private theorem closure_sLet :
    Subgroup.closure {x : Γ | ∃ w ∈ sLet P.C, x = evalElt P.els w} = P.S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    unfold sLet at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sLet_mem_closure P i (List.mem_range.mp hi)
  · rw [S, Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_take] at hxi
    have hi' : i < P.C.ng := by
      have h := hi
      rw [List.length_take] at h
      omega
    have hi'' : i < P.C.ns := by
      have := ng_le_ns P
      omega
    have hsl : i < P.sl.length := by
      have := P.hsl
      omega
    have he : evalElt P.els [Nat.add 2 i] = P.sl[i] := by
      rw [evalElt_cons, evalElt_nil, mul_one, els_getD_two_add P i, List.getD_eq_getElem P.sl 1 hsl]
    refine Subgroup.subset_closure ⟨[Nat.add 2 i], ?_, ?_⟩
    · unfold sLet
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi'', rfl⟩
    · rw [he, ← hxi]

private theorem mem_eMem_iff {j : ℕ} {x : Γ} :
    (∃ v ∈ eMem P.C P.D j, x = evalElt P.els v) ↔
      (∃ v ∈ sLet P.C, x = evalElt P.els v) ∨
        (∃ v ∈ P.D.mw.getD j [], x = evalElt P.els v) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [eMem, List.mem_append] at hv
    rcases hv with hv | hv
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, by rw [eMem, List.mem_append]; exact Or.inl hv, rfl⟩
    · exact ⟨v, by rw [eMem, List.mem_append]; exact Or.inr hv, rfl⟩

private theorem closure_eMem (j : ℕ) :
    Subgroup.closure {x : Γ | ∃ w ∈ eMem P.C P.D j, x = evalElt P.els w} = P.Y j := by
  have h1 : {x : Γ | ∃ w ∈ eMem P.C P.D j, x = evalElt P.els w} =
      {x : Γ | ∃ w ∈ sLet P.C, x = evalElt P.els w} ∪
        {x : Γ | ∃ w ∈ P.D.mw.getD j [], x = evalElt P.els w} := by
    ext x
    exact mem_eMem_iff P
  have h2 : {x : Γ | ∃ w ∈ P.D.mw.getD j [], x = evalElt P.els w} =
      {x : Γ | ∃ w ∈ P.D.mw.getD j [], x = wordElt P.a P.b w} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, P.evalElt_eq_wordElt (mw_letters P hw)⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (P.evalElt_eq_wordElt (mw_letters P hw)).symm⟩
  have h3 : P.Y j =
      Subgroup.closure {x : Γ | ∃ w ∈ P.D.mw.getD j [], x = wordElt P.a P.b w} ⊔ P.S := by
    unfold Y
    have hset : {x : Γ | x ∈ P.sl.take P.C.ng ++ (P.D.mw.getD j []).map (wordElt P.a P.b)} =
        {x : Γ | x ∈ P.sl.take P.C.ng} ∪
          {x : Γ | ∃ w ∈ P.D.mw.getD j [], x = wordElt P.a P.b w} := by
      ext x
      rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, List.mem_append]
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
          exact Or.inr ⟨w, hw, rfl⟩
      · rintro (hx | ⟨w, hw, rfl⟩)
        · exact Or.inl hx
        · exact Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)
    rw [hset, Subgroup.closure_union,
      show Subgroup.closure {x : Γ | x ∈ P.sl.take P.C.ng} = P.S from rfl, sup_comm]
  rw [h1, h2, Subgroup.closure_union, closure_sLet P, h3, sup_comm]

private theorem mem_eAtom_iff {w : List ℕ} {x : Γ} :
    (∃ v ∈ eAtom P.C w, x = evalElt P.els v) ↔
      (∃ v ∈ sLet P.C, x = evalElt P.els v) ∨ x = evalElt P.els w := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [eAtom, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · exact ⟨v, by rw [eAtom, List.mem_append]; exact Or.inl hv, rfl⟩
    · exact ⟨w, by rw [eAtom, List.mem_append]; exact Or.inr (List.mem_singleton_self ..), rfl⟩

private theorem closure_eAtom (w : List ℕ) :
    Subgroup.closure {x : Γ | ∃ v ∈ eAtom P.C w, x = evalElt P.els v} =
      P.S ⊔ Subgroup.closure {evalElt P.els w} := by
  have h1 : {x : Γ | ∃ v ∈ eAtom P.C w, x = evalElt P.els v} =
      {x : Γ | ∃ v ∈ sLet P.C, x = evalElt P.els v} ∪ {evalElt P.els w} := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff,
      mem_eAtom_iff]
  rw [h1, Subgroup.closure_union, closure_sLet P]

private theorem mem_of_lab_eq {g h : Γ} (hl : lab n ptLab P.C.Δ g = lab n ptLab P.C.Δ h) :
    ∃ t ∈ P.S, g = h * t := by
  have h1 : g⁻¹ * h ∈ P.S := by
    rw [← lab_eq_iff_S P]
    exact (lab_eq_iff hlaw P.hΔ g h).mp hl
  refine ⟨(g⁻¹ * h)⁻¹, P.S.inv_mem h1, ?_⟩
  group

private theorem eMem_letters {j : ℕ} {w : List ℕ} (hw : w ∈ eMem P.C P.D j) :
    ∀ l ∈ w, l < 2 + P.C.ns := by
  unfold eMem at hw
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · unfold sLet at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hi' : i < P.C.ns := List.mem_range.mp hi
    intro l hl
    have hl' : l = Nat.add 2 i := List.mem_singleton.mp hl
    subst hl'
    rw [show Nat.add 2 i = 2 + i from rfl]
    omega
  · intro l hl
    have h1 := mw_letters P hw l hl
    omega

private theorem eAtom_letters {w : List ℕ} (hw : ∀ l ∈ w, l < 2 + P.C.ns) {v : List ℕ}
    (hv : v ∈ eAtom P.C w) : ∀ l ∈ v, l < 2 + P.C.ns := by
  unfold eAtom at hv
  rw [List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · unfold sLet at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hi' : i < P.C.ns := List.mem_range.mp hi
    intro l hl
    have hl' : l = Nat.add 2 i := List.mem_singleton.mp hl
    subst hl'
    rw [show Nat.add 2 i = 2 + i from rfl]
    omega
  · intro l hl
    exact hw l hl

private theorem memW_mem_Y {j : ℕ} {x : Wit} {T : List ℕ}
    (h : memW P.C (eMem P.C P.D j) x T = true) :
    ∃ s ∈ P.S, ∃ u ∈ P.Y j, lab n ptLab P.C.Δ (s * u) = T := by
  obtain ⟨s, hs, u, hu, hlab⟩ := memW_sound P (fun w hw => eMem_letters P hw) h
  refine ⟨s, hs, u, ?_, hlab⟩
  rwa [closure_eMem P j] at hu

private theorem memW_mem_sup {w : List ℕ} (hw : isW P.C w = true) {x : Wit} {T : List ℕ}
    (h : memW P.C (eAtom P.C w) x T = true) :
    ∃ s ∈ P.S, ∃ u ∈ P.S ⊔ Subgroup.closure {evalElt P.els w},
      lab n ptLab P.C.Δ (s * u) = T := by
  obtain ⟨s, hs, u, hu, hlab⟩ := memW_sound P (fun v hv => eAtom_letters P (isW_lt P hw) hv) h
  refine ⟨s, hs, u, ?_, hlab⟩
  rwa [closure_eAtom P w] at hu

private theorem evalElt_mem_Y {r : Rep} {j : ℕ} (hr : repOK P.C P.D r)
    {x : Wit} (h : memW P.C (eMem P.C P.D j) x r.lab = true) :
    evalElt P.els r.w ∈ P.Y j := by
  obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_Y P h
  have hlab' : lab n ptLab P.C.Δ (evalElt P.els r.w) = lab n ptLab P.C.Δ (s * u) := by
    rw [hlab, rep_lab_eq P hr]
  obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab'
  rw [hgt]
  exact Subgroup.mul_mem (P.Y j) (Subgroup.mul_mem (P.Y j) (S_le_Y P j hs) hu) (S_le_Y P j ht)

private theorem all2_length_eq {α β : Type} {f : α → β → Bool} :
    ∀ (l : List α) (m : List β), all2 f l m = true → l.length = m.length
  | [], [], _ => by simp
  | _ :: l, _ :: m, h => by
    simp only [all2, Bool.and_eq_true] at h
    rw [List.length_cons, List.length_cons, all2_length_eq l m h.2]
  | [], _ :: _, h => by simp [all2] at h
  | _ :: _, [], h => by simp [all2] at h

private theorem all2_spec {α β : Type} {f : α → β → Bool} :
    ∀ (l : List α) (m : List β), all2 f l m = true →
      ∀ i (hi : i < l.length) (hj : i < m.length), f l[i] m[i] = true
  | [], [], _, i, hi, _ => by simp at hi
  | _ :: _, _ :: _, h, 0, _, _ => by
    simp only [all2, Bool.and_eq_true] at h
    exact h.1
  | _ :: l, _ :: m, h, i + 1, hi, hj => by
    simp only [all2, Bool.and_eq_true] at h
    have hi' : i < l.length := by simpa using hi
    have hj' : i < m.length := by simpa using hj
    simpa using all2_spec l m h.2 i hi' hj'
  | [], _ :: _, h, _, _, _ => by simp [all2] at h
  | _ :: _, [], h, _, _, _ => by simp [all2] at h

private theorem gensW_mem {E : List (List ℕ)} {ws : List Wit} {gs : List (List ℕ)}
    (h : gensW P.C E ws gs = true) {g : List ℕ} (hg : g ∈ gs) :
    ∃ x ∈ ws, memW P.C E x (genLab P.C g) = true := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlen : ws.length = gs.length := all2_length_eq ws gs h
  have hi' : i < ws.length := by rw [hlen]; exact hi
  have h1 := all2_spec (f := fun x g => memW P.C E x (genLab P.C g)) ws gs h i hi' hi
  exact ⟨ws[i], List.getElem_mem hi', h1⟩

private theorem genLab_eq {g : List ℕ} (hg : ∀ l ∈ g, l < 2 + P.C.ns) :
    genLab P.C g = lab n ptLab P.C.Δ (evalElt P.els g) :=
  P.labF_eq_lab hg

private theorem evalElt_mem_sup {r : Rep} (hwis : isW P.C r.w = true) {ws : List Wit}
    {gs : List (List ℕ)} (h : gensW P.C (eAtom P.C r.w) ws gs = true) {g : List ℕ}
    (hg : g ∈ gs) (hgl : ∀ l ∈ g, l < 2 + P.C.ns) :
    evalElt P.els g ∈ P.S ⊔ Subgroup.closure {evalElt P.els r.w} := by
  obtain ⟨x, hx, hxT⟩ := gensW_mem P h hg
  obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_sup P hwis hxT
  have hlab2 : lab n ptLab P.C.Δ (s * u) = lab n ptLab P.C.Δ (evalElt P.els g) := by
    rw [hlab, genLab_eq P hgl]
  obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab2
  have hsup : evalElt P.els g = (s * u) * t⁻¹ := by
    rw [hgt]
    group
  rw [hsup]
  exact (P.S ⊔ Subgroup.closure {evalElt P.els r.w}).mul_mem
    ((P.S ⊔ Subgroup.closure {evalElt P.els r.w}).mul_mem
      (Subgroup.mem_sup_left hs) hu)
    (Subgroup.mem_sup_left (P.S.inv_mem ht))

private theorem refR_mem_recs {c : ℕ} (h : refOK P.D c = true) : refR P.D c ∈ P.recs := by
  have h := h
  unfold refOK at h
  rw [show Nat.div c P.D.csz = c / P.D.csz from rfl,
    show Nat.mod c P.D.csz = c % P.D.csz from rfl,
    Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hchunk : P.D.Rc.getD (c / P.D.csz) [] = P.D.Rc[c / P.D.csz] :=
    List.getD_eq_getElem _ _ h1
  have h2' : c % P.D.csz < (P.D.Rc[c / P.D.csz]).length := by rwa [hchunk] at h2
  have hrec : refR P.D c = (P.D.Rc[c / P.D.csz])[c % P.D.csz] := by
    unfold refR
    rw [show Nat.div c P.D.csz = c / P.D.csz from rfl,
      show Nat.mod c P.D.csz = c % P.D.csz from rfl, hchunk,
      List.getD_eq_getElem _ _ h2']
  rw [hrec]
  unfold recs
  exact List.mem_flatten.mpr
    ⟨P.D.Rc[c / P.D.csz], List.getElem_mem h1, List.getElem_mem h2'⟩

private theorem refR_repOK {c : ℕ} (h : refOK P.D c = true) : repOK P.C P.D (refR P.D c) = true :=
  mem_recs_repOK P (refR_mem_recs P h)

private def AtomProp (r : Rep) : Prop :=
  evalElt P.els r.w ∈ memberOrTop P.D.mw.length P.Y r.cls ∧
    ∀ Z : Subgroup Γ, P.S ≤ Z → evalElt P.els r.w ∈ Z →
      memberOrTop P.D.mw.length P.Y r.cls ≤ Z

private theorem memW_mem_of_sup {g : Γ} {T : List ℕ} {w : List ℕ}
    (h : ∃ s ∈ P.S, ∃ u ∈ P.S ⊔ Subgroup.closure {evalElt P.els w}, lab n ptLab P.C.Δ (s * u) = T)
    (hT : T = lab n ptLab P.C.Δ g) :
    g ∈ P.S ⊔ Subgroup.closure {evalElt P.els w} := by
  obtain ⟨s, hs, u, hu, hlab⟩ := h
  have hlab' : lab n ptLab P.C.Δ (s * u) = lab n ptLab P.C.Δ g := by rw [hlab, hT]
  obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab'
  have hsup : g = (s * u) * t⁻¹ := by rw [hgt]; group
  rw [hsup]
  exact (P.S ⊔ Subgroup.closure {evalElt P.els w}).mul_mem
    ((P.S ⊔ Subgroup.closure {evalElt P.els w}).mul_mem
      (Subgroup.mem_sup_left hs) hu)
    (Subgroup.mem_sup_left (P.S.inv_mem ht))

private theorem atom_prop_member {r : Rep} (hr : r ∈ P.recs)
    (hcls : Nat.blt r.cls P.D.mw.length = true)
    {x : Wit} {gs : List Wit} (hwits : r.wits = x :: gs)
    (h1 : memW P.C (eMem P.C P.D r.cls) x r.lab = true)
    (h2 : gensW P.C (eAtom P.C r.w) gs (P.D.mw.getD r.cls []) = true) :
    AtomProp P r := by
  have hrOK := mem_recs_repOK P hr
  have hisW : isW P.C r.w = true := (repOK_parts P hrOK).1
  have hjJ : r.cls < P.D.mw.length := by rwa [Nat.blt_eq] at hcls
  have hmem : memberOrTop P.D.mw.length P.Y r.cls = P.Y r.cls := by
    unfold memberOrTop
    rw [if_pos hjJ]
  refine ⟨?_, ?_⟩
  · rw [hmem]
    exact evalElt_mem_Y P hrOK h1
  · intro Z hSZ hrep
    rw [hmem]
    have hsup_le : P.S ⊔ Subgroup.closure {evalElt P.els r.w} ≤ Z := by
      refine sup_le hSZ ?_
      rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hrep
    rw [Y, Subgroup.closure_le]
    intro y hy
    rw [Set.mem_setOf_eq] at hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact hSZ (Subgroup.subset_closure hy)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
      rw [← P.evalElt_eq_wordElt (mw_letters P hw)]
      have hgl : ∀ l ∈ w, l < 2 + P.C.ns := by
        intro l hl
        have := mw_letters P hw l hl
        omega
      exact hsup_le (evalElt_mem_sup P hisW h2 hw hgl)

private theorem genLab_zero : genLab P.C [0] = lab n ptLab P.C.Δ P.a := by
  have h1 : genLab P.C [0] = lab n ptLab P.C.Δ (evalElt P.els [0]) :=
    P.labF_eq_lab (by intro l hl; rw [List.mem_singleton] at hl; subst hl; omega)
  rw [h1]
  congr 1
  rw [evalElt_cons, evalElt_nil, mul_one, P.els_getD]
  rfl

private theorem genLab_one : genLab P.C [1] = lab n ptLab P.C.Δ P.b := by
  have h1 : genLab P.C [1] = lab n ptLab P.C.Δ (evalElt P.els [1]) :=
    P.labF_eq_lab (by intro l hl; rw [List.mem_singleton] at hl; subst hl; omega)
  rw [h1]
  congr 1
  rw [evalElt_cons, evalElt_nil, mul_one, P.els_getD]
  rfl

private theorem topW_spec {E : List (List ℕ)} {ok : ℕ → Bool} {ws : List Wit}
    (h : topW P.C P.D E ok ws = true) :
    (∃ x : Wit, ws = [x] ∧ 2 ≤ x.2.2 ∧ refOK P.D (x.2.2 - 2) = true ∧
        (refR P.D (x.2.2 - 2)).cls = P.D.mw.length ∧ ok (x.2.2 - 2) = true ∧
        memW P.C E x (refR P.D (x.2.2 - 2)).lab = true) ∨
      (∃ x y : Wit, ws = [x, y] ∧ x.2.2 = 0 ∧ y.2.2 = 1 ∧
        memW P.C E x (genLab P.C [0]) = true ∧ memW P.C E y (genLab P.C [1]) = true) := by
  rcases ws with _ | ⟨x, ws⟩
  · simp [topW] at h
  · rcases ws with _ | ⟨y, ws⟩
    · unfold topW at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Nat.ble_eq, Nat.beq_eq] at h
      exact Or.inl ⟨x, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
    · rcases ws with _ | ⟨z, ws⟩
      · unfold topW at h
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Nat.beq_eq, Nat.beq_eq] at h
        exact Or.inr ⟨x, y, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · unfold topW at h
        simp at h

private theorem sup_le_of_mem {r : Rep} {Z : Subgroup Γ} (hSZ : P.S ≤ Z)
    (hrep : evalElt P.els r.w ∈ Z) :
    P.S ⊔ Subgroup.closure {evalElt P.els r.w} ≤ Z := by
  refine sup_le hSZ ?_
  rw [Subgroup.closure_le]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hrep

private theorem atom_prop_top_ref {r : Rep} {Z : Subgroup Γ}
    (hsup_le : P.S ⊔ Subgroup.closure {evalElt P.els r.w} ≤ Z)
    (hSZ : P.S ≤ Z) (hisW : isW P.C r.w = true)
    (ih : ∀ (r' : Rep), r' ∈ P.recs → r'.rank < r.rank → AtomProp P r')
    {c' : ℕ} (hrefOK : refOK P.D c' = true)
    (hclsJ : (refR P.D c').cls = P.D.mw.length)
    (hrank' : (refR P.D c').rank < r.rank)
    {x : Wit} (hmemW : memW P.C (eAtom P.C r.w) x (refR P.D c').lab = true) :
    ⊤ ≤ Z := by
  have hr' : refR P.D c' ∈ P.recs := refR_mem_recs P hrefOK
  have hr'OK := mem_recs_repOK P hr'
  have hrefZ : evalElt P.els (refR P.D c').w ∈ Z := by
    have h1 : ∃ s ∈ P.S, ∃ u ∈ P.S ⊔ Subgroup.closure {evalElt P.els r.w},
        lab n ptLab P.C.Δ (s * u) = (refR P.D c').lab :=
      memW_mem_sup P hisW hmemW
    rw [rep_lab_eq P hr'OK] at h1
    exact hsup_le (memW_mem_of_sup P h1 rfl)
  have h2 := (ih (refR P.D c') hr' hrank').2 Z hSZ hrefZ
  have h3 : memberOrTop P.D.mw.length P.Y (refR P.D c').cls = ⊤ := by
    unfold memberOrTop
    rw [hclsJ, if_neg (by omega)]
  rwa [h3] at h2

private theorem atom_prop_top_letters {r : Rep} {Z : Subgroup Γ}
    (hsup_le : P.S ⊔ Subgroup.closure {evalElt P.els r.w} ≤ Z)
    (hisW : isW P.C r.w = true) {x y : Wit}
    (hmemx : memW P.C (eAtom P.C r.w) x (genLab P.C [0]) = true)
    (hmemy : memW P.C (eAtom P.C r.w) y (genLab P.C [1]) = true) :
    ⊤ ≤ Z := by
  have ha : P.a ∈ Z := by
    have h1 := memW_mem_sup P hisW hmemx
    rw [genLab_zero P] at h1
    exact hsup_le (memW_mem_of_sup P h1 rfl)
  have hb : P.b ∈ Z := by
    have h1 := memW_mem_sup P hisW hmemy
    rw [genLab_one P] at h1
    exact hsup_le (memW_mem_of_sup P h1 rfl)
  rw [← P.gen, Subgroup.closure_le]
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

private theorem atom_prop_top {r : Rep} (hr : r ∈ P.recs) (hJ : r.cls = P.D.mw.length)
    (htop : topW P.C P.D (eAtom P.C r.w)
      (fun c' => Nat.blt (refR P.D c').rank r.rank) r.wits = true)
    (ih : ∀ (r' : Rep), r' ∈ P.recs → r'.rank < r.rank → AtomProp P r') :
    AtomProp P r := by
  have hrOK := mem_recs_repOK P hr
  have hisW : isW P.C r.w = true := (repOK_parts P hrOK).1
  have hmem : memberOrTop P.D.mw.length P.Y r.cls = ⊤ := by
    unfold memberOrTop
    rw [if_neg (by omega)]
  refine ⟨?_, ?_⟩
  · rw [hmem]
    exact Subgroup.mem_top _
  · intro Z hSZ hrep
    rw [hmem]
    have hsup_le := sup_le_of_mem P hSZ hrep
    rcases topW_spec P htop with ⟨x, _, -, hrefOK, hclsJ, hrank, hmemW⟩ |
      ⟨x, y, _, _, _, hmemx, hmemy⟩
    · exact atom_prop_top_ref P hsup_le hSZ hisW ih hrefOK hclsJ
        (by rwa [Nat.blt_eq] at hrank) hmemW
    · exact atom_prop_top_letters P hsup_le hisW hmemx hmemy

private theorem atom_prop_aux : ∀ (ρ : ℕ) (r : Rep), r ∈ P.recs → r.rank = ρ → AtomProp P r := by
  intro ρ
  induction ρ using Nat.strong_induction_on with
  | h ρ ih =>
    intro r hr hρ
    have hrOK := mem_recs_repOK P hr
    have hatom : atomR P.C P.D r = true := by
      have h := hrOK
      unfold repOK at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      exact h.2
    unfold atomR at hatom
    cases hcls : Nat.blt r.cls P.D.mw.length with
    | true =>
      rw [hcls] at hatom
      simp only [cond_true] at hatom
      cases hwits : r.wits with
      | nil => rw [hwits] at hatom; simp at hatom
      | cons x gs =>
        rw [hwits, Bool.and_eq_true] at hatom
        exact atom_prop_member P hr hcls hwits hatom.1 hatom.2
    | false =>
      rw [hcls] at hatom
      simp only [cond_false, Bool.and_eq_true, Nat.beq_eq] at hatom
      refine atom_prop_top P hr hatom.1 hatom.2 ?_
      intro r' hr' hrank'
      exact ih r'.rank (by rwa [hρ] at hrank') r' hr' rfl

private theorem atom_prop {r : Rep} (hr : r ∈ P.recs) : AtomProp P r :=
  atom_prop_aux P r.rank r hr rfl

private theorem eJoin_letters {j j' : ℕ} {w : List ℕ} (hw : w ∈ eJoin P.C P.D j j') :
    ∀ l ∈ w, l < 2 + P.C.ns := by
  unfold eJoin at hw
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · unfold sLet at hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hi' : i < P.C.ns := List.mem_range.mp hi
      intro l hl
      rw [List.mem_singleton] at hl
      subst hl
      rw [show Nat.add 2 i = 2 + i from rfl]
      omega
    · intro l hl
      have := mw_letters P hw l hl
      omega
  · intro l hl
    have := mw_letters P hw l hl
    omega

private theorem memW_mem_of_le {E : List (List ℕ)} {H : Subgroup Γ}
    (hE : Subgroup.closure {x : Γ | ∃ w ∈ E, x = evalElt P.els w} ≤ H)
    (hEl : ∀ w ∈ E, ∀ l ∈ w, l < 2 + P.C.ns)
    {x : Wit} {T : List ℕ} (h : memW P.C E x T = true) :
    ∃ s ∈ P.S, ∃ u ∈ H, lab n ptLab P.C.Δ (s * u) = T := by
  obtain ⟨s, hs, u, hu, hlab⟩ := memW_sound P hEl h
  exact ⟨s, hs, u, hE hu, hlab⟩

private theorem eJoin_subset_sup {j j' : ℕ} :
    Subgroup.closure {x : Γ | ∃ w ∈ eJoin P.C P.D j j', x = evalElt P.els w} ≤
      P.Y j ⊔ P.Y j' := by
  rw [Subgroup.closure_le]
  rintro x ⟨w, hw, rfl⟩
  unfold eJoin at hw
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · unfold sLet at hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Y_le_sup_left P j j' (S_le_Y P j (sLet_mem_closure P i (List.mem_range.mp hi)))
    · rw [P.evalElt_eq_wordElt (mw_letters P hw)]
      exact Y_le_sup_left P j j' (Subgroup.subset_closure
        (List.mem_append_right _ (List.mem_map.mpr ⟨w, hw, rfl⟩)))
  · rw [P.evalElt_eq_wordElt (mw_letters P hw)]
    exact Y_le_sup_right P j j' (Subgroup.subset_closure
      (List.mem_append_right _ (List.mem_map.mpr ⟨w, hw, rfl⟩)))

private theorem Y_le_sup_of_eJoin {j j' jj : ℕ} {ws : List Wit}
    (h : gensW P.C (eJoin P.C P.D j j') ws (P.D.mw.getD jj []) = true) :
    P.Y jj ≤ P.Y j ⊔ P.Y j' := by
  rw [Y, Subgroup.closure_le]
  intro x hx
  rw [Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · exact Y_le_sup_left P j j' (Subgroup.subset_closure (List.mem_append_left _ hx))
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    rw [← P.evalElt_eq_wordElt (mw_letters P hw)]
    obtain ⟨x', hx', hx'm⟩ := gensW_mem P h hw
    obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_of_le P (eJoin_subset_sup P)
      (fun w hw => eJoin_letters P hw) hx'm
    have hlab' : lab n ptLab P.C.Δ (s * u) = lab n ptLab P.C.Δ (evalElt P.els w) := by
      rw [hlab, genLab_eq P (fun l hl => by
        have := mw_letters P hw l hl; omega)]
    obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab'.symm
    rw [hgt]
    exact mul_mem_sup_Y P j j'
      (Subgroup.mul_mem (P.Y j ⊔ P.Y j') (S_le_sup_Y P j j' hs) hu)
      (S_le_sup_Y P j j' ht)

private theorem Y_le_Y_of_gens {j jj : ℕ} {ws : List Wit}
    (h : gensW P.C (eMem P.C P.D jj) ws (P.D.mw.getD j []) = true) :
    P.Y j ≤ P.Y jj := by
  rw [Y, Subgroup.closure_le]
  intro x hx
  rw [Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · exact S_le_Y P jj (Subgroup.subset_closure hx)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    rw [← P.evalElt_eq_wordElt (mw_letters P hw)]
    obtain ⟨x', hx', hx'm⟩ := gensW_mem P h hw
    obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_Y P hx'm
    have hlab' : lab n ptLab P.C.Δ (s * u) = lab n ptLab P.C.Δ (evalElt P.els w) := by
      rw [hlab, genLab_eq P (fun l hl => by
        have := mw_letters P hw l hl; omega)]
    obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab'.symm
    rw [hgt]
    exact Subgroup.mul_mem (P.Y jj) (Subgroup.mul_mem (P.Y jj) (S_le_Y P jj hs) hu)
      (S_le_Y P jj ht)

private theorem pairsL_mem {J j j' : ℕ} : (j, j') ∈ pairsL J ↔ j < j' ∧ j' < J := by
  unfold pairsL
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hb⟩
    rw [List.mem_map] at hb
    obtain ⟨b, hb, hje⟩ := hb
    rw [List.mem_range] at ha
    rw [List.mem_range'] at hb
    obtain ⟨k, hk, hbk⟩ := hb
    simp only [Prod.mk.injEq] at hje
    obtain ⟨rfl, rfl⟩ := hje
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨j, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨j', ?_, rfl⟩⟩
    rw [List.mem_range']
    exact ⟨j' - (j + 1), by omega, by omega⟩

private theorem exists_join {j j' : ℕ} (h : (j, j') ∈ pairsL P.D.mw.length) :
    ∃ e ∈ P.D.joins, e.1 = j ∧ e.2.1 = j' := by
  have hmap : (j, j') ∈ P.D.joins.map (fun e => (e.1, e.2.1)) := by
    rw [joins_pairs P]
    exact h
  rw [List.mem_map] at hmap
  obtain ⟨e, he, hje⟩ := hmap
  exact ⟨e, he, (Prod.mk.inj hje).1, (Prod.mk.inj hje).2⟩

private theorem memberOrTop_lt {j : ℕ} (h : j < P.D.mw.length) :
    memberOrTop P.D.mw.length P.Y j = P.Y j := by
  unfold memberOrTop
  rw [if_pos h]

private theorem memberOrTop_top : memberOrTop P.D.mw.length P.Y P.D.mw.length = ⊤ := by
  unfold memberOrTop
  rw [if_neg (by omega)]

private theorem sup_top_of_topW {j j' : ℕ} {ws : List Wit}
    (h : topW P.C P.D (eJoin P.C P.D j j') (fun _ => true) ws = true) :
    P.Y j ⊔ P.Y j' = ⊤ := by
  have hsup_le : P.S ≤ P.Y j ⊔ P.Y j' := S_le_sup_Y P j j'
  rcases topW_spec P h with ⟨x, hws, -, hrefOK, hclsJ, -, hmemW⟩ |
    ⟨x, y, hws, hx0, hy1, hmemx, hmemy⟩
  · have hrefZ : evalElt P.els (refR P.D (x.2.2 - 2)).w ∈ P.Y j ⊔ P.Y j' := by
      obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_of_le P (eJoin_subset_sup P)
        (fun w hw => eJoin_letters P hw) hmemW
      rw [rep_lab_eq P (refR_repOK P hrefOK)] at hlab
      obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab.symm
      rw [hgt]
      exact mul_mem_sup_Y P j j'
        (Subgroup.mul_mem _ (S_le_sup_Y P j j' hs) hu) (S_le_sup_Y P j j' ht)
    have hIH := atom_prop P (refR_mem_recs P hrefOK)
    have h2 := hIH.2 (P.Y j ⊔ P.Y j') hsup_le hrefZ
    rw [hclsJ, memberOrTop_top] at h2
    exact eq_top_iff.mpr h2
  · have ha : P.a ∈ P.Y j ⊔ P.Y j' := by
      obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_of_le P (eJoin_subset_sup P)
        (fun w hw => eJoin_letters P hw) hmemx
      rw [genLab_zero P] at hlab
      obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab.symm
      rw [hgt]
      exact mul_mem_sup_Y P j j'
        (Subgroup.mul_mem _ (S_le_sup_Y P j j' hs) hu) (S_le_sup_Y P j j' ht)
    have hb : P.b ∈ P.Y j ⊔ P.Y j' := by
      obtain ⟨s, hs, u, hu, hlab⟩ := memW_mem_of_le P (eJoin_subset_sup P)
        (fun w hw => eJoin_letters P hw) hmemy
      rw [genLab_one P] at hlab
      obtain ⟨t, ht, hgt⟩ := mem_of_lab_eq P hlab.symm
      rw [hgt]
      exact mul_mem_sup_Y P j j'
        (Subgroup.mul_mem _ (S_le_sup_Y P j j' hs) hu) (S_le_sup_Y P j j' ht)
    rw [eq_top_iff, ← P.gen, Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb

private theorem joinOK_spec {e : Join} (h : joinOK P.C P.D e = true) :
    e.2.2.1 ≤ P.D.mw.length ∧
      ((e.2.2.1 < P.D.mw.length ∧
          gensW P.C (eMem P.C P.D e.2.2.1) e.2.2.2.1 (P.D.mw.getD e.1 []) = true ∧
          gensW P.C (eMem P.C P.D e.2.2.1) e.2.2.2.2.1 (P.D.mw.getD e.2.1 []) = true ∧
          gensW P.C (eJoin P.C P.D e.1 e.2.1) e.2.2.2.2.2 (P.D.mw.getD e.2.2.1 []) = true) ∨
        (e.2.2.1 = P.D.mw.length ∧
          topW P.C P.D (eJoin P.C P.D e.1 e.2.1) (fun _ => true) e.2.2.2.2.2 = true)) := by
  unfold joinOK at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hjle, hrest⟩ := h
  refine ⟨hjle, ?_⟩
  by_cases hlt : Nat.blt e.2.2.1 P.D.mw.length = true
  · left
    rw [hlt, cond_true, Bool.and_eq_true, Bool.and_eq_true] at hrest
    exact ⟨by rwa [Nat.blt_eq] at hlt, hrest.1.1, hrest.1.2, hrest.2⟩
  · right
    have hfl : Nat.blt e.2.2.1 P.D.mw.length = false := by
      rw [Bool.eq_false_iff]
      exact hlt
    rw [hfl, cond_false] at hrest
    have hge : P.D.mw.length ≤ e.2.2.1 := by
      have h1 : ¬ (e.2.2.1 < P.D.mw.length) := by
        rw [← Nat.blt_eq]
        rw [hfl]
        exact Bool.false_ne_true
      omega
    exact ⟨Nat.le_antisymm hjle hge, hrest⟩

private theorem Y_join_pair {j j' : ℕ} (h : (j, j') ∈ pairsL P.D.mw.length) :
    ∃ jj ≤ P.D.mw.length, memberOrTop P.D.mw.length P.Y j ⊔
      memberOrTop P.D.mw.length P.Y j' = memberOrTop P.D.mw.length P.Y jj := by
  obtain ⟨e, he, he1, he2⟩ := exists_join P h
  obtain ⟨hjle, hspec⟩ := joinOK_spec P (joins_ok P e he)
  have hjJ : j < P.D.mw.length := (pairsL_mem.mp h).1.trans (pairsL_mem.mp h).2
  have hj'J : j' < P.D.mw.length := (pairsL_mem.mp h).2
  rw [memberOrTop_lt P hjJ, memberOrTop_lt P hj'J]
  rw [he1, he2] at hspec
  rcases hspec with ⟨hlt, hg1, hg2, hg3⟩ | ⟨hjjJ, htopW⟩
  · refine ⟨e.2.2.1, hjle, ?_⟩
    rw [memberOrTop_lt P hlt]
    exact le_antisymm (sup_le (Y_le_Y_of_gens P hg1) (Y_le_Y_of_gens P hg2))
      (Y_le_sup_of_eJoin P hg3)
  · refine ⟨P.D.mw.length, le_rfl, ?_⟩
    rw [memberOrTop_top, sup_top_of_topW P htopW]

private theorem Y_join {j j' : ℕ} (hj : j ≤ P.D.mw.length) (hj' : j' ≤ P.D.mw.length) :
    ∃ jj ≤ P.D.mw.length, memberOrTop P.D.mw.length P.Y j ⊔
      memberOrTop P.D.mw.length P.Y j' = memberOrTop P.D.mw.length P.Y jj := by
  rcases lt_or_eq_of_le hj' with hj'J | hj'J
  ·
    rcases lt_or_eq_of_le hj with hjJ | hjJ
    ·
      rcases lt_trichotomy j j' with hlt | heq | hgt
      · exact Y_join_pair P (pairsL_mem.mpr ⟨hlt, hj'J⟩)
      · subst heq
        refine ⟨j, le_of_lt hjJ, ?_⟩
        rw [memberOrTop_lt P hjJ, sup_idem]
      · have h := Y_join_pair P (pairsL_mem.mpr ⟨hgt, hjJ⟩)
        rw [sup_comm]
        exact h
    ·
      subst hjJ
      refine ⟨P.D.mw.length, le_rfl, ?_⟩
      rw [memberOrTop_top, memberOrTop_lt P hj'J]
      exact le_antisymm (le_top : ⊤ ⊔ P.Y j' ≤ ⊤) (le_sup_left : ⊤ ≤ ⊤ ⊔ P.Y j')
  ·
    subst hj'J
    rcases lt_or_eq_of_le hj with hjJ | hjJ
    · refine ⟨P.D.mw.length, le_rfl, ?_⟩
      rw [memberOrTop_top, memberOrTop_lt P hjJ]
      exact le_antisymm (le_top : P.Y j ⊔ ⊤ ≤ ⊤) (le_sup_right : ⊤ ≤ P.Y j ⊔ ⊤)
    · subst hjJ
      refine ⟨P.D.mw.length, le_rfl, ?_⟩
      rw [memberOrTop_top]
      exact le_antisymm (le_top : ⊤ ⊔ ⊤ ≤ ⊤) (le_sup_left : ⊤ ≤ ⊤ ⊔ ⊤)

private theorem mem_recs_atomR {r : Rep} (hr : r ∈ P.recs) (hcls : ¬ r.cls < P.D.mw.length) :
    r.cls = P.D.mw.length := by
  have hrOK := mem_recs_repOK P hr
  have hatom : atomR P.C P.D r = true := by
    have h := hrOK
    unfold repOK at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    exact h.2
  unfold atomR at hatom
  have hfl : Nat.blt r.cls P.D.mw.length = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hcls (by rwa [← Nat.blt_eq])
  rw [hfl, cond_false, Bool.and_eq_true, Nat.beq_eq] at hatom
  exact hatom.1

theorem family_complete_apply :
    ∀ Z : Subgroup Γ, P.S ≤ Z →
      ∃ j ≤ P.D.mw.length, Z = memberOrTop P.D.mw.length P.Y j := by
  let R : ℕ := P.recs.length
  let rep : ℕ → Γ := fun c => if h : c < R then evalElt P.els (P.recs[c]).w else 1
  let jc : ℕ → ℕ := fun c => if h : c < R then (P.recs[c]).cls else P.D.mw.length
  have hrep : ∀ c (h : c < R), rep c = evalElt P.els (P.recs[c]).w := by
    intro c h
    unfold rep
    rw [dif_pos h]
  have hjc : ∀ c (h : c < R), jc c = (P.recs[c]).cls := by
    intro c h
    unfold jc
    rw [dif_pos h]
  have hcover : ∀ g : Γ, ∃ c < R, ∃ s ∈ P.S, ∃ t ∈ P.S, g = s * rep c * t := by
    intro g
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := cover_rec P g
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp hr
    exact ⟨c, hc, s, hs, t, ht, by rw [hrep c hc]⟩
  have hatom : ∀ c < R, jc c ≤ P.D.mw.length ∧
      rep c ∈ memberOrTop P.D.mw.length P.Y (jc c) ∧
      ∀ Z : Subgroup Γ, P.S ≤ Z → rep c ∈ Z →
        memberOrTop P.D.mw.length P.Y (jc c) ≤ Z := by
    intro c hc
    obtain ⟨hmem, hmin⟩ := atom_prop P (List.getElem_mem hc)
    have hcls_le : (P.recs[c]).cls ≤ P.D.mw.length := by
      by_cases hlt : (P.recs[c]).cls < P.D.mw.length
      · omega
      · rw [mem_recs_atomR P (List.getElem_mem hc) hlt]
    refine ⟨by rw [hjc c hc]; exact hcls_le, ?_, ?_⟩
    · rw [hrep c hc, hjc c hc]
      exact hmem
    · intro Z hSZ hZ
      rw [hrep c hc] at hZ
      rw [hjc c hc]
      exact hmin Z hSZ hZ
  exact family_complete P.D.mw.length P.Y R rep jc (fun j _ => S_le_Y P j)
    ⟨mw_length_pos P, Y_zero P⟩ hcover hatom (fun j hj j' hj' => Y_join P (le_of_lt hj) hj')

end DcSoundCtx

end CFSG.KC.SLDc

end
