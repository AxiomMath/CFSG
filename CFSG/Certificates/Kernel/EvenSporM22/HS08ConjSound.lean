module

public import Certificates.Data.Kernel.EvenSporM22.HS08ConjDefs

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.HS08Check

def hs08TabF (f : Fin 22 → Fin 22) : Tab := List.ofFn fun i => (f i).val

theorem hs08length_tabF (f : Fin 22 → Fin 22) : (hs08TabF f).length = 22 := by
  simp only [hs08TabF, List.length_ofFn]

theorem hs08getD_tabF (f : Fin 22 → Fin 22) (j : Fin 22) :
    (hs08TabF f).getD j.val 0 = (f j).val := by
  rw [List.getD_eq_getElem _ _ (by rw [hs08length_tabF]; exact j.2)]
  simp only [hs08TabF, List.getElem_ofFn]

theorem hs08TabF_comp (f g : Fin 22 → Fin 22) :
    hs08TabF (f ∘ g) = tmul (hs08TabF f) (hs08TabF g) := by
  simp only [tmul, hs08TabF, List.map_ofFn]
  congr 1
  funext i
  have := hs08getD_tabF f (g i)
  simp only [hs08TabF] at this
  simp only [Function.comp_apply, this]

theorem hs08TabF_injective : Function.Injective hs08TabF := by
  intro f g h
  have := List.ofFn_injective h
  funext i
  exact Fin.ext (congrFun this i)

theorem hs08TabF_id : hs08TabF id = idTab := by
  decide

theorem hs08exists_tabF {t : Tab} (h : hs08TabV t = true) : ∃ f, hs08TabF f = t := by
  simp only [hs08TabV, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hlt⟩ := h
  refine ⟨fun i => ⟨t[i.val]'(by rw [hl]; exact i.2), hlt _ (List.getElem_mem _)⟩, ?_⟩
  apply List.ext_getElem
  · rw [hs08length_tabF, hl]
  · intro n h1 h2
    simp only [hs08TabF, List.getElem_ofFn]

theorem hs08lt_of_tabF (f : Fin 22 → Fin 22) : ∀ e ∈ hs08TabF f, e < 32 := by
  intro e he
  simp only [hs08TabF, List.mem_ofFn] at he
  obtain ⟨i, hi⟩ := he
  have h1 : e = (f i).val := hi.symm
  have := (f i).isLt
  omega

theorem hs08fld_zero : ∀ j, hs08Fld 0 j = 0
  | 0 => rfl
  | j + 1 => by
    simp only [hs08Fld, Nat.zero_div]
    exact hs08fld_zero j

theorem hs08fld_pk : ∀ (t : Tab) (j : Nat), (∀ e ∈ t, e < 32) → hs08Fld (hs08Pk t) j = t.getD j 0
  | [], j, _ => by
    simp only [hs08Pk, List.foldr_nil, List.getD_nil]
    exact hs08fld_zero j
  | e :: t, 0, h => by
    have he := h e List.mem_cons_self
    simp only [hs08Pk, List.foldr_cons, hs08Fld, List.getD_cons_zero]
    omega
  | e :: t, j + 1, h => by
    have he := h e List.mem_cons_self
    have ih := hs08fld_pk t j fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [hs08Pk, List.foldr_cons, hs08Fld, List.getD_cons_succ] at ih ⊢
    have hd : (e + 32 * t.foldr (fun e a => e + 32 * a) 0) / 32 =
        t.foldr (fun e a => e + 32 * a) 0 := by
      omega
    rw [hd]
    exact ih

theorem hs08pconj_tabF (A X B : Fin 22 → Fin 22) :
    hs08PConj (hs08Pk (hs08TabF A)) (hs08Pk (hs08TabF X)) (hs08Pk (hs08TabF B)) =
      hs08Pk (hs08TabF (A ∘ X ∘ B)) := by
  unfold hs08PConj
  apply congrArg hs08Pk
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hs08length_tabF]
  · intro i h1 h2
    have hi : i < 22 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hs08fld_pk _ _ (hs08lt_of_tabF B), hs08getD_tabF B ⟨i, hi⟩,
      hs08fld_pk _ _ (hs08lt_of_tabF X), hs08getD_tabF X, hs08fld_pk _ _ (hs08lt_of_tabF A),
      hs08getD_tabF A]
    simp only [hs08TabF, List.getElem_ofFn, Function.comp_apply]

theorem hs08perm_sum {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y l =>
    simp only [List.sum_cons]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem hs08inv_of {a b : Tab} {A B : Fin 22 → Fin 22} (hA : hs08TabF A = a) (hB : hs08TabF B = b)
    (h : tmul a b = idTab) : ∀ x, A (B x) = x := by
  rw [← hA, ← hB, ← hs08TabF_comp, ← hs08TabF_id] at h
  exact fun x => congrFun (hs08TabF_injective h) x

def hs08ConjSet (J : List Tab) (p : Tab × Tab) : List Tab := J.map fun x => tmul (tmul p.1 x) p.2

theorem hs08key_spec {J : List Tab} {p : Tab × Tab} (hV : ∀ x ∈ J, hs08TabV x = true)
    (h1 : hs08TabV p.1 = true) (h2 : hs08TabV p.2 = true) :
    hs08Key (J.map hs08Pk) (hs08Pk p.1) (hs08Pk p.2) =
      ((hs08ConjSet J p).map hs08Pk).sum % hs08KeyMod := by
  unfold hs08Key hs08ConjSet
  congr 2
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro x hx
  obtain ⟨X, rfl⟩ := hs08exists_tabF (hV x hx)
  obtain ⟨A, hA⟩ := hs08exists_tabF h1
  obtain ⟨B, hB⟩ := hs08exists_tabF h2
  simp only [Function.comp_apply]
  rw [← hA, ← hB, ← hs08TabF_comp, ← hs08TabF_comp]
  exact hs08pconj_tabF A X B

theorem hs08key_eq {J : List Tab} {p q : Tab × Tab} (hJ : J.Nodup)
    (hV : ∀ x ∈ J, hs08TabV x = true)
    (hp : hs08TabV p.1 = true ∧ hs08TabV p.2 = true ∧ tmul p.1 p.2 = idTab ∧ tmul p.2 p.1 = idTab)
    (hq : hs08TabV q.1 = true ∧ hs08TabV q.2 = true ∧ tmul q.1 q.2 = idTab ∧ tmul q.2 q.1 = idTab)
    (hc : ∀ x ∈ J, tmul (tmul (tmul p.2 q.1) x) (tmul q.2 p.1) ∈ J) :
    hs08Key (J.map hs08Pk) (hs08Pk p.1) (hs08Pk p.2) =
      hs08Key (J.map hs08Pk) (hs08Pk q.1) (hs08Pk q.2) := by
  obtain ⟨P1, hP1⟩ := hs08exists_tabF hp.1
  obtain ⟨P2, hP2⟩ := hs08exists_tabF hp.2.1
  obtain ⟨Q1, hQ1⟩ := hs08exists_tabF hq.1
  obtain ⟨Q2, hQ2⟩ := hs08exists_tabF hq.2.1
  have e12 := hs08inv_of hP1 hP2 hp.2.2.1
  have f21 := hs08inv_of hQ2 hQ1 hq.2.2.2
  have hsub : ∀ y ∈ hs08ConjSet J q, y ∈ hs08ConjSet J p := by
    intro y hy
    simp only [hs08ConjSet, List.mem_map] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨_, hc x hx, ?_⟩
    obtain ⟨X, rfl⟩ := hs08exists_tabF (hV x hx)
    rw [← hP1, ← hP2, ← hQ1, ← hQ2]
    simp only [← hs08TabF_comp]
    congr 1
    funext a
    simp only [Function.comp_apply, e12]
  have hndq : (hs08ConjSet J q).Nodup := by
    unfold hs08ConjSet
    refine List.Nodup.map_on ?_ hJ
    intro x hx y hy hxy
    obtain ⟨X, rfl⟩ := hs08exists_tabF (hV x hx)
    obtain ⟨Y, rfl⟩ := hs08exists_tabF (hV y hy)
    rw [← hQ1, ← hQ2] at hxy
    simp only [← hs08TabF_comp] at hxy
    have h := hs08TabF_injective hxy
    congr 1
    funext a
    have h1 := congrFun h (Q1 a)
    simp only [Function.comp_apply, f21] at h1
    have h2 := congrArg Q2 h1
    simp only [f21] at h2
    exact h2
  have hperm : (hs08ConjSet J q).Perm (hs08ConjSet J p) :=
    List.Subperm.perm_of_length_le (hndq.subperm hsub)
      (by simp only [hs08ConjSet, List.length_map, le_refl])
  rw [hs08key_spec hV hp.1 hp.2.1, hs08key_spec hV hq.1 hq.2.1,
    hs08perm_sum (hperm.map hs08Pk)]

theorem hs08pairwise_of_keys {J : List Tab} {P : List (Tab × Tab)} (hJ : J.Nodup)
    (hV : ∀ x ∈ J, hs08TabV x = true) (hP : HS08PairsOK P) (hK : hs08KeysOK J P = true) :
    P.Pairwise fun p q => ∃ x ∈ J, tmul (tmul (tmul p.2 q.1) x) (tmul q.2 p.1) ∉ J := by
  have hnd : (P.map fun p => hs08Key (J.map hs08Pk) (hs08Pk p.1) (hs08Pk p.2)).Nodup :=
    CFSG.Decide.nodup_of_bitsetNodup_nat hK
  have hpw := List.pairwise_map.1 hnd
  refine hpw.imp_of_mem fun {p q} hp hq hne => ?_
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  exact hne (hs08key_eq hJ hV (hP p hp) (hP q hq) hc)

theorem hs08conjPropJ {J : List Tab} (hJ : J.Nodup) (hV : ∀ x ∈ J, hs08TabV x = true)
    (hl : cPairs.length = 231) (hP : HS08PairsOK cPairs) (hK : hs08KeysOK J cPairs = true) :
    ConjPropJ J := by
  unfold ConjPropJ
  exact ⟨hl, fun p hp => (hP p hp).2.2.1, hs08pairwise_of_keys hJ hV hP hK⟩

end CFSG.KC.EvenSporM22
