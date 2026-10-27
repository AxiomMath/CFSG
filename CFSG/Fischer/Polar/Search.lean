module

public import CFSG.Fischer.Polar.Basic

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

@[expose] def Cons (I X : Flags) (O : Set (Fin 693)) : Prop :=
  (∀ p : Fin 693, I[p.val]! = true → p ∈ O) ∧ ∀ p : Fin 693, X[p.val]! = true → p ∉ O

structure CtxOK (C : HCtx) : Prop where
  perpT : ∀ x y : Fin 693, (C.P[x.val]!)[y.val]! = true ↔ perp x y
  pl : ∀ (x : Fin 693) (y : ℕ), y ∈ C.pl[x.val]! ↔ ∃ h : y < 693, perp x ⟨y, h⟩
  lamIdx : ∀ a < 693, ∀ j, j ∈ C.lamIdx[a]! ↔ j < 1024 ∧ (C.lam[j]!)[a]! = true
  gI : ∀ x < 693, ∀ y < 693, ap C.gI[x]! y < 693

@[expose] def LocalOK (C : HCtx) (O : Set (Fin 693)) : Prop :=
  ∀ x : Fin 693, x ∈ O → ∃ j < 1024, ∀ y : Fin 693, perp x y →
    (y ∈ O ↔ (C.lam[j]!)[ap C.gI[x.val]! y.val]! = true)

theorem anyIn_eq_true {n : ℕ} {p : ℕ → Bool} : anyIn n p = true ↔ ∃ i < n, p i = true := by
  unfold anyIn
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allIn_eq_true]
  constructor
  · intro h
    by_contra hc
    exact h fun i _ hi => by
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.2 fun h' => hc ⟨i, hi, h'⟩
  · rintro ⟨i, hi, h⟩ H
    have := H i (Nat.zero_le _) hi
    rw [h] at this
    exact Bool.false_ne_true this

theorem getElem!_set!_true {a : Flags} {k p : ℕ} (h : (a.set! k true)[p]! = true) :
    a[p]! = true ∨ k = p := by
  by_cases hkp : k = p
  · exact Or.inr hkp
  · rw [Array.getElem!_set!_ne _ _ _ _ hkp] at h
    exact Or.inl h

theorem foldl_set_true {l : List ℕ} {c : ℕ → Bool} {a : Flags} {p : ℕ}
    (h : (l.foldl (fun a y => if c y then a.set! y true else a) a)[p]! = true) :
    a[p]! = true ∨ (p ∈ l ∧ c p = true) := by
  induction l generalizing a with
  | nil => exact Or.inl h
  | cons y l ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h1 | ⟨h1, h2⟩
    · by_cases hc : c y = true
      · rw [ite_eq_left hc] at h1
        rcases getElem!_set!_true h1 with h3 | rfl
        · exact Or.inl h3
        · exact Or.inr ⟨List.mem_cons_self .., hc⟩
      · rw [ite_eq_right hc] at h1
        exact Or.inl h1
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem foldl_set_false {l : List ℕ} {c : ℕ → Bool} {a : Flags} {p : ℕ}
    (h : (l.foldl (fun a y => if c y then a else a.set! y true) a)[p]! = true) :
    a[p]! = true ∨ (p ∈ l ∧ c p = false) := by
  induction l generalizing a with
  | nil => exact Or.inl h
  | cons y l ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h1 | ⟨h1, h2⟩
    · by_cases hc : c y = true
      · rw [ite_eq_left hc] at h1
        exact Or.inl h1
      · rw [ite_eq_right hc] at h1
        rcases getElem!_set!_true h1 with h3 | rfl
        · exact Or.inl h3
        · exact Or.inr ⟨List.mem_cons_self .., Bool.eq_false_iff.2 hc⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem extI_sound {C : HCtx} {F : List (ℕ × ℕ)} {I : Flags} {p : ℕ}
    (h : (extI C F I)[p]! = true) :
    I[p]! = true ∨ ∃ e ∈ F, p ∈ C.pl[e.1]! ∧ (C.lam[e.2]!)[ap C.gI[e.1]! p]! = true := by
  unfold extI at h
  induction F generalizing I with
  | nil => exact Or.inl h
  | cons e F ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h1 | ⟨e', he', h2⟩
    · rw [← Array.foldl_toList] at h1
      rcases foldl_set_true h1 with h3 | ⟨h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨e, List.mem_cons_self .., Array.mem_toList_iff.1 h3, h4⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h2⟩

theorem extX_sound {C : HCtx} {F : List (ℕ × ℕ)} {X : Flags} {p : ℕ}
    (h : (extX C F X)[p]! = true) :
    X[p]! = true ∨ ∃ e ∈ F, p ∈ C.pl[e.1]! ∧ (C.lam[e.2]!)[ap C.gI[e.1]! p]! = false := by
  unfold extX at h
  induction F generalizing X with
  | nil => exact Or.inl h
  | cons e F ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h1 | ⟨e', he', h2⟩
    · rw [← Array.foldl_toList] at h1
      rcases foldl_set_false h1 with h3 | ⟨h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨e, List.mem_cons_self .., Array.mem_toList_iff.1 h3, h4⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h2⟩

@[expose] def TrueAt (C : HCtx) (O : Set (Fin 693)) (x j : ℕ) : Prop :=
  ∃ hx : x < 693, (⟨x, hx⟩ : Fin 693) ∈ O ∧ ∀ y : Fin 693, perp ⟨x, hx⟩ y →
    (y ∈ O ↔ (C.lam[j]!)[ap C.gI[x]! y.val]! = true)

theorem cons_ext {C : HCtx} (hC : CtxOK C) {F : List (ℕ × ℕ)} {I X : Flags}
    {O : Set (Fin 693)} (hc : Cons I X O) (hF : ∀ e ∈ F, TrueAt C O e.1 e.2) :
    Cons (extI C F I) (extX C F X) O := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rcases extI_sound hp with h | ⟨e, he, hpl, hlam⟩
    · exact hc.1 p h
    · obtain ⟨hx, -, hy⟩ := hF e he
      have hperp := ((hC.pl ⟨e.1, hx⟩ p.val).1 hpl).2
      exact (hy p hperp).2 hlam
  · rcases extX_sound hp with h | ⟨e, he, hpl, hlam⟩
    · exact hc.2 p h
    · obtain ⟨hx, -, hy⟩ := hF e he
      have hperp := ((hC.pl ⟨e.1, hx⟩ p.val).1 hpl).2
      intro hpO
      rw [(hy p hperp).1 hpO] at hlam
      exact Bool.noConfusion hlam

theorem mem_cands {C : HCtx} (hC : CtxOK C) {I X : Flags} {O : Set (Fin 693)} (hc : Cons I X O)
    {x j : ℕ} (hxj : TrueAt C O x j) (hj : j < 1024) : j ∈ cands C x I X := by
  obtain ⟨hx, -, hy⟩ := hxj
  have hA : ∀ a ∈ C.pl[x]!.filterMap (fun y => if I[y]! then some (ap C.gI[x]! y) else none),
      (C.lam[j]!)[a]! = true := by
    intro a ha
    rw [Array.mem_filterMap] at ha
    obtain ⟨y, hy1, hy2⟩ := ha
    split at hy2
    · rename_i hIy
      cases hy2
      obtain ⟨hylt, hperp⟩ := (hC.pl ⟨x, hx⟩ y).1 hy1
      exact (hy ⟨y, hylt⟩ hperp).1 (hc.1 ⟨y, hylt⟩ hIy)
    · cases hy2
  have hB : ∀ b ∈ C.pl[x]!.filterMap (fun y => if X[y]! then some (ap C.gI[x]! y) else none),
      (C.lam[j]!)[b]! = false := by
    intro b hb
    rw [Array.mem_filterMap] at hb
    obtain ⟨y, hy1, hy2⟩ := hb
    split at hy2
    · rename_i hXy
      cases hy2
      obtain ⟨hylt, hperp⟩ := (hC.pl ⟨x, hx⟩ y).1 hy1
      rw [Bool.eq_false_iff]
      intro h'
      exact hc.2 ⟨y, hylt⟩ hXy ((hy ⟨y, hylt⟩ hperp).2 h')
    · cases hy2
  unfold cands
  simp only
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · split
    · rename_i a ha
      have ha' := Array.mem_of_find?_eq_some ha
      have hpos := Array.find?_some ha
      have halt : a < 693 := by
        rw [Array.mem_filterMap] at ha'
        obtain ⟨y, hy1, hy2⟩ := ha'
        split at hy2
        · cases hy2
          exact hC.gI x hx y ((hC.pl ⟨x, hx⟩ y).1 hy1).1
        · cases hy2
      exact (hC.lamIdx a halt j).2 ⟨hj, hA a ha'⟩
    · exact List.mem_range.2 hj
  · rw [Bool.and_eq_true, Array.all_eq_true', Array.all_eq_true']
    refine ⟨hA, fun b hb => ?_⟩
    rw [hB b hb]
    rfl

theorem pickMin_mem {cs : List (ℕ × List ℕ)} {d : ℕ × List ℕ} (h : pickMin cs = some d) :
    d ∈ cs := by
  induction cs with
  | nil => cases h
  | cons c cs ih =>
    unfold pickMin at h
    split at h
    · cases h
      exact List.mem_cons_self ..
    · rename_i d' hd'
      split at h
      · cases h
        exact List.mem_cons_self ..
      · cases h
        exact List.mem_cons_of_mem _ (ih hd')

theorem mem_forcedOf {cs : List (ℕ × List ℕ)} {e : ℕ × ℕ} (h : e ∈ forcedOf cs) :
    (e.1, [e.2]) ∈ cs := by
  unfold forcedOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, he⟩ := h
  split at he
  · rename_i j hj
    cases he
    rw [← hj]
    exact hc
  · cases he

theorem branchAll_sound {rec : Flags → Flags → Option (List Flags)} {C : HCtx} {x : ℕ}
    {I X : Flags} {js : List ℕ} {L : List Flags} (h : branchAll rec C x I X js = some L) {j : ℕ}
    (hj : j ∈ js) : ∃ a, rec (extI C [(x, j)] I) (extX C [(x, j)] X) = some a ∧ ∀ F ∈ a, F ∈ L := by
  induction js generalizing L with
  | nil => cases hj
  | cons j' js ih =>
    unfold branchAll at h
    split at h
    · rename_i a b ha hb
      cases h
      rcases List.mem_cons.1 hj with rfl | hj'
      · exact ⟨a, ha, fun F hF => List.mem_append_left _ hF⟩
      · obtain ⟨a', ha', hsub⟩ := ih hb hj'
        exact ⟨a', ha', fun F hF => List.mem_append_right _ (hsub F hF)⟩
    · cases h

theorem exists_trueAt {C : HCtx} (hC : CtxOK C) {I X : Flags} {O : Set (Fin 693)}
    (hO : LocalOK C O) (hc : Cons I X O) {x : ℕ} (hx : x < 693) (hIx : I[x]! = true) :
    ∃ j, j ∈ cands C x I X ∧ TrueAt C O x j := by
  obtain ⟨j, hj, hjy⟩ := hO ⟨x, hx⟩ (hc.1 ⟨x, hx⟩ hIx)
  have ht : TrueAt C O x j := ⟨hx, hc.1 ⟨x, hx⟩ hIx, hjy⟩
  exact ⟨j, mem_cands hC hc ht hj, ht⟩

theorem mem_xs {C : HCtx} {I X : Flags} {x : ℕ}
    (h : x ∈ filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []) :
    x < 693 ∧ I[x]! = true := by
  rw [mem_filterRange, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1⟩

theorem hstep_sound {C : HCtx} (hC : CtxOK C) {rec : Flags → Flags → Option (List Flags)}
    (hrec : ∀ I X L, rec I X = some L → ∀ O, LocalOK C O → Cons I X O →
      ∃ F ∈ L, O = flagSet F)
    {I X : Flags} {L : List Flags} (h : hstep C rec I X = some L) {O : Set (Fin 693)}
    (hO : LocalOK C O) (hc : Cons I X O) : ∃ F ∈ L, O = flagSet F := by
  unfold hstep at h
  split_ifs at h with h1 h2
  · exfalso
    obtain ⟨p, hp, hpp⟩ := anyIn_eq_true.1 h1
    rw [Bool.and_eq_true] at hpp
    exact hc.2 ⟨p, hp⟩ hpp.2 (hc.1 ⟨p, hp⟩ hpp.1)
  · cases h
    refine ⟨I, List.mem_singleton_self _, ?_⟩
    ext p
    rw [mem_flagSet]
    constructor
    · intro hpO
      have := (allIn_eq_true.1 h2) p.val (Nat.zero_le _) p.2
      rw [Bool.or_eq_true] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd hpO (hc.2 p h')
    · exact hc.1 p
  dsimp only at h
  split_ifs at h with h3 h4
  · exfalso
    rw [List.any_eq_true] at h3
    obtain ⟨c, hc', hce⟩ := h3
    rw [List.mem_map] at hc'
    obtain ⟨x, hx, rfl⟩ := hc'
    obtain ⟨hxlt, hIx⟩ := mem_xs hx
    obtain ⟨j, hj, -⟩ := exists_trueAt hC hO hc hxlt hIx
    rw [List.isEmpty_iff] at hce
    have hce' : cands C x I X = [] := hce
    rw [hce'] at hj
    exact List.not_mem_nil hj
  · refine hrec _ _ _ h O hO (cons_ext hC hc fun e he => ?_)
    have he' := mem_forcedOf he
    rw [List.mem_map] at he'
    obtain ⟨x, hx, hxe⟩ := he'
    obtain ⟨hxlt, hIx⟩ := mem_xs hx
    rw [Prod.mk.injEq] at hxe
    obtain ⟨rfl, hce⟩ := hxe
    obtain ⟨j, hj, ht⟩ := exists_trueAt hC hO hc hxlt hIx
    rw [hce, List.mem_singleton] at hj
    rw [← hj]
    exact ht
  · split at h
    · cases h
    · rename_i d hd
      have hd' := pickMin_mem hd
      rw [List.mem_map] at hd'
      obtain ⟨x, hx, rfl⟩ := hd'
      obtain ⟨hxlt, hIx⟩ := mem_xs hx
      obtain ⟨j, hj, ht⟩ := exists_trueAt hC hO hc hxlt hIx
      obtain ⟨a, ha, hsub⟩ := branchAll_sound h hj
      obtain ⟨F, hF, hOF⟩ := hrec _ _ _ ha O hO (cons_ext hC hc fun e he => by
        rw [List.mem_singleton] at he
        rw [he]
        exact ht)
      exact ⟨F, hsub F hF, hOF⟩

theorem hsearch_sound {C : HCtx} (hC : CtxOK C) (n : ℕ) :
    ∀ I X L, hsearch C n I X = some L → ∀ O, LocalOK C O → Cons I X O →
      ∃ F ∈ L, O = flagSet F := by
  induction n with
  | zero => intro I X L h; cases h
  | succ n ih =>
    intro I X L h O hO hc
    exact hstep_sound hC ih h hO hc

end CFSG.Fischer
