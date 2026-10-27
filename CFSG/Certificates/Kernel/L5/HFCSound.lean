
module

public import Certificates.Data.Kernel.L5.HFC
public import CFSG.Certificates.Kernel.L5.Fast
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

theorem tabL_getD (p : Perm (Fin 16)) (j : Fin 16) : (tabL p).getD j.val 0 = p j := by
  unfold tabL
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem tabL_mul (p q : Perm (Fin 16)) : tmulL (tabL p) (tabL q) = tabL (p * q) := by
  unfold tmulL
  conv_lhs => arg 2; unfold tabL
  rw [List.map_map, tabL]
  congr 1
  funext i
  exact tabL_getD p (q i)

theorem tabL_injective : Function.Injective tabL := by
  intro p q h
  ext i
  have := congrArg (fun t => List.getD t i.val 0) h
  simp only [tabL_getD] at this
  rw [this]

theorem tabL_one : tabL 1 = List.finRange 16 := by
  unfold tabL
  simp

theorem mem_map_tabL (l : List (Perm (Fin 16))) (p : Perm (Fin 16)) :
    tabL p ∈ l.map tabL ↔ p ∈ l :=
  List.mem_map_of_injective tabL_injective

theorem closureL_map (gs : List (Perm (Fin 16))) (k : Nat) :
    closureL (gs.map tabL) k = (closureList gs k).map tabL := by
  unfold closureL closureList
  induction k with
  | zero => simp [tabL_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    unfold closureStep
    rw [← List.dedup_map_of_injective tabL_injective]
    congr 1
    simp only [List.map_append, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, tabL_mul]

theorem invTab_spec {f : Fin 16 → Fin 16} (hs : Function.Surjective f) (j : Fin 16) :
    f (invTab f j) = j := by
  unfold invTab
  have hx : ((List.finRange 16).find? fun i => decide (f i = j)).isSome := by
    rw [List.find?_isSome]
    obtain ⟨i, hi⟩ := hs j
    exact ⟨i, List.mem_finRange _, by simpa using hi⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hx
  rw [hx, Option.getD_some]
  simpa using List.find?_some hx

theorem isPermChk_iff (f : Fin 16 → Fin 16) : isPermChk f = true ↔ Function.Surjective f := by
  unfold isPermChk
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, decide_eq_true_eq,
    true_implies]
  constructor
  · intro h j
    exact ⟨_, (h j).2⟩
  · intro hs i
    have hi : Function.Injective f := Finite.injective_iff_surjective.2 hs
    exact ⟨hi (invTab_spec hs (f i)), invTab_spec hs i⟩

theorem isPermChk_perm (p : Perm (Fin 16)) : isPermChk p = true :=
  (isPermChk_iff p).2 p.surjective

theorem permOfTab_tabL (p : Perm (Fin 16)) : permOfTab (tabL p) = p := by
  unfold permOfTab
  have e : (fun i : Fin 16 => (tabL p).getD i.val 0) = p := funext (tabL_getD p)
  rw [e]
  unfold mkPerm
  rw [dif_pos (isPermChk_perm p)]
  ext i
  rfl

theorem n24L_eq : n24L = n24C.map ev := (map_cOf_ev n24L).symm

theorem d8L_eq : d8L = d8C.map ev := (map_cOf_ev d8L).symm

theorem n24L_getD (k : Nat) : n24L.getD k 1 = ev (n24C.getD k 1) := by
  rw [n24L_eq, ← ev_one, List.getD_map]

theorem G72gens_eq : G72gens = G72gC.map ev := by
  simp only [G72gens, G72gC, List.map_cons, List.map_nil, yC, wC, cHC, ev_cOf, n24L_getD]

theorem G72L_eq : G72L = G72C.map ev := by
  unfold G72L G72C
  rw [closureL_map, List.map_map]
  have e : permOfTab ∘ tabL = id := funext permOfTab_tabL
  rw [e, List.map_id, G72gens_eq, closureList_map_ev]

theorem closureL_ev (gs : List (CV 16)) (k : Nat) :
    closureL ((gs.map ev).map tabL) k = ((closureList gs k).map ev).map tabL := by
  rw [closureL_map, closureList_map_ev]

theorem mem_closureL_ev (gs : List (CV 16)) (k : Nat) (x : CV 16) :
    tabL (ev x) ∈ closureL ((gs.map ev).map tabL) k ↔ x ∈ closureList gs k := by
  rw [closureL_ev, mem_map_tabL, mem_map_ev]

theorem all_congr_mem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem any_congr_mem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem testBit_foldl_or {α : Type*} (f : α → Nat) : ∀ (l : List α) (init e : Nat),
    (l.foldl (fun acc x => acc ||| f x) init).testBit e =
      (init.testBit e || l.any fun x => (f x).testBit e)
  | [], init, e => by simp
  | x :: l, init, e => by
    rw [List.foldl_cons, testBit_foldl_or f l, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem testBit_ite_pow (c : Prop) [Decidable c] (k e : Nat) :
    (if c then 2 ^ k else 0).testBit e = (decide c && decide (k = e)) := by
  split_ifs with h <;> simp [h, Nat.testBit_two_pow]

theorem pN_testBit (V : Finset (Fin 16)) (e : Nat) :
    (pN V).testBit e = (List.finRange 16).any fun i => decide (i ∈ V) && decide (i.val = e) := by
  unfold pN
  rw [testBit_foldl_or (fun i : Fin 16 => if i ∈ V then 2 ^ i.val else 0)]
  simp only [Nat.zero_testBit, Bool.false_or, testBit_ite_pow]

theorem pN_testBit_fin (V : Finset (Fin 16)) (i : Fin 16) :
    (pN V).testBit i.val = decide (i ∈ V) := by
  rw [pN_testBit, Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, e⟩
    rwa [← Fin.ext e]
  · intro h
    exact ⟨i, h, rfl⟩

theorem pN_testBit_ge (V : Finset (Fin 16)) {e : Nat} (he : 16 ≤ e) : (pN V).testBit e = false := by
  rw [pN_testBit, List.any_eq_false]
  intro i _
  have := i.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro _
  omega

theorem pN_injective : Function.Injective pN := by
  intro V W h
  ext i
  have := congrArg (fun n => Nat.testBit n i.val) h
  simp only [pN_testBit_fin, decide_eq_decide] at this
  exact this

theorem decide_eq_pN (V W : Finset (Fin 16)) : decide (V = W) = (pN V == pN W) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => pN_injective h⟩

theorem bit_mul_pow (M i k : Nat) : (M >>> i) % 2 * 2 ^ k = if M.testBit i then 2 ^ k else 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (M / 2 ^ i) with h | h <;> simp [h]

theorem pN_image (g : CV 16) (V : Finset (Fin 16)) : pN (V.image (ev g)) = imgN g (pN V) := by
  apply Nat.eq_of_testBit_eq
  intro e
  unfold imgN
  rw [pN_testBit, testBit_foldl_or (fun i => (pN V >>> i) % 2 * 2 ^ img 16 g.1 i)]
  simp only [Nat.zero_testBit, Bool.false_or, bit_mul_pow, testBit_ite_pow]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_finRange, List.mem_range, true_and, Bool.and_eq_true,
    decide_eq_true_eq, Finset.mem_image]
  constructor
  · rintro ⟨i, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨a.val, a.isLt, ?_, (ev_apply g a).symm⟩
    rw [pN_testBit_fin]
    exact decide_eq_true ha
  · rintro ⟨i, hi, hb, h⟩
    have ha : (⟨i, hi⟩ : Fin 16) ∈ V := by
      have := pN_testBit_fin V ⟨i, hi⟩
      simp only at this
      rw [this] at hb
      exact of_decide_eq_true hb
    exact ⟨ev g ⟨i, hi⟩, ⟨_, ha, rfl⟩, by rw [ev_apply]; exact h⟩

theorem pN_inter (A B : Finset (Fin 16)) : pN (A ∩ B) = pN A &&& pN B := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_and]
  by_cases he : e < 16
  · have h := pN_testBit_fin (A ∩ B) ⟨e, he⟩
    rw [pN_testBit_fin A ⟨e, he⟩, pN_testBit_fin B ⟨e, he⟩]
    simp only at h
    have hi : decide ((⟨e, he⟩ : Fin 16) ∈ A ∩ B) =
        (decide ((⟨e, he⟩ : Fin 16) ∈ A) && decide ((⟨e, he⟩ : Fin 16) ∈ B)) := by
      rw [← Bool.decide_and]
      exact decide_eq_decide.2 Finset.mem_inter
    rw [h, hi]
  · rw [pN_testBit_ge _ (by omega), pN_testBit_ge _ (by omega)]
    rfl

theorem testBit_permFold (f : Fin 16 → Fin 16) (e : Nat) :
    ((List.finRange 16).foldl (fun acc i => acc ||| 2 ^ (f i).val) 0).testBit e =
      (List.finRange 16).any fun i => decide ((f i).val = e) := by
  rw [testBit_foldl_or (fun i : Fin 16 => 2 ^ (f i).val)]
  simp [Nat.testBit_two_pow]

theorem isPermChk_eq (f : Fin 16 → Fin 16) : isPermChk f = permN f := by
  rw [Bool.eq_iff_iff, isPermChk_iff]
  unfold permN
  rw [beq_iff_eq]
  have h65 : (65535 : Nat) = 2 ^ 16 - 1 := by norm_num
  constructor
  · intro hs
    apply Nat.eq_of_testBit_eq
    intro e
    rw [testBit_permFold, h65, Nat.testBit_two_pow_sub_one]
    by_cases he : e < 16
    · obtain ⟨i, hi⟩ := hs ⟨e, he⟩
      simp only [he, decide_true, List.any_eq_true, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact ⟨i, by rw [hi]⟩
    · simp only [he, decide_false, List.any_eq_false, List.mem_finRange, true_implies,
        decide_eq_true_eq]
      intro i hi
      have := (f i).isLt
      omega
  · intro h j
    have := congrArg (fun n => Nat.testBit n j.val) h
    simp only [testBit_permFold, h65, Nat.testBit_two_pow_sub_one, j.isLt, decide_true,
      List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at this
    obtain ⟨i, hi⟩ := this
    exact ⟨i, Fin.ext hi⟩

theorem allQ2_eq (g : Fin 16 → Fin 16 → Bool) (c : Perm (Fin 16) → Bool) :
    allQ2 g c = allQ2C g (fun x => c (ev x)) := by
  unfold allQ2 allQ2C
  simp only [ev_cOf, isPermChk_eq]

theorem allQ2C_of_rows (g : Fin 16 → Fin 16 → Bool) (c : CV 16 → Bool)
    (h : ∀ k < 4, allQ2RowC g c k = true) : allQ2C g c = true := by
  unfold allQ2C
  rw [List.all_eq_true]
  intro a ha
  have h0 := h (a.val / 4) (by omega)
  unfold allQ2RowC at h0
  rw [List.all_eq_true] at h0
  have h1 := h0 a ha
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem orbStep_map (gs : List (CV 16)) (l : List (Finset (Fin 16))) :
    (orbStep (gs.map ev) l).map pN = orbStepN gs (l.map pN) := by
  unfold orbStep orbStepN
  rw [List.map_take, ← List.dedup_map_of_injective pN_injective]
  simp only [List.map_append, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, pN_image]

theorem orbList_map (gs : List (CV 16)) (k : Nat) :
    (orbList (gs.map ev) k).map pN = orbListN gs k := by
  unfold orbList orbListN
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, orbStep_map]

theorem orbStepN_nodup (gs : List (CV 16)) (l : List Nat) : (orbStepN gs l).Nodup :=
  (List.nodup_dedup _).sublist (List.take_sublist _ _)

theorem orbStepN_len5 (gs : List (CV 16)) {l : List Nat} (hn : l.Nodup) (h5 : l.length = 5) :
    (orbStepN gs l).length = 5 := by
  unfold orbStepN
  rw [List.length_take]
  have hs : l ⊆ (l ++ l.flatMap fun M => gs.map fun g => imgN g M).dedup := by
    intro a ha
    rw [List.mem_dedup]
    exact List.mem_append_left _ ha
  have := (List.subperm_of_subset hn hs).length_le
  omega

theorem orbListN_len5 (gs : List (CV 16)) (h : (orbListN gs 3).length = 5) :
    5 ≤ (orbListN gs 6).dedup.length := by
  have key : ∀ j, (orbListN gs (3 + j)).length = 5 ∧ (orbListN gs (3 + j)).Nodup := by
    intro j
    induction j with
    | zero =>
      refine ⟨h, ?_⟩
      unfold orbListN
      rw [Function.iterate_succ_apply']
      exact orbStepN_nodup _ _
    | succ j ih =>
      have e : orbListN gs (3 + (j + 1)) = orbStepN gs (orbListN gs (3 + j)) := by
        unfold orbListN
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
      rw [e]
      exact ⟨orbStepN_len5 gs ih.2 ih.1, orbStepN_nodup _ _⟩
  obtain ⟨h1, h2⟩ := key 3
  rw [List.Nodup.dedup h2, h1]

theorem subset_toFinset_iff (F : Finset (Finset (Fin 16))) (L : List (Finset (Fin 16)))
    (hF : ∀ V, V ∈ F ↔ V ∈ L) (l : List (Finset (Fin 16))) :
    decide (F ⊆ l.toFinset) = L.all fun V => decide (pN V ∈ l.map pN) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  simp only [decide_eq_true_eq, List.mem_map_of_injective pN_injective]
  constructor
  · intro h V hV
    exact List.mem_toFinset.1 (h ((hF V).2 hV))
  · intro h V hV
    exact List.mem_toFinset.2 (h V ((hF V).1 hV))

theorem mem_fam0 (V : Finset (Fin 16)) : V ∈ fam0 ↔ V ∈ fam0L := by
  simp [fam0, fam0L]

theorem mem_fam1 (V : Finset (Fin 16)) : V ∈ fam1 ↔ V ∈ fam1L := by
  simp [fam1, fam1L]

theorem linChk_ev (c : CV 16) : linChk (ev c) = linChkN c := by
  unfold linChk linChkN
  apply all_congr_mem
  intro i _
  apply all_congr_mem
  intro j _
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Fin.ext_iff]
  exact Iff.rfl

theorem fam0Chk_ev (c : CV 16) : fam0Chk (ev c) = fam0ChkN c := by
  unfold fam0Chk fam0ChkN
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  simp only [decide_eq_true_eq, ← pN_image, List.mem_map_of_injective pN_injective]
  constructor
  · intro h V hV
    exact (mem_fam0 _).1 (h V ((mem_fam0 V).2 hV))
  · intro h V hV
    exact (mem_fam0 _).2 (h V ((mem_fam0 V).1 hV))

theorem closureList_map_hom (ψ : CV 16 → CV 16) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (h1 : ψ 1 = 1) (hinj : Function.Injective ψ) (gs : List (CV 16)) (k : Nat) :
    closureList (gs.map ψ) k = (closureList gs k).map ψ := by
  unfold closureList
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    unfold closureStep
    rw [← List.dedup_map_of_injective hinj]
    congr 1
    simp only [List.map_append, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, hmul]

theorem getD_idxOf {G : List (CV 16)} {x : CV 16} (hx : x ∈ G) :
    G.idxOf x < G.length ∧ G.getD (G.idxOf x) 1 = x := by
  have h := List.idxOf_lt_length_of_mem hx
  exact ⟨h, by rw [List.getD_eq_getElem _ _ h, List.getElem_idxOf]⟩

theorem stepG_testBit (n : Nat) (mul : Nat → Nat → Nat) (gs : List Nat) (M e : Nat) :
    (stepG n mul gs M).testBit e = (M.testBit e || (List.range n).any fun a =>
      M.testBit a && gs.any fun s => decide (mul a s = e)) := by
  unfold stepG
  rw [testBit_foldl_or (fun a => if M.testBit a then gs.foldl (fun acc' s => acc' ||| 2 ^ mul a s) 0
    else 0)]
  congr 1
  apply any_congr_mem
  intro a _
  split_ifs with h
  · rw [testBit_foldl_or (fun s => 2 ^ mul a s)]
    simp [h, Nat.testBit_two_pow]
  · simp [h]

section Gen

variable (G : List (CV 16)) (n : Nat) (mul : Nat → Nat → Nat) (i1 : Nat) (hn : i1 < n)
  (h0 : G.getD i1 1 = 1)
  (hm : ∀ a < n, ∀ b < n, mul a b < n ∧ G.getD a 1 * G.getD b 1 = G.getD (mul a b) 1)
include hn h0 hm

theorem mem_closureList_gen (gs : List Nat) (hg : ∀ s ∈ gs, s < n) (k : Nat) (x : CV 16) :
    x ∈ closureList (gs.map fun s => G.getD s 1) k ↔
      ∃ a < n, (closG n mul i1 gs k).testBit a ∧ x = G.getD a 1 := by
  induction k generalizing x with
  | zero =>
    unfold closureList closG
    simp only [Function.iterate_zero, id_eq, List.mem_singleton, Nat.testBit_two_pow,
      decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨i1, hn, rfl, h0.symm⟩
    · rintro ⟨a, ha, rfl, rfl⟩
      exact h0
  | succ k ih =>
    have e1 : closureList (gs.map fun s => G.getD s 1) (k + 1) =
        closureStep (gs.map fun s => G.getD s 1) (closureList (gs.map fun s => G.getD s 1) k) := by
      unfold closureList
      rw [Function.iterate_succ_apply']
    have e2 : closG n mul i1 gs (k + 1) = stepG n mul gs (closG n mul i1 gs k) := by
      unfold closG
      rw [Function.iterate_succ_apply']
    rw [e1, e2]
    unfold closureStep
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]
    constructor
    · rintro (hx | ⟨g, hgl, s', ⟨s, hs, rfl⟩, rfl⟩)
      · obtain ⟨a, ha, hb, rfl⟩ := (ih x).1 hx
        exact ⟨a, ha, by rw [stepG_testBit, hb, Bool.true_or], rfl⟩
      · obtain ⟨a, ha, hb, rfl⟩ := (ih g).1 hgl
        obtain ⟨h1, h2⟩ := hm a ha s (hg s hs)
        refine ⟨mul a s, h1, ?_, h2⟩
        rw [stepG_testBit]
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq]
        exact Or.inr ⟨a, ha, hb, s, hs, rfl⟩
    · rintro ⟨e, he, hb, rfl⟩
      rw [stepG_testBit] at hb
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at hb
      rcases hb with hb | ⟨a, ha, hab, s, hs, rfl⟩
      · exact Or.inl ((ih _).2 ⟨e, he, hb, rfl⟩)
      · refine Or.inr ⟨G.getD a 1, (ih _).2 ⟨a, ha, hab, rfl⟩, G.getD s 1, ⟨s, hs, rfl⟩, ?_⟩
        exact (hm a ha s (hg s hs)).2

theorem decide_mem_closure_gen (hl : G.length = n) (hnd : G.Nodup) (gs : List Nat)
    (hg : ∀ s ∈ gs, s < n) (k : Nat) {e : Nat} (he : e < n) :
    decide (G.getD e 1 ∈ closureList (gs.map fun s => G.getD s 1) k) =
      (closG n mul i1 gs k).testBit e := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_closureList_gen G n mul i1 hn h0 hm gs hg]
  constructor
  · rintro ⟨a, ha, hb, h⟩
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
    rw [(hnd.getElem_inj_iff).1 h]
    exact hb
  · intro hb
    exact ⟨e, he, hb, rfl⟩

end Gen

theorem gens_eq (x : CV 16) : [yHat, wHat, ev x] = [yC, wC, x].map ev := by
  simp [yC, wC, ev_cOf]

theorem n24Cov_ev (C : List (CV 16)) (tw : Bool) :
    n24Cov ((C.map ev).map tabL) tw = n24CovC C tw := by
  unfold n24Cov n24CovC
  rw [n24L_eq, List.all_map]
  congr 1
  funext a
  have e : (if tw then twPerm * ev a * twPerm⁻¹ else ev a) =
      ev (if tw then twC * a * twC⁻¹ else a) := by
    cases tw <;> simp [twC, ev_mul, ev_inv, ev_cOf]
  simp only [Function.comp_apply, e, decide_eq_decide, mem_map_tabL, mem_map_ev]

theorem Ppl_ev (x : CV 16) : decide (Ppl.image (ev x) = Ppl) = (imgN x (pN Ppl) == pN Ppl) := by
  rw [decide_eq_pN, pN_image]

theorem n24Pre_ev (x : CV 16) : n24Pre (ev x) = n24PreC x := by
  unfold n24Pre n24PreC
  have e0 : pN {0} = 1 := by decide +kernel
  rw [decide_not, decide_eq_pN, decide_eq_pN, decide_eq_pN, pN_inter, pN_inter, pN_image, e0]

@[expose] noncomputable def n24TailF (x : CV 16) (o : List Nat) : Bool :=
  (imgN x (pN Ppl) == pN Ppl) &&
    (let C := closureList [yC, wC, x] 8
     ((fam0L.all fun F => decide (pN F ∈ o)) && n24CovC C false) ||
       ((fam1L.all fun F => decide (pN F ∈ o)) && n24CovC C true))

@[expose] noncomputable def n24ChkF (x : CV 16) : Bool :=
  let o := orbListN [yC, wC, x] 6
  decide (5 ≤ o.dedup.length) || n24TailF x o

theorem n24Chk_ev (x : CV 16) : n24Chk (ev x) = n24ChkF x := by
  unfold n24Chk n24ChkF n24Tail n24TailF
  dsimp only
  rw [gens_eq, List.card_toFinset, subset_toFinset_iff fam0 fam0L mem_fam0,
    subset_toFinset_iff fam1 fam1L mem_fam1, closureL_ev, n24Cov_ev, n24Cov_ev, Ppl_ev,
    ← orbList_map, List.dedup_map_of_injective pN_injective, List.length_map]

@[expose] noncomputable def famEntryF (x : CV 16) : Bool :=
  let f0 := fam0ChkL (ev x)
  let f1 := fam1ChkL (ev x)
  (!(f0 || f1) || (imgN x (pN Ppl) == pN Ppl)) && (!f0 || decide (x ∈ G72C)) &&
    (!f0 || decide (x ∈ n24C) || decide (cHC ∈ closureList [wC, n24C.getD 6 1, x] 8))

theorem famEntry_ev (x : CV 16) : famEntry G72L (ev x) = famEntryF x := by
  unfold famEntry famEntryF cHatChk presChk
  have e1 : decide (ev x ∈ G72L) = decide (x ∈ G72C) := by
    rw [G72L_eq, decide_mem_map_ev]
  have e2 : decide (ev x ∈ n24L) = decide (x ∈ n24C) := by
    rw [n24L_eq, decide_mem_map_ev]
  have e3 : decide (tabL cHat ∈ closureL ([wHat, n24L.getD 6 1, ev x].map tabL) 8) =
      decide (cHC ∈ closureList [wC, n24C.getD 6 1, x] 8) := by
    have e : [wHat, n24L.getD 6 1, ev x] = [wC, n24C.getD 6 1, x].map ev := by
      rw [n24L_getD]
      simp only [List.map_cons, List.map_nil, wC, ev_cOf]
    have e' : cHat = ev cHC := by rw [cHC, ev_cOf]
    rw [e, e', decide_eq_decide, mem_closureL_ev]
  rw [e1, e2, e3, Ppl_ev]

@[expose] noncomputable def d8ChkC (b c : CV 16) : Bool :=
  let gens : List (CV 16) := [yC, b, c]
  let T := closureList gens 8
  (T.all fun t => gens.all fun s => decide (t * s ∈ T) && decide (t * s⁻¹ ∈ T)) &&
    (let L := n24C.filter fun x => decide (x ∈ T)
     !decide (L.length = 8) || (L.all (fun x => decide (x ∈ d8C)) && d8C.all fun x => decide (x ∈ L)))

theorem d8Chk_ev (b c : CV 16) : d8Chk (ev b) (ev c) = d8ChkC b c := by
  unfold d8Chk d8ChkC
  have eg : [yHat, ev b, ev c] = [yC, b, c].map ev := by simp [yC, ev_cOf]
  simp only [eg, closureL_ev, List.all_map, Function.comp_def, tabL_mul, ← ev_mul, ← ev_inv,
    decide_eq_decide, mem_map_tabL, mem_map_ev, n24L_eq, d8L_eq, List.filter_map,
    List.length_map]

end CFSG.Certificates.Kernel.L5H

end
