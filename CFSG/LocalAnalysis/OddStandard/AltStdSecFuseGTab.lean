module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGBlk
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGam
import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseModelA
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def Gl : (l : List ℕ) → Set (Gam l)
  | [] => ∅
  | a :: l => (Gb a ×ˢ Fl l) ∪ (Fb a ×ˢ Gl l)

theorem mem_Gl_iff (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) (γ : Gam l) :
    γ ∈ Gl l ↔ γ * γ = 1 ∧ fixG l γ = 2 := by
  induction l with
  | nil =>
    refine ⟨fun h => (Set.notMem_empty _ h).elim, fun ⟨_, h⟩ => ?_⟩
    exact absurd h (by simp [fixG])
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    have ha : 1 ≤ a := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, 1 ≤ b := fun b hb => hl b (List.mem_cons_of_mem a hb)
    obtain ⟨m, hm⟩ := fixW_even a ha x
    obtain ⟨k, hk⟩ := fixG_even l hl' γ
    show (x, γ) ∈ (Gb a ×ˢ Fl l) ∪ (Fb a ×ˢ Gl l) ↔
      (x * x, γ * γ) = ((1 : W a), (1 : Gam l)) ∧ fixW a x + fixG l γ = 2
    rw [Set.mem_union, Set.mem_prod, Set.mem_prod, mem_Fl_iff l γ, ih hl' γ, Prod.mk.injEq]
    show ((x * x = 1 ∧ fixW a x = 2) ∧ _) ∨ ((x * x = 1 ∧ fixW a x = 0) ∧ _) ↔ _
    constructor
    · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
      · exact ⟨⟨h1, h3⟩, by omega⟩
      · exact ⟨⟨h1, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h3⟩, h⟩
      by_cases hc : fixW a x = 2
      · exact Or.inl ⟨⟨h1, hc⟩, h3, by omega⟩
      · exact Or.inr ⟨⟨h1, by omega⟩, h3, by omega⟩

theorem Gl_sq {l : List ℕ} (hl : ∀ a ∈ l, 1 ≤ a) {γ : Gam l} (h : γ ∈ Gl l) : γ * γ = 1 :=
  ((mem_Gl_iff l hl γ).1 h).1

theorem disjoint_Fl_Gl (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) : Disjoint (Fl l) (Gl l) := by
  refine Set.disjoint_left.2 fun γ h1 h2 => ?_
  have e1 := ((mem_Fl_iff l γ).1 h1).2
  have e2 := ((mem_Gl_iff l hl γ).1 h2).2
  omega

theorem card_Gl (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) : Nat.card (Gl l) = dprod phiB psiB l := by
  induction l with
  | nil =>
    show Nat.card (∅ : Set (Gam [])) = 0
    exact Nat.card_of_isEmpty
  | cons a l ih =>
    have ha : 1 ≤ a := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, 1 ≤ b := fun b hb => hl b (List.mem_cons_of_mem a hb)
    have hdisj : Disjoint (Gb a ×ˢ Fl l) (Fb a ×ˢ Gl l) := by
      refine Set.disjoint_left.2 fun p h1 h2 => ?_
      exact Set.disjoint_left.1 (disjoint_Fb_Gb a) h2.1 h1.1
    show Nat.card ↥((Gb a ×ˢ Fl l) ∪ (Fb a ×ˢ Gl l)) = _
    rw [Nat.card_coe_set_eq, Set.ncard_union_eq hdisj, Set.ncard_prod, Set.ncard_prod,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, card_Gb_eq a ha, card_Fl l hl', card_Fb_eq a ha, ih hl']
    rfl

theorem card_Fl_union_Gl (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) :
    Nat.card ↥(Fl l ∪ Gl l) = (l.map phiB).prod + dprod phiB psiB l := by
  rw [Nat.card_coe_set_eq, Set.ncard_union_eq (disjoint_Fl_Gl l hl), ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq, card_Fl l hl, card_Gl l hl]

open scoped Classical in
@[expose] noncomputable def wtFG {D : Type*} (F G : Set D) (j : Fin 3) (x : D) : R8 :=
  (if x ∈ F then 1 else 0) + eR j * (if x ∈ G then 1 else 0)

@[expose] noncomputable def wtL (l : List ℕ) (j : Fin 3) (γ : Gam l) : R8 :=
  wtFG (Fl l) (Gl l) j γ

@[expose] noncomputable def tabL (l : List ℕ) (g : Gam l) : R8 := trSum (fun j => wtL l j) g

theorem wtFG_prod {D E : Type*} (F₁ G₁ : Set D) (F₂ G₂ : Set E) (hd : Disjoint F₁ G₁) (j : Fin 3)
    (x : D) (y : E) :
    wtFG (F₁ ×ˢ F₂) ((G₁ ×ˢ F₂) ∪ (F₁ ×ˢ G₂)) j (x, y) = wtFG F₁ G₁ j x * wtFG F₂ G₂ j y := by
  classical
  unfold wtFG
  simp only [Set.mem_prod, Set.mem_union]
  have hxx := eR_mul_self j
  by_cases h1 : x ∈ F₁
  · have h2 : x ∉ G₁ := fun h => Set.disjoint_left.1 hd h1 h
    by_cases h3 : y ∈ F₂ <;> by_cases h4 : y ∈ G₂ <;> simp [h1, h2, h3, h4]
  · by_cases h2 : x ∈ G₁ <;> by_cases h3 : y ∈ F₂ <;> by_cases h4 : y ∈ G₂ <;>
      simp [h1, h2, h3, h4]
    all_goals linear_combination (-1 : R8) * hxx

theorem wtL_cons (a : ℕ) (l : List ℕ) (j : Fin 3) (x : W a) (γ : Gam l) :
    wtL (a :: l) j (x, γ) = wtB a j x * wtL l j γ :=
  wtFG_prod (Fb a) (Gb a) (Fl l) (Gl l) (disjoint_Fb_Gb a) j x γ

theorem tabL_cons (a : ℕ) (l : List ℕ) (g : W a) (g' : Gam l) :
    tabL (a :: l) (g, g') = tabB a g * tabL l g' := by
  have h : (fun j => wtL (a :: l) j) = fun j (p : W a × Gam l) => wtB a j p.1 * wtL l j p.2 :=
    funext fun j => funext fun p => wtL_cons a l j p.1 p.2
  show trSum (D := W a × Gam l) (fun j => wtL (a :: l) j) (g, g') = _
  rw [h]
  exact trSum_prod (fun j => wtB a j) (fun j => wtL l j) g g'

theorem wtL_nil (j : Fin 3) (x : Gam []) : wtL [] j x = 1 := by
  classical
  have h1 : x ∈ Fl [] := Set.mem_univ x
  have h2 : x ∉ Gl [] := Set.notMem_empty x
  unfold wtL wtFG
  simp [h1, h2]

theorem tabL_nil (g : Gam []) : tabL [] g = 1 := by
  classical
  have : Unique (Gam []) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  unfold tabL trSum
  rw [finsum_unique, ite_eq_left (Subsingleton.elim _ _)]
  exact Finset.prod_eq_one fun j _ => wtL_nil j _

theorem sR_prod_wtFG_pos {D : Type*} (F G : Set D) (hFG : Disjoint F G) (t : Fin 3 → D)
    (hall : ∀ j, t j ∈ F ∪ G) : sR (∏ j, wtFG F G j (t j)) = 1 := by
  classical
  have h : ∏ j, wtFG F G j (t j) = ∏ j ∈ Finset.univ.filter (fun j => t j ∈ G), eR j := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold wtFG
    rcases hall j with h | h
    · have h' : t j ∉ G := fun h' => Set.disjoint_left.1 hFG h h'
      simp [h, h']
    · have h' : t j ∉ F := fun h' => Set.disjoint_left.1 hFG h' h
      simp [h, h']
  rw [h, sR_prod_eR]

theorem sR_prod_wtFG_neg {D : Type*} (F G : Set D) (t : Fin 3 → D)
    (hall : ¬ ∀ j, t j ∈ F ∪ G) : sR (∏ j, wtFG F G j (t j)) = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.1 hall
  have hj' : t j ∉ F ∧ t j ∉ G := by simpa [Set.mem_union] using hj
  have h : wtFG F G j (t j) = 0 := by
    unfold wtFG
    simp [hj'.1, hj'.2]
  rw [Finset.prod_eq_zero (f := fun j => wtFG F G j (t j)) (Finset.mem_univ j) h, map_zero]

@[expose] def triEquiv (D : Type*) : (D × D × D) ≃ (Fin 3 → D) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun t := (t 0, t 1, t 2)
  left_inv _ := rfl
  right_inv t := by
    funext i
    fin_cases i <;> rfl

theorem triEquiv_apply {D : Type*} (p : D × D × D) : triEquiv D p = ![p.1, p.2.1, p.2.2] := rfl

theorem sR_trSum_wtFG {D : Type*} [Group D] [Finite D] (F G : Set D) (hFG : Disjoint F G)
    (g : D) : sR (trSum (fun j => wtFG F G j) g) = (prodCnt (F ∪ G) g : ℤ) := by
  classical
  have := Fintype.ofFinite D
  unfold trSum
  rw [finsum_eq_sum_of_fintype, map_sum]
  have key : ∀ t : Fin 3 → D, sR (if t 0 * t 1 * t 2 = g then ∏ j, wtFG F G j (t j) else 0) =
      if (t 0 * t 1 * t 2 = g ∧ ∀ j, t j ∈ F ∪ G) then 1 else 0 := by
    intro t
    by_cases hg : t 0 * t 1 * t 2 = g
    · by_cases hall : ∀ j, t j ∈ F ∪ G
      · rw [ite_eq_left hg, ite_eq_left ⟨hg, hall⟩, sR_prod_wtFG_pos F G hFG t hall]
      · rw [ite_eq_left hg, ite_eq_right (fun h => hall h.2), sR_prod_wtFG_neg F G t hall]
    · rw [ite_eq_right hg, ite_eq_right (fun h => hg h.1), map_zero]
  simp_rw [key]
  rw [Finset.sum_boole]
  have hiff : ∀ p : D × D × D, (p.1 ∈ F ∪ G ∧ p.2.1 ∈ F ∪ G ∧ p.2.2 ∈ F ∪ G ∧
      p.1 * p.2.1 * p.2.2 = g) ↔ ((triEquiv D p) 0 * (triEquiv D p) 1 * (triEquiv D p) 2 = g ∧
      ∀ j, (triEquiv D p) j ∈ F ∪ G) := by
    rintro ⟨a, b, c⟩
    simp only [triEquiv_apply, Fin.forall_fin_succ]
    simp
    tauto
  have hcard : prodCnt (F ∪ G) g = (Finset.univ.filter (fun t : Fin 3 → D =>
      t 0 * t 1 * t 2 = g ∧ ∀ j, t j ∈ F ∪ G)).card := by
    unfold prodCnt
    rw [Nat.card_congr ((triEquiv D).subtypeEquiv (q := fun t : Fin 3 → D =>
      t 0 * t 1 * t 2 = g ∧ ∀ j, t j ∈ F ∪ G) hiff), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [hcard]

theorem tabL_one (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    tabL l 1 = (((l.map tauB).prod : ℕ) : R8) + ((dprod tauB tau2B l : ℕ) : R8) * sigR := by
  induction l with
  | nil => rw [tabL_nil]; simp [dprod]
  | cons a l ih =>
    have ha : 2 ≤ a := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, 2 ≤ b := fun b hb => hl b (List.mem_cons_of_mem a hb)
    have h1 : (1 : Gam (a :: l)) = ((1 : W a), (1 : Gam l)) := rfl
    rw [h1, tabL_cons, tabB_one a ha, ih hl']
    simp only [List.map_cons, List.prod_cons, dprod]
    push_cast
    linear_combination ((tau2B a : R8) * (dprod tauB tau2B l : R8)) * sigR_mul_self

theorem tabL_cL (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    tabL l (cL l) = (((l.map upsB).prod : ℕ) : R8) + ((dprod upsB ups2B l : ℕ) : R8) * sigR := by
  induction l with
  | nil => rw [tabL_nil]; simp [dprod]
  | cons a l ih =>
    have ha : 2 ≤ a := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, 2 ≤ b := fun b hb => hl b (List.mem_cons_of_mem a hb)
    show tabL (a :: l) (cc a, cL l) = _
    rw [tabL_cons, tabB_cc a ha, ih hl']
    simp only [List.map_cons, List.prod_cons, dprod]
    push_cast
    linear_combination ((ups2B a : R8) * (dprod upsB ups2B l : R8)) * sigR_mul_self

theorem prodCnt_FG_eq_sR (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) (g : Gam l) :
    (prodCnt (Fl l ∪ Gl l) g : ℤ) = sR (tabL l g) :=
  (sR_trSum_wtFG (Fl l) (Gl l) (disjoint_Fl_Gl l hl) g).symm

theorem prodCnt_FG_one (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    prodCnt (Fl l ∪ Gl l) 1 = (l.map tauB).prod + 3 * dprod tauB tau2B l := by
  have hl1 : ∀ a ∈ l, 1 ≤ a := fun a ha => by have := hl a ha; omega
  have h := prodCnt_FG_eq_sR l hl1 1
  have h2 := sR_cast_add_mul_sigR ((l.map tauB).prod : ℤ) (dprod tauB tau2B l : ℤ)
  rw [tabL_one l hl] at h
  simp only [Int.cast_natCast] at h2
  rw [h2] at h
  omega

theorem prodCnt_FG_cL (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    prodCnt (Fl l ∪ Gl l) (cL l) = (l.map upsB).prod + 3 * dprod upsB ups2B l := by
  have hl1 : ∀ a ∈ l, 1 ≤ a := fun a ha => by have := hl a ha; omega
  have h := prodCnt_FG_eq_sR l hl1 (cL l)
  have h2 := sR_cast_add_mul_sigR ((l.map upsB).prod : ℤ) (dprod upsB ups2B l : ℤ)
  rw [tabL_cL l hl] at h
  simp only [Int.cast_natCast] at h2
  rw [h2] at h
  omega

theorem modelFarG (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) (hbig : (∃ a ∈ l, 4 ≤ a) ∨ l = [2, 3]) :
    prodCnt (insert (1 : Gam l) (Fl l ∪ Gl l)) 1 <
      prodCnt (insert (1 : Gam l) (Fl l ∪ Gl l)) (cL l) := by
  have hl1 : ∀ a ∈ l, 1 ≤ a := fun a ha => by have := hl a ha; omega
  have hne : l ≠ [] := by
    rcases hbig with ⟨a, ha, _⟩ | rfl
    · exact List.ne_nil_of_mem ha
    · exact List.cons_ne_nil _ _
  have h1 : (1 : Gam l) ∉ Fl l ∪ Gl l := by
    rintro (h | h)
    · exact one_notMem_Fl l hne h
    · have h2 := ((mem_Gl_iff l hl1 1).1 h).2
      rw [fixG_one] at h2
      obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.map_cons, List.sum_cons] at h2
      have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (hl a List.mem_cons_self)
      omega
  have hle := prodCnt_one_le (F := Fl l ∪ Gl l)
    (fun w hw => hw.elim (fun h => Fl_sq h) (fun h => Gl_sq hl1 h)) h1
  have hge := prodCnt_ge h1 (Set.mem_union_left _ (cL_mem_Fl l hl1))
  rw [card_Fl_union_Gl l hl1, prodCnt_FG_one l hl] at hle
  rw [prodCnt_FG_cL l hl] at hge
  have hpi := prod_ineqG l hl hbig
  omega

end CFSG.OddStandard.AltStdSec.SylowSn
