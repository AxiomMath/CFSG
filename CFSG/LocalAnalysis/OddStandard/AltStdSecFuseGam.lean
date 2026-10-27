module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowGam

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] noncomputable def fixG : (l : List ℕ) → Gam l → ℕ
  | [], _ => 0
  | a :: l, x => fixW a x.1 + fixG l x.2

@[expose] def Fl : (l : List ℕ) → Set (Gam l)
  | [] => Set.univ
  | a :: l => Fb a ×ˢ Fl l

@[expose] noncomputable def cL : (l : List ℕ) → Gam l
  | [] => 1
  | a :: l => (cc a, cL l)

theorem fixG_one (l : List ℕ) : fixG l 1 = (l.map (fun a => 2 ^ a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show fixW a 1 + fixG l 1 = _
    rw [fixW_one, ih, List.map_cons, List.sum_cons]

theorem mem_Fl_iff (l : List ℕ) (γ : Gam l) : γ ∈ Fl l ↔ γ * γ = 1 ∧ fixG l γ = 0 := by
  induction l with
  | nil => exact ⟨fun _ => ⟨Subsingleton.elim _ _, rfl⟩, fun _ => Set.mem_univ _⟩
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    show (x, γ) ∈ Fb a ×ˢ Fl l ↔
      (x * x, γ * γ) = ((1 : W a), (1 : Gam l)) ∧ fixW a x + fixG l γ = 0
    rw [Set.mem_prod]
    show (x ∈ Fb a ∧ γ ∈ Fl l) ↔ _
    rw [ih γ, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h3⟩, h⟩
      exact ⟨⟨h1, by omega⟩, h3, by omega⟩

theorem Fl_sq {l : List ℕ} {γ : Gam l} (h : γ ∈ Fl l) : γ * γ = 1 := ((mem_Fl_iff l γ).1 h).1

theorem cL_mem_Fl (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) : cL l ∈ Fl l := by
  induction l with
  | nil => exact Set.mem_univ _
  | cons a l ih =>
    exact Set.mk_mem_prod (cc_mem_Fb a (hl a List.mem_cons_self))
      (ih fun b hb => hl b (List.mem_cons_of_mem a hb))

theorem one_notMem_Fl (l : List ℕ) (hl : l ≠ []) : (1 : Gam l) ∉ Fl l := by
  intro h
  have h0 := ((mem_Fl_iff l 1).1 h).2
  rw [fixG_one] at h0
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [List.map_cons, List.sum_cons] at h0
  have : 0 < 2 ^ a := Nat.two_pow_pos a
  omega

theorem prodCnt_univ_nil (g : Gam []) : prodCnt (Set.univ : Set (Gam [])) g = 1 := by
  rw [prodCnt, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩,
    ⟨⟨(1, 1, 1), trivial, trivial, trivial, Subsingleton.elim _ _⟩⟩⟩

theorem prodCnt_Fl_one (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) :
    prodCnt (Fl l) 1 = (l.map tauB).prod := by
  induction l with
  | nil => exact prodCnt_univ_nil 1
  | cons a l ih =>
    show prodCnt (Fb a ×ˢ Fl l) ((1 : W a), (1 : Gam l)) = _
    rw [prodCnt_prod, prodCnt_Fb_one_eq a (hl a List.mem_cons_self),
      ih fun b hb => hl b (List.mem_cons_of_mem a hb), List.map_cons, List.prod_cons]

theorem prodCnt_Fl_cL (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) :
    prodCnt (Fl l) (cL l) = (l.map upsB).prod := by
  induction l with
  | nil => exact prodCnt_univ_nil _
  | cons a l ih =>
    show prodCnt (Fb a ×ˢ Fl l) (cc a, cL l) = _
    rw [prodCnt_prod, prodCnt_Fb_cc_eq a (hl a List.mem_cons_self),
      ih fun b hb => hl b (List.mem_cons_of_mem a hb), List.map_cons, List.prod_cons]

theorem card_Fl (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) : Nat.card (Fl l) = (l.map phiB).prod := by
  induction l with
  | nil =>
    have : Unique (Gam []) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    show Nat.card (Set.univ : Set (Gam [])) = 1
    rw [Nat.card_univ, Nat.card_unique]
  | cons a l ih =>
    show Nat.card (↥(Fb a ×ˢ Fl l)) = _
    rw [Nat.card_congr (Equiv.Set.prod (Fb a) (Fl l)), Nat.card_prod,
      card_Fb_eq a (hl a List.mem_cons_self), ih fun b hb => hl b (List.mem_cons_of_mem a hb),
      List.map_cons, List.prod_cons]

theorem modelFar (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) (hbig : (∃ a ∈ l, 4 ≤ a) ∨ l = [2, 3]) :
    prodCnt (insert (1 : Gam l) (Fl l)) 1 < prodCnt (insert (1 : Gam l) (Fl l)) (cL l) := by
  have hl1 : ∀ a ∈ l, 1 ≤ a := fun a ha => by have := hl a ha; omega
  have hne : l ≠ [] := by
    rcases hbig with ⟨a, ha, _⟩ | rfl
    · exact List.ne_nil_of_mem ha
    · exact List.cons_ne_nil _ _
  have h1 : (1 : Gam l) ∉ Fl l := one_notMem_Fl l hne
  have hle := prodCnt_one_le (fun w hw => Fl_sq hw) h1
  have hge := prodCnt_ge h1 (cL_mem_Fl l hl1)
  rw [prodCnt_Fl_one l hl1, card_Fl l hl1] at hle
  rw [prodCnt_Fl_cL l hl1] at hge
  have hpi := prod_ineq l hl1 hbig
  omega

end CFSG.OddStandard.AltStdSec.SylowSn
