module

public import CFSG.CGT.L5R.L2InputsLD
public import CFSG.CGT.M24R.L2Tab

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

@[expose] def bL (i : Fin 3) : N8 := n8 (betaW10 i)

@[expose] def gL : N8 := n8 gammaW10

@[expose] def dL (i : Fin 2) : N8 := n8 (dW10 i)

@[expose] def thL (i : Fin 2) : N8 := n8 (thW10 i)

@[expose] def nzL : N8 := n8 nzW10

@[expose] def wv2 {K : Type*} [Group K] (u : Fin 2 → K) (w : List (Fin 2)) : K := (w.map u).prod

theorem wv2_nil {K : Type*} [Group K] (u : Fin 2 → K) : wv2 u [] = 1 := rfl

theorem wv2_cons {K : Type*} [Group K] (u : Fin 2 → K) (k : Fin 2) (w : List (Fin 2)) :
    wv2 u (k :: w) = u k * wv2 u w := by
  simp [wv2]

theorem wv2_conj {K : Type*} [Group K] (e : K) (u : Fin 2 → K) (w : List (Fin 2)) :
    wv2 (fun k => e * u k * e⁻¹) w = e * wv2 u w * e⁻¹ := by
  induction w with
  | nil => simp [wv2_nil]
  | cons k w ih => rw [wv2_cons, wv2_cons, ih]; group

theorem wv2_mem {K : Type*} [Group K] {S : Subgroup K} {u : Fin 2 → K} (hu : ∀ k, u k ∈ S)
    (w : List (Fin 2)) : wv2 u w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons k w ih => rw [wv2_cons]; exact S.mul_mem (hu k) ih

theorem evT2_size (a : Fin 2 → Table) (w : List (Fin 2)) : (evT2 a w).size = 16 := by
  have key : ∀ (w : List (Fin 2)) (X : Table), X.size = 16 →
      (w.foldl (fun X k => compT 16 X (a k)) X).size = 16 := by
    intro w
    induction w with
    | nil => intro X h; exact h
    | cons l w ih => intro X _; exact ih _ (compT_size _ _)
  exact key w _ idT_size

section Tab

theorem evT2_isTab {a : Fin 2 → Table} {u : Fin 2 → N8} (h : ∀ k, IsTab (a k) (u k))
    (w : List (Fin 2)) : IsTab (evT2 a w) (wv2 u w) := by
  have key : ∀ (w : List (Fin 2)) (X : Table) (x : N8), IsTab X x →
      IsTab (w.foldl (fun X k => compT 16 X (a k)) X) (x * wv2 u w) := by
    intro w
    induction w with
    | nil => intro X x hX; simpa [wv2_nil] using hX
    | cons k w ih =>
      intro X x hX
      rw [List.foldl_cons, wv2_cons, ← mul_assoc]
      exact ih _ _ (hX.mul (h k))
  have := key w (idT 16) 1 IsTab.one
  rwa [one_mul] at this

theorem isTab_betaT (i : Fin 3) : IsTab (betaT i) (bL i) := isTab_wTab _

theorem isTab_gamT : IsTab gamT gL := isTab_wTab _

theorem isTab_dT2 (i : Fin 2) : IsTab (dT2 i) (dL i) := isTab_wTab _

theorem isTab_thT2 (i : Fin 2) : IsTab (thT2 i) (thL i) := isTab_wTab _

theorem isTab_nzW10 : IsTab (wTab nzW10) nzL := isTab_wTab _

end Tab

@[expose] def eightE {K : Type*} [Group K] (p q r : K) : List K :=
  [1, p, q, p * q, r, p * r, q * r, p * q * r]

theorem forall₂_eight {P Q R : Table} {p q r : N8}
    (hP : IsTab P p) (hQ : IsTab Q q) (hR : IsTab R r) :
    List.Forall₂ IsTab (eightT P Q R) (eightE p q r) :=
  .cons IsTab.one (.cons hP (.cons hQ (.cons (hP.mul hQ) (.cons hR (.cons (hP.mul hR)
    (.cons (hQ.mul hR) (.cons ((hP.mul hQ).mul hR) .nil)))))))

theorem eightT_size {P Q R : Table} (hP : P.size = 16) (hQ : Q.size = 16) (hR : R.size = 16) :
    ∀ X ∈ eightT P Q R, X.size = 16 := by
  intro X hX
  simp only [eightT, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idT_size
  · exact hP
  · exact hQ
  · exact compT_size _ _
  · exact hR
  · exact compT_size _ _
  · exact compT_size _ _
  · exact compT_size _ _

theorem exists_of_forall₂ {α β : Type*} {Rel : α → β → Prop} {Ls : List α} {Le : List β}
    (h : List.Forall₂ Rel Ls Le) {x : β} (hx : x ∈ Le) : ∃ Y ∈ Ls, Rel Y x := by
  induction h with
  | nil => simp at hx
  | cons hXx _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hXx⟩
    · obtain ⟨Y, hY, h⟩ := ih hx
      exact ⟨Y, List.mem_cons_of_mem _ hY, h⟩

theorem exists_of_forall₂' {α β : Type*} {Rel : α → β → Prop} {Ls : List α} {Le : List β}
    (h : List.Forall₂ Rel Ls Le) {X : α} (hX : X ∈ Ls) : ∃ x ∈ Le, Rel X x := by
  induction h with
  | nil => simp at hX
  | cons hXx _ ih =>
    rcases List.mem_cons.1 hX with rfl | hX
    · exact ⟨_, List.mem_cons_self, hXx⟩
    · obtain ⟨y, hy, h⟩ := ih hX
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem nodup_of_forall₂ {Ls : List Table} {Le : List N8}
    (h : List.Forall₂ IsTab Ls Le) (hs : ∀ X ∈ Ls, X.size = 16) (hn : Ls.Nodup) : Le.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons X x Ls Le hXx hrest ih =>
    rw [List.nodup_cons] at hn ⊢
    refine ⟨fun hx => hn.1 ?_, ih (fun Y hY => hs Y (List.mem_cons_of_mem _ hY)) hn.2⟩
    obtain ⟨Y, hY, hYx⟩ := exists_of_forall₂ hrest hx
    have := table_eq_of_rep hXx hYx (hs X List.mem_cons_self) (hs Y (List.mem_cons_of_mem _ hY))
    rw [this]
    exact hY

theorem mem_of_nodup_card {K : Type*} [Group K] [Finite K] {S : Subgroup K} {Le : List K}
    (hn : Le.Nodup) (hmem : ∀ x ∈ Le, x ∈ S) (hc : Nat.card S ≤ Le.length) :
    ∀ z ∈ S, z ∈ Le := by
  classical
  have hsub : (Le.toFinset : Set K) ⊆ (S : Set K) := fun x hx => hmem x (by simpa using hx)
  have h1 : (Le.toFinset : Set K).ncard = Le.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hn]
  have h2 : (S : Set K).ncard = Nat.card S := by rw [← Nat.card_coe_set_eq]; rfl
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  intro z hz
  have : z ∈ (Le.toFinset : Set K) := by rw [heq]; exact hz
  simpa using this

end CFSG.CGT.L5R
