module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lists
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeFam

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint.Chevalley

structure NodeTab (s : N6) where
  A : ℕ
  B : ℕ
  wTab : List (List N6)
  uTab : List (List N6)
  v0 : List ℤ
  xorb : List (List ℤ)
  hv0len : v0.length = Tag.rank .E6
  hv0 : ∀ j : N6, j ≠ s → reflectL6 j v0 = v0
  hU1 : ∀ j : Fin B, (uTab.getD j []).foldr refEL (List.ofFn (alphaF s)) = List.ofFn (alphaF s)
  hU2 : ∀ j : Fin B, (uTab.getD j []).foldr reflectL6 (List.ofFn (Pi.single s (1 : ℤ) : N6 → ℤ)) =
    List.ofFn (Pi.single s (1 : ℤ) : N6 → ℤ)
  hdist : ∀ j j' : Fin B, j ≠ j' →
    (uTab.getD j []).foldr reflectL6 v0 ≠ (uTab.getD j' []).foldr reflectL6 v0
  hβ : ∀ i i' : Fin A, i ≠ i' →
    1 ≤ contentL (subL ((wTab.getD i []).foldr refEL (List.ofFn (alphaF s)))
      ((wTab.getD i' []).foldr refEL (List.ofFn (alphaF s)))) ∧
    contentL (subL ((wTab.getD i []).foldr refEL (List.ofFn (alphaF s)))
      ((wTab.getD i' []).foldr refEL (List.ofFn (alphaF s)))) ≤ 2
  hbdβ : ∀ i : Fin A, ∀ c ∈ (wTab.getD i []).foldr refEL (List.ofFn (alphaF s)), |c| ≤ 2
  hY : ∀ j j' : Fin B, j ≠ j' →
    (uTab.getD j []).foldr refEL (List.ofFn (omegaF s)) ≠
      (uTab.getD j' []).foldr refEL (List.ofFn (omegaF s))
  hbdX : ∀ (i : Fin A) (j : Fin B), ∀ c ∈ (wTab.getD i []).foldr refEL
    ((uTab.getD j []).foldr refEL (List.ofFn (omegaF s))), |c| ≤ 2
  hmem : ∀ (i : Fin A) (j : Fin B), (wTab.getD i []).foldr refEL
    ((uTab.getD j []).foldr refEL (List.ofFn (omegaF s))) ∈ xorb
  hxorb : ∀ x ∈ xorb, ∀ y ∈ xorb, x ≠ y → 1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2

namespace NodeTab

variable {s : N6} (T : NodeTab s)

@[expose] def wW (i : Fin T.A) : List N6 := T.wTab.getD i []

@[expose] def uW (j : Fin T.B) : List N6 := T.uTab.getD j []

@[expose] def v0F : N6 → ℤ := fun i => T.v0.getD i 0

theorem ofFn_v0F : List.ofFn T.v0F = T.v0 := by
  refine List.ext_getElem (by simp [T.hv0len]) fun n h1 h2 => ?_
  simp [v0F, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem refE_involutive (j : N6) (x : N6 → ℤ) : refE j (refE j x) = x := by
  ext i
  simp only [refE, Tag.cartan_self]
  ring

theorem foldr_refE_injective (l : List N6) : Function.Injective (l.foldr refE) := by
  induction l with
  | nil => exact fun _ _ h => h
  | cons j l ih =>
    intro x y h
    simp only [List.foldr_cons] at h
    have := congrArg (refE j) h
    rw [refE_involutive, refE_involutive] at this
    exact ih this

theorem contentL_subL_self (L : List ℤ) : contentL (subL L L) = 0 := by
  have : ∀ (g : ℕ) (L : List ℤ),
      (subL L L).foldl (fun g x => Nat.gcd g x.natAbs) g = g := by
    intro g L
    induction L generalizing g with
    | nil => rfl
    | cons a t ih =>
      simp only [subL, List.zipWith_cons_cons, sub_self, Int.natAbs_zero, Nat.gcd_zero_right,
        List.foldl_cons]
      exact ih g
  exact this 0 L

theorem unit_of_content {x y : List ℤ}
    (h : 1 ≤ contentL (subL x y) ∧ contentL (subL x y) ≤ 2) : x ≠ y := by
  rintro rfl
  have := contentL_subL_self x
  omega

theorem fam_hU (j : Fin T.B) : (T.uW j).foldr refE (alphaF s) = alphaF s := by
  apply List.ofFn_injective
  rw [ofFn_foldr_refEL]
  exact T.hU1 j

theorem fam_hU2 (j : Fin T.B) :
    (T.uW j).foldr (reflect Tag.E6) (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
  apply List.ofFn_injective
  rw [ofFn_foldr_reflect6]
  exact T.hU2 j

theorem fam_hv0 (j : N6) (hj : j ≠ s) : reflect Tag.E6 j T.v0F = T.v0F := by
  apply List.ofFn_injective
  rw [ofFn_reflect6, ofFn_v0F]
  exact T.hv0 j hj

theorem fam_hdist (j j' : Fin T.B) (h : j ≠ j') :
    (T.uW j).foldr (reflect Tag.E6) T.v0F ≠ (T.uW j').foldr (reflect Tag.E6) T.v0F := by
  intro he
  apply T.hdist j j' h
  have := congrArg List.ofFn he
  rwa [ofFn_foldr_reflect6, ofFn_foldr_reflect6, ofFn_v0F] at this

theorem ofFn_famB (i : Fin T.A) :
    List.ofFn (famB s T.wW i) =
      (T.wTab.getD (i : ℕ) []).foldr refEL (List.ofFn (alphaF s)) := by
  unfold famB
  rw [ofFn_foldr_refEL]
  rfl

theorem ofFn_famY (j : Fin T.B) :
    List.ofFn (famY s T.uW j) =
      (T.uTab.getD (j : ℕ) []).foldr refEL (List.ofFn (omegaF s)) := by
  unfold famY
  rw [ofFn_foldr_refEL]
  rfl

theorem ofFn_famX (i : Fin T.A) (j : Fin T.B) :
    List.ofFn (famX s T.wW T.uW i j) =
      (T.wTab.getD (i : ℕ) []).foldr refEL
        ((T.uTab.getD (j : ℕ) []).foldr refEL (List.ofFn (omegaF s))) := by
  unfold famX
  rw [ofFn_foldr_refEL, ofFn_famY]
  rfl

theorem fam_hβinj (i i' : Fin T.A) (h : famB s T.wW i = famB s T.wW i') : i = i' := by
  by_contra hne
  have := T.hβ i i' hne
  have h2 := unit_of_content this
  apply h2
  rw [← ofFn_famB, ← ofFn_famB]
  exact congrArg List.ofFn h

theorem fam_hβ (i i' : Fin T.A) (h : famB s T.wW i ≠ famB s T.wW i') :
    Cont2 (famB s T.wW i - famB s T.wW i') := by
  have hii : i ≠ i' := fun e => h (e ▸ rfl)
  apply cont2_of_contentL
  rw [ofFn_famB, ofFn_famB]
  exact T.hβ i i' hii

theorem fam_bdβ (i : Fin T.A) (c : N6) : |famB s T.wW i c| ≤ 2 := by
  apply T.hbdβ i
  rw [← ofFn_famB]
  exact List.mem_ofFn.2 ⟨c, rfl⟩

theorem fam_bdX (i : Fin T.A) (j : Fin T.B) (c : N6) : |famX s T.wW T.uW i j c| ≤ 2 := by
  apply T.hbdX i j
  rw [← ofFn_famX]
  exact List.mem_ofFn.2 ⟨c, rfl⟩

theorem fam_hX (i i' : Fin T.A) (j j' : Fin T.B)
    (h : famX s T.wW T.uW i j ≠ famX s T.wW T.uW i' j') :
    Cont2 (famX s T.wW T.uW i j - famX s T.wW T.uW i' j') := by
  apply cont2_of_contentL
  rw [ofFn_famX, ofFn_famX]
  apply T.hxorb _ (T.hmem i j) _ (T.hmem i' j')
  intro he
  apply h
  apply List.ofFn_injective
  rw [ofFn_famX, ofFn_famX]
  exact he

theorem fam_hinj (i i' : Fin T.A) (j j' : Fin T.B)
    (hX : famX s T.wW T.uW i j = famX s T.wW T.uW i' j')
    (hB : famB s T.wW i = famB s T.wW i') : i = i' ∧ j = j' := by
  have hii := fam_hβinj T i i' hB
  subst hii
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hY : famY s T.uW j = famY s T.uW j' :=
    foldr_refE_injective (T.wW i) hX
  apply T.hY j j' hne
  rw [← ofFn_famY, ← ofFn_famY]
  exact congrArg List.ofFn hY

end NodeTab

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
