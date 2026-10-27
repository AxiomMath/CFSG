module

public import Certificates.Data.E4QuatArr
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.E4QuatCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n : ℕ}

section Lists

variable {α β : Type*} {R : α → β → Prop}

theorem all_eq_of_forall₂ {f : α → Bool} {g : β → Bool} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hfg : ∀ a b, R a b → f a = g b) : l₁.all f = l₂.all g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.all_cons, ih, hfg _ _ hab]

theorem any_eq_of_forall₂ {f : α → Bool} {g : β → Bool} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hfg : ∀ a b, R a b → f a = g b) : l₁.any f = l₂.any g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.any_cons, ih, hfg _ _ hab]

end Lists

theorem rep_inv {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ :=
  CFSG.Sporadic.SuzRecog.ModelGroups.rep_invCand ht

theorem eqA_eq {a b : Array ℕ} {g h : Equiv.Perm (Fin n)} (ha : Rep n a g) (hb : Rep n b h) :
    eqA n a b = decide (g = h) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact eqA_iff ha hb

theorem rep_conjA {h x : Array ℕ} {a b : Equiv.Perm (Fin n)} (hh : Rep n h a) (hx : Rep n x b) :
    Rep n (conjA n h x) (a * b * a⁻¹) :=
  rep_compA (rep_compA hh hx) (rep_inv hh)

theorem rep_getD {LA : List (Array ℕ)} {LP : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) LA LP) (k : ℕ) : Rep n (LA.getD k (idA n)) (LP.getD k 1) := by
  induction h generalizing k with
  | nil => simpa using rep_idA
  | cons hab _ ih =>
    cases k with
    | zero => simpa using hab
    | succ k => simpa using ih k

theorem memA_eq {LA : List (Array ℕ)} {LP : List (Equiv.Perm (Fin n))} {x : Array ℕ}
    {g : Equiv.Perm (Fin n)} (hx : Rep n x g) (hL : List.Forall₂ (Rep n) LA LP) :
    memA n LA x = decide (g ∈ LP) := by
  induction hL with
  | nil => simp [memA]
  | cons hab _ ih =>
    simp only [memA] at ih ⊢
    rw [List.any_cons, ih, eqA_eq hx hab]
    simp [List.mem_cons]

theorem forall₂_q8A {r i j : Array ℕ} {R I J : Equiv.Perm (Fin n)} (hr : Rep n r R)
    (hi : Rep n i I) (hj : Rep n j J) :
    List.Forall₂ (Rep n) (q8A n r i j) (q8Elems R I J) :=
  .cons rep_idA (.cons hr (.cons hi (.cons (rep_compA hi hr) (.cons hj (.cons (rep_compA hj hr)
    (.cons (rep_compA hi hj) (.cons (rep_compA (rep_compA hi hj) hr) .nil)))))))

variable {LA : List (Array ℕ)} {LP : List (Equiv.Perm (Fin n))} {i j : Array ℕ}
  {I J : Equiv.Perm (Fin n)}

theorem normsA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {h : Array ℕ} {H : Equiv.Perm (Fin n)} (hh : Rep n h H) :
    normsA n LA i j h = norms LP I J H := by
  rw [normsA, norms, memA_eq (rep_conjA hh hi) hL, memA_eq (rep_conjA hh hj) hL]

theorem edgeCheckA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : Rep n g G) :
    edgeCheckA n LA i j g = edgeCheck LP I J G := by
  rw [edgeCheckA, edgeCheck, normsA_eq hL hi hj hg, normsA_eq hL hi hj (rep_conjA hg hi),
    normsA_eq hL hi hj (rep_conjA hg hj)]

end CFSG.ClassicalInvolution.Q3.TL4.E4A
