module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

section Index

variable {r : ℕ}

@[expose] def nodeIdx : Option (Fin r) → ℕ
  | none => 0
  | some j => (j : ℕ) + 1

@[expose] def idxNode (i : ℕ) : Option (Fin r) :=
  if h : 0 < i ∧ i - 1 < r then some ⟨i - 1, h.2⟩ else none

theorem idxNode_nodeIdx (x : Option (Fin r)) : idxNode (nodeIdx x) = x := by
  cases x with
  | none => simp [nodeIdx, idxNode]
  | some j =>
    have h : 0 < (j : ℕ) + 1 ∧ (j : ℕ) + 1 - 1 < r := ⟨by omega, by simp⟩
    rw [nodeIdx, idxNode, dite_eq_left_of_eq_true (eq_true h)]
    congr 1

theorem nodeIdx_lt (x : Option (Fin r)) : nodeIdx x < r + 1 := by
  cases x with
  | none => simp [nodeIdx]
  | some j =>
    have := j.2
    simp only [nodeIdx]
    omega

theorem nodeIdx_injective : Function.Injective (nodeIdx (r := r)) :=
  Function.LeftInverse.injective idxNode_nodeIdx

theorem nodeIdx_idxNode {i : ℕ} (hi : i < r + 1) : nodeIdx (idxNode (r := r) i) = i := by
  unfold idxNode
  split_ifs with h
  · simp only [nodeIdx]
    omega
  · simp only [nodeIdx]
    omega

end Index

section Tree

@[expose] def treePath (anc : ℕ → List ℕ) (a b : ℕ) : List ℕ :=
  (anc a).filter (fun w => !(anc b).elem w) ++
    ((anc a).filter (fun w => (anc b).elem w)).take 1 ++
      ((anc b).filter (fun w => !(anc a).elem w)).reverse

@[expose] def chainB (E : List (ℕ × ℕ)) : List ℕ → Bool
  | a :: b :: l => E.elem (a, b) && chainB E (b :: l)
  | _ => true

structure IsTreePaths (n : ℕ) (E : List (ℕ × ℕ)) (tp : ℕ → ℕ → List ℕ) : Prop where
  self : ∀ a < n, tp a a = [a]
  lt : ∀ a < n, ∀ b < n, ∀ w ∈ tp a b, w < n
  head : ∀ a < n, ∀ b < n, (tp a b).head? = some a
  last : ∀ a < n, ∀ b < n, (tp a b).getLast? = some b
  chain : ∀ a < n, ∀ b < n, chainB E (tp a b) = true
  step : ∀ x < n, ∀ e ∈ E, ∀ w ∈ tp x e.2, w ∈ tp x e.1 ∨ w = e.2

theorem eqvGen_of_chainB {E : List (ℕ × ℕ)} {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (hR : ∀ u v, (u, v) ∈ E → P u → P v → R u v) :
    ∀ (l : List ℕ) (a b : ℕ), chainB E (a :: l) = true → (a :: l).getLast? = some b →
      (∀ w ∈ a :: l, P w) → Relation.EqvGen R a b := by
  intro l
  induction l with
  | nil =>
    intro a b _ hb _
    simp only [List.getLast?_singleton, Option.some.injEq] at hb
    subst hb
    exact Relation.EqvGen.refl a
  | cons c t ih =>
    intro a b hc hb hP
    simp only [chainB, Bool.and_eq_true, List.elem_eq_mem, decide_eq_true_eq] at hc
    have hb' : (c :: t).getLast? = some b := by
      rw [← hb, List.getLast?_cons_cons]
    have h1 : R a c := hR a c hc.1 (hP a (by simp)) (hP c (by simp))
    exact (Relation.EqvGen.rel a c h1).trans _ _ _
      (ih c b hc.2 hb' fun w hw => hP w (List.mem_cons_of_mem a hw))

theorem eqvGen_map {α β : Type*} {R : β → β → Prop} (f : α → β) {a b : α}
    (h : Relation.EqvGen (fun u v => R (f u) (f v)) a b) : Relation.EqvGen R (f a) (f b) := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ huv
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

@[expose] def compIdx (n : ℕ) (tp : ℕ → ℕ → List ℕ) (zl : List ℕ) (x : ℕ) : List ℕ :=
  (List.range n).filter fun y => (tp x y).all fun w => zl.elem w

@[expose] def sameSet (a b : List ℕ) : Bool := a.all (b.elem ·) && b.all (a.elem ·)

theorem mem_iff_of_sameSet {a b : List ℕ} (h : sameSet a b = true) (y : ℕ) : y ∈ a ↔ y ∈ b := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.elem_eq_mem,
    decide_eq_true_eq] at h
  exact ⟨h.1 y, h.2 y⟩

end Tree

namespace KacData

variable {τ : Tag} (K : KacData τ)

theorem adj_symm {x y : Option (Fin τ.rank)} (h : K.Adj x y) : K.Adj y x :=
  ⟨h.1.symm, by rw [iform_comm]; exact h.2⟩

theorem comp_eq_treePath {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hE : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)} (hx : K.IsZ p μ x) :
    K.comp p μ x = {y | ∀ w ∈ tp (nodeIdx x) (nodeIdx y), K.IsZ p μ (idxNode w)} := by
  set S : Set (Option (Fin τ.rank)) :=
    {y | ∀ w ∈ tp (nodeIdx x) (nodeIdx y), K.IsZ p μ (idxNode w)} with hS
  have hclosed : ∀ a b, K.ZRel p μ a b → a ∈ S → b ∈ S := by
    intro a b hab ha w hw
    have he : (nodeIdx a, nodeIdx b) ∈ E := (hE a b).1 hab.2.2
    rcases hT.step _ (nodeIdx_lt x) _ he w hw with hw' | hw'
    · exact ha w hw'
    · rw [hw', idxNode_nodeIdx]
      exact hab.2.1
  have hiff : ∀ a b, Relation.EqvGen (K.ZRel p μ) a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    induction h with
    | rel a b hab =>
      exact ⟨hclosed a b hab, hclosed b a ⟨hab.2.1, hab.1, K.adj_symm hab.2.2⟩⟩
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hxS : x ∈ S := by
    intro w hw
    rw [hT.self _ (nodeIdx_lt x), List.mem_singleton] at hw
    rw [hw, idxNode_nodeIdx]
    exact hx
  ext y
  constructor
  · rintro ⟨-, hxy⟩
    exact (hiff x y hxy).1 hxS
  · intro hy
    have hlast := hT.last _ (nodeIdx_lt x) _ (nodeIdx_lt y)
    have hyZ : K.IsZ p μ y := by
      have := hy (nodeIdx y) (List.mem_of_getLast? hlast)
      rwa [idxNode_nodeIdx] at this
    refine ⟨hyZ, ?_⟩
    have hhead := hT.head _ (nodeIdx_lt x) _ (nodeIdx_lt y)
    obtain ⟨t, ht⟩ : ∃ t, tp (nodeIdx x) (nodeIdx y) = nodeIdx x :: t := by
      cases h : tp (nodeIdx x) (nodeIdx y) with
      | nil => rw [h] at hhead; simp at hhead
      | cons c t =>
        rw [h, List.head?_cons, Option.some.injEq] at hhead
        exact ⟨t, by rw [hhead]⟩
    have hlt := hT.lt _ (nodeIdx_lt x) _ (nodeIdx_lt y)
    have hR : ∀ u v, (u, v) ∈ E → (u < τ.rank + 1 ∧ K.IsZ p μ (idxNode u)) →
        (v < τ.rank + 1 ∧ K.IsZ p μ (idxNode v)) →
          K.ZRel p μ (idxNode u) (idxNode v) := by
      intro u v huv hu hv
      refine ⟨hu.2, hv.2, (hE _ _).2 ?_⟩
      rw [nodeIdx_idxNode hu.1, nodeIdx_idxNode hv.1]
      exact huv
    have h := eqvGen_of_chainB (R := fun u v => K.ZRel p μ (idxNode u) (idxNode v)) hR t
      (nodeIdx x) (nodeIdx y) (ht ▸ hT.chain _ (nodeIdx_lt x) _ (nodeIdx_lt y)) (ht ▸ hlast)
      (fun w hw => ⟨hlt w (ht ▸ hw), hy w (ht ▸ hw)⟩)
    have h' := eqvGen_map (R := K.ZRel p μ) idxNode h
    rwa [idxNode_nodeIdx, idxNode_nodeIdx] at h'

open Classical in
@[expose] noncomputable def zeroIdx (p : ℕ) (μ : Fin τ.rank → ℤ) : List ℕ :=
  (List.range (τ.rank + 1)).filter fun i => decide (K.IsZ p μ (idxNode i))

theorem mem_zeroIdx {p : ℕ} {μ : Fin τ.rank → ℤ} {i : ℕ} :
    i ∈ K.zeroIdx p μ ↔ i < τ.rank + 1 ∧ K.IsZ p μ (idxNode i) := by
  classical
  simp [zeroIdx]

theorem zeroIdx_mem_sublists (p : ℕ) (μ : Fin τ.rank → ℤ) :
    K.zeroIdx p μ ∈ (List.range (τ.rank + 1)).sublists :=
  List.mem_sublists.2 List.filter_sublist

theorem comp_eq_compIdx {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hE : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)} (hx : K.IsZ p μ x) :
    K.comp p μ x = {y | nodeIdx y ∈ compIdx (τ.rank + 1) tp (K.zeroIdx p μ) (nodeIdx x)} := by
  rw [K.comp_eq_treePath hT hE hx]
  ext y
  simp only [Set.mem_ofPred_eq, compIdx, List.mem_filter, List.mem_range, List.all_eq_true,
    List.elem_eq_mem, decide_eq_true_eq, K.mem_zeroIdx]
  have hlt := hT.lt _ (nodeIdx_lt x) _ (nodeIdx_lt y)
  exact ⟨fun h => ⟨nodeIdx_lt y, fun w hw => ⟨hlt w hw, h w hw⟩⟩,
    fun h w hw => (h.2 w hw).2⟩

theorem exists_comp_eq_of_check {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hE : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)} {adm : List ℕ → Bool}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !adm zl || zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    {p : ℕ} {μ : Fin τ.rank → ℤ} (hadm : adm (K.zeroIdx p μ) = true)
    {x : Option (Fin τ.rank)} (hx : K.IsZ p μ x) :
    ∃ c ∈ cands, K.comp p μ x = {y | nodeIdx y ∈ c} := by
  have h := List.all_eq_true.1 hcheck _ (K.zeroIdx_mem_sublists p μ)
  rw [hadm, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have hxz : nodeIdx x ∈ K.zeroIdx p μ :=
    K.mem_zeroIdx.2 ⟨nodeIdx_lt x, by rw [idxNode_nodeIdx]; exact hx⟩
  obtain ⟨c, hc, hsame⟩ := List.any_eq_true.1 (h _ hxz)
  refine ⟨c, hc, ?_⟩
  rw [K.comp_eq_compIdx hT hE hx]
  ext y
  exact mem_iff_of_sameSet hsame (nodeIdx y)

@[expose] def label (i : ℕ) : ℤ :=
  match idxNode (r := τ.rank) i with
  | none => 1
  | some j => K.θ j

end KacData

end CFSG.HardMathSupport.Timmesfeld.CrossChar
