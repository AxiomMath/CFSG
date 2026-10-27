module

public import CFSG.Certificates.Kernel.SporSch.KeyBfsClosed
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

namespace CFSG.KS.ClassOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.KS.KeyBfs CFSG.KS.Tbl

variable {n : Nat}

theorem key_eq_of_rep {S T : Table} {g : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T g) :
    key n S = key n T := by
  rw [key_eq_foldr, key_eq_foldr]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [hS i hi, hT i hi]

theorem rep_unique {T : Table} {g h : Equiv.Perm (Fin n)} (hg : Rep n T g) (hh : Rep n T h) :
    g = h :=
  key_inj hg hh rfl

theorem tblEq_refl (T : Table) : tblEq n T T = true := by
  unfold tblEq
  rw [allIn_eq_true]
  intro i _ _
  exact beq_self_eq_true _

section Closure

variable {gens gensInv : Array Table} {γ : Nat → Equiv.Perm (Fin n)}
  {C : Set (Equiv.Perm (Fin n))}

theorem conjClosure_one (hn : n < 2 ^ 32)
    (hg : ∀ l < gens.size, Rep n gens[l]! (γ l) ∧ Rep n gensInv[l]! (γ l)⁻¹)
    (hCf : C.Finite) (hCcl : ∀ l < gens.size, ∀ x ∈ C, γ l * x * (γ l)⁻¹ ∈ C)
    (hmin : ∀ g ∈ C, ∀ D : Set (Equiv.Perm (Fin n)), D.Finite → g ∈ D →
      (∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D) → C ⊆ D)
    {x : Table} {g₀ : Equiv.Perm (Fin n)} (hx : Rep n x g₀) (hg₀ : g₀ ∈ C) {cap : Nat}
    (hcap : C.ncard ≤ cap) :
    conjTreeOK n gens gensInv x (conjClosure n gens gensInv x cap).1
        (conjClosure n gens gensInv x cap).2.1 (conjClosure n gens gensInv x cap).2.2 = true ∧
      keysDistinct n (conjClosure n gens gensInv x cap).1.toList = true ∧
      (conjClosure n gens gensInv x cap).1.size = C.ncard ∧
      ∀ y ∈ C, ∃ i < (conjClosure n gens gensInv x cap).1.size,
        Rep n (conjClosure n gens gensInv x cap).1[i]! y := by
  classical
  let Good : Table → Prop := fun T => ∃ g ∈ C, Rep n T g
  let K : Finset Nat := hCf.toFinset.image fun g => key n (toTable g)
  have hK : ∀ T, Good T → key n T ∈ K := by
    rintro T ⟨g, hgC, hT⟩
    exact Finset.mem_image.2 ⟨g, hCf.mem_toFinset.2 hgC, key_eq_of_rep (rep_toTable hn g) hT⟩
  have hKc : K.card ≤ cap := by
    refine (Finset.card_image_le).trans ?_
    rw [← Set.ncard_eq_toFinset_card C hCf]
    exact hcap
  have hstep : ∀ l < gens.size, ∀ T, Good T → Good (conjT n gens[l]! gensInv[l]! T) := by
    rintro l hl T ⟨g, hgC, hT⟩
    exact ⟨_, hCcl l hl g hgC, rep_conjT (hg l hl).1 (hg l hl).2 hT⟩
  have R := keyBfs_closed (st := fun l y => conjT n gens[l]! gensInv[l]! y) (root := x)
    (Good := Good) ⟨g₀, hg₀, hx⟩ hstep hK hKc
  rw [← CFSG.KS.KeyBfs.conjClosure_eq] at R
  generalize conjClosure n gens gensInv x cap = r at R ⊢
  obtain ⟨E, par, lab⟩ := r
  obtain ⟨rpos, rps, rls, rroot, rgood, rinj, rtree, rclose⟩ := R
  simp only at rpos rps rls rroot rgood rinj rtree rclose ⊢
  choose! φ hφC hφ using rgood
  let D : Set (Equiv.Perm (Fin n)) := φ '' {i | i < E.size}
  have hDC : D ⊆ C := by
    rintro _ ⟨i, hi, rfl⟩
    exact hφC i hi
  have hφ0 : φ 0 = g₀ := by
    have := hφ 0 rpos
    rw [rroot] at this
    exact rep_unique this hx
  have hDcl : ∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D := by
    rintro l hl _ ⟨i, hi, rfl⟩
    obtain ⟨q, hq, e⟩ := rclose i hi l hl
    have h1 := rep_conjT (hg l hl).1 (hg l hl).2 (hφ i hi)
    exact ⟨q, hq, (key_inj (hφ q hq) h1 e.symm)⟩
  have hCD : C ⊆ D := hmin g₀ hg₀ D (hCf.subset hDC) ⟨0, rpos, hφ0⟩ hDcl
  have hφinj : Set.InjOn φ {i | i < E.size} := fun a ha b hb e =>
    rinj a ha b hb (by rw [key_eq_of_rep (hφ a ha) (rep_toTable hn _),
      key_eq_of_rep (hφ b hb) (rep_toTable hn _), e])
  have hsize : E.size = C.ncard := by
    rw [← Set.Subset.antisymm hDC hCD, hφinj.ncard_image,
      show {i | i < E.size} = ((Finset.range E.size : Finset Nat) : Set Nat) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  refine ⟨?_, ?_, hsize, fun y hy => ?_⟩
  · unfold conjTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, allIn_eq_true]
    refine ⟨⟨rpos, by rw [rroot]; exact tblEq_refl x⟩, fun k _ hk => ?_⟩
    obtain ⟨t1, t2, t3⟩ := rtree k (by omega) hk
    refine ⟨⟨t1, t2⟩, ?_⟩
    rw [← t3]
    exact tblEq_refl _
  · apply keysDistinct_of_nodup
    rw [List.nodup_iff_injective_get]
    intro a b e
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at e
    have ha : a.val < E.size := by simpa using a.isLt
    have hb : b.val < E.size := by simpa using b.isLt
    rw [← getElem!_pos E a.val ha, ← getElem!_pos E b.val hb] at e
    exact Fin.ext (rinj a ha b hb e)
  · obtain ⟨i, hi, rfl⟩ := hCD hy
    exact ⟨i, hi, hφ i hi⟩

end Closure

theorem forIn_const {β : Type} (l : List Nat) (b : β) (f : Nat → β → Id (ForInStep β))
    (h : ∀ i ∈ l, f i b = pure (ForInStep.yield b)) : forIn l b f = pure b := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons, h i List.mem_cons_self]
    exact ih fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem contains_foldl_insert (l : List Table) (s : Std.HashSet Nat) (x : Nat) :
    (l.foldl (fun s e => s.insert (key n e)) s).contains x = true ↔
      s.contains x = true ∨ ∃ e ∈ l, key n e = x := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem findReps_one {gens gensInv : Array Table} {X : List Table} {cap : Nat} (hX : X ≠ [])
    (hcov : ∀ i < X.length, ∃ j < (conjClosure n gens gensInv X.toArray[0]! cap).1.size,
      key n X[i]! = key n (conjClosure n gens gensInv X.toArray[0]! cap).1[j]!) :
    findReps n gens gensInv X cap = [0] := by
  unfold findReps
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  obtain ⟨m, hm⟩ : ∃ m, X.length = m + 1 := Nat.exists_eq_succ_of_ne_zero (by simpa using hX)
  rw [List.size_toArray, hm, List.range'_succ, List.forIn_cons]
  simp only [Std.HashSet.contains_empty, Bool.not_false, ite_true, Array.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, pure_bind]
  rw [forIn_const]
  · rfl
  intro i hi
  rw [List.mem_range'] at hi
  have hiX : i < X.length := by omega
  have hc : key n X.toArray[i]! ∈ (conjClosure n gens gensInv X.toArray[0]! cap).1.foldl
      (fun (s : Std.HashSet Nat) e => s.insert (key n e)) ∅ := by
    rw [Std.HashSet.mem_iff_contains, ← Array.foldl_toList, contains_foldl_insert]
    obtain ⟨j, hj, e⟩ := hcov i hiX
    refine Or.inr ⟨_, Array.mem_toList_iff.2 (Array.getElem_mem hj), ?_⟩
    rw [← getElem!_pos _ j hj, ← e]
    simp
  simp at hc
  simp [hc]

section Class

variable {gens gensInv : Array Table} {γ : Nat → Equiv.Perm (Fin n)}
  {C : Set (Equiv.Perm (Fin n))}

theorem classOK_one (hn : n < 2 ^ 32)
    (hg : ∀ l < gens.size, Rep n gens[l]! (γ l) ∧ Rep n gensInv[l]! (γ l)⁻¹)
    (hCf : C.Finite) (hCcl : ∀ l < gens.size, ∀ x ∈ C, γ l * x * (γ l)⁻¹ ∈ C)
    (hmin : ∀ g ∈ C, ∀ D : Set (Equiv.Perm (Fin n)), D.Finite → g ∈ D →
      (∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D) → C ⊆ D)
    {X : List Table} {XG : List (Equiv.Perm (Fin n))} (hXF : List.Forall₂ (Rep n) X XG)
    (hXC : ∀ x ∈ XG, x ∈ C) (hXlen : X.length = C.ncard) (hX : X ≠ []) {cap : Nat}
    (hcap : C.ncard ≤ cap) :
    classes n gens gensInv X cap = [(X.toArray[0]!, conjClosure n gens gensInv X.toArray[0]! cap)] ∧
      classOK n gens gensInv X cap = true ∧
      (conjClosure n gens gensInv X.toArray[0]! cap).1.size = C.ncard := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hXF
  have hX0 : 0 < X.length := List.length_pos_iff.2 hX
  have rep_i : ∀ i (hi : i < X.length), Rep n X[i]! (XG[i]'(by omega)) := fun i hi => by
    rw [getElem!_pos X i hi]
    exact hget i hi (by omega)
  have e0 : X.toArray[0]! = X[0]! := by
    rw [getElem!_pos X.toArray 0 (by simpa using hX0), getElem!_pos X 0 hX0,
      List.getElem_toArray]
  obtain ⟨htree, hdist, hsize, hcov⟩ := conjClosure_one hn hg hCf hCcl hmin
    (x := X.toArray[0]!) (by rw [e0]; exact rep_i 0 hX0) (hXC _ (List.getElem_mem _)) hcap
  have hreps : findReps n gens gensInv X cap = [0] := findReps_one hX fun i hi => by
    obtain ⟨j, hj, hr⟩ := hcov _ (hXC (XG[i]'(by omega)) (List.getElem_mem _))
    exact ⟨j, hj, key_eq_of_rep (rep_i i hi) hr⟩
  have hcl : classes n gens gensInv X cap =
      [(X.toArray[0]!, conjClosure n gens gensInv X.toArray[0]! cap)] := by
    unfold classes
    rw [hreps]
    rfl
  refine ⟨hcl, ?_, hsize⟩
  unfold classOK
  simp only [hcl, hreps, List.all_cons, List.all_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨hX0, htree⟩, hdist⟩, hsize.trans hXlen.symm⟩

theorem classTotal_one {X Y : List Table} {cap r s mx my : Nat}
    (hcl : classes n gens gensInv X cap =
      [(X.toArray[0]!, conjClosure n gens gensInv X.toArray[0]! cap)]) :
    classTotal n gens gensInv X Y cap r s mx my =
      (conjClosure n gens gensInv X.toArray[0]! cap).1.size *
        Y.countP (pairTest n r s mx my X.toArray[0]!) := by
  unfold classTotal
  rw [hcl]
  simp

end Class

end CFSG.KS.ClassOne

end
