module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import Certificates.Data.F4TwoSeitz
import CFSG.LieType.Ree.EndoRoots

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

@[expose] def f4EqB (A B : ℕ) : Bool := A % 2 ^ 2704 == B % 2 ^ 2704

@[expose] def f4Eq (u v : List ℕ) : Bool := f4EqB (codeBits u) (codeBits v)

structure F4InnerData where
  zW : List (List ℕ)
  aW : List (List ℕ)
  rootW : List (List ℕ × ℕ × ℕ)
  gW : List ℕ
  gConj : List (List ℕ)
  gConjInv : List (List ℕ)
  targets : List (List ℕ)

namespace F4InnerData

variable (d : F4InnerData)

@[expose] def z (i : ℕ) : List ℕ := d.zW.getD i []

@[expose] def a (i : ℕ) : List ℕ := d.aW.getD i []

@[expose] def eWord (e : List ℕ) : List ℕ :=
  ((List.range 4).map fun i => (List.replicate (e.getD i 0) (d.z i)).flatten).flatten

@[expose] def genWord (k : ℕ) : List ℕ :=
  if k < d.rootW.length then (d.rootW.getD k ([], 0, 0)).1
  else if k = d.rootW.length then d.gW else d.gW.reverse

@[expose] def prodWord (idxs : List ℕ) : List ℕ := (idxs.map d.genWord).flatten

end F4InnerData

@[expose] def f4InnerCheck (d : F4InnerData) : Bool :=
  (List.range 4).all (fun i => (List.range 4).all fun j =>
    f4Eq (d.z i ++ d.z j) (d.z j ++ d.z i)) &&
  (List.range 4).all (fun i => f4Eq (d.z i ++ d.z i ++ d.z i) [] && !f4Eq (d.z i) []) &&
  (List.range 4).all (fun i => f4Eq (d.a i ++ d.z i ++ (d.a i).reverse) (d.z i).reverse) &&
  (List.range 4).all (fun i => (List.range 4).all fun j =>
    i == j || f4Eq (d.a i ++ d.z j ++ (d.a i).reverse) (d.z j)) &&
  d.rootW.all (fun r => decide (r.2.1 < r.2.2) && decide (r.2.2 < 4) &&
    f4Eq (r.1 ++ d.z r.2.1) (d.z r.2.1 ++ r.1) && f4Eq (r.1 ++ d.z r.2.2) (d.z r.2.2 ++ r.1)) &&
  (List.range 4).all (fun i =>
    f4Eq (d.gW ++ d.z i ++ d.gW.reverse) (d.eWord (d.gConj.getD i [])) &&
    f4Eq (d.gW.reverse ++ d.z i ++ d.gW) (d.eWord (d.gConjInv.getD i []))) &&
  (List.range 8).all (fun t => f4Eq (d.prodWord (d.targets.getD t [])) (targetWord t))

section Sound

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

private noncomputable def elt (K : Type) [Field K] (w : List ℕ) : adjointGroup ReeTag.F4.tag K :=
  evalG K (wordOfCodes w)

private theorem elt_append (u v : List ℕ) : elt K (u ++ v) = elt K u * elt K v := by
  simp [elt, wordOfCodes, evalG_append]

private theorem elt_nil : elt K [] = 1 := by
  simp [elt, wordOfCodes]

private theorem elt_reverse (u : List ℕ) : (elt K u)⁻¹ = elt K u.reverse := by
  simp only [elt, wordOfCodes, evalG_inv, List.map_reverse]

private theorem elt_flatten (ls : List (List ℕ)) : elt K ls.flatten = (ls.map (elt K)).prod := by
  induction ls with
  | nil => simp [elt_nil]
  | cons u ls ih => simp [List.flatten_cons, elt_append, ih]

private theorem elt_replicate (n : ℕ) (u : List ℕ) :
    elt K (List.replicate n u).flatten = elt K u ^ n := by
  induction n with
  | zero => simp [elt_nil]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, elt_append, ih, pow_succ']

private theorem f4Eq_iff (u v : List ℕ) : f4Eq u v = true ↔ elt K u = elt K v := by
  unfold f4Eq f4EqB elt
  rw [beq_iff_eq, evalG_eq_evalG_iff]
  rfl

private theorem eq_zero_or_eq_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem xElement_one_mul_self (i : Fin ReeTag.F4.tag.rank) :
    xElement (τ := ReeTag.F4.tag) (K := K) i 1 * xElement i 1 = 1 := by
  rw [← xElement_add, CharTwo.add_self_eq_zero, xElement_zero]

private theorem yElement_one_eq (i : Fin ReeTag.F4.tag.rank) :
    yElement (τ := ReeTag.F4.tag) (K := K) i 1 =
      xElement i 1 * weylElement ReeTag.F4.tag K i * xElement i 1 := by
  have hn : weylElement ReeTag.F4.tag K i =
      xElement (τ := ReeTag.F4.tag) (K := K) i 1 * yElement i 1 * xElement i 1 := by
    have h := ReeTag.weylElementOf_eq (t := ReeTag.F4) (K := K) i 1
    simp only [inv_one, Units.val_one, CharTwo.neg_eq] at h
    exact h
  rw [hn]
  have hx := xElement_one_mul_self (K := K) i
  calc yElement (τ := ReeTag.F4.tag) (K := K) i 1
      = (xElement i 1 * xElement i 1) * yElement i 1 * (xElement i 1 * xElement i 1) := by
        rw [hx]; simp
    _ = xElement i 1 * (xElement i 1 * yElement i 1 * xElement i 1) * xElement i 1 := by group

private theorem elt_targetWord_x (i : Fin 4) :
    elt K (targetWord i.val) = xElement (idx i) 1 := by
  have h1 : i.val < 4 := i.2
  simp [elt, targetWord, wordOfCodes, letterOfCode, h1, Letter.elt]

private theorem elt_targetWord_y (i : Fin 4) :
    elt K (targetWord (i.val + 4)) =
      xElement (idx i) 1 * weylElement ReeTag.F4.tag K (idx i) * xElement (idx i) 1 := by
  have h1 : i.val < 4 := i.2
  have h2 : ¬ (i.val + 4 < 4) := by omega
  have hF : (⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = i := Fin.ext (Nat.mod_eq_of_lt h1)
  simp [elt, targetWord, wordOfCodes, letterOfCode, h1, h2, Letter.elt, mul_assoc, hF]

theorem liftableNormalizerGen_of_f4InnerCheck (hK : Nat.card K = 2) (d : F4InnerData)
    (hd : f4InnerCheck d = true) : LiftableNormalizerGen (adjointGroup ReeTag.F4.tag K) := by
  simp only [f4InnerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨hcomm, hord⟩, hinv⟩, hfix⟩, hroot⟩, hconj⟩, htarg⟩ := hd
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin 4 → adjointGroup ReeTag.F4.tag K, ∀ i, Z i = elt K (d.z i) :=
    ⟨fun i => elt K (d.z i), fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin 4 → adjointGroup ReeTag.F4.tag K, ∀ i, A i = elt K (d.a i) :=
    ⟨fun i => elt K (d.a i), fun _ => rfl⟩
  have hZcomm : ∀ i j, Commute (Z i) (Z j) := fun i j => by
    have := (f4Eq_iff (K := K) _ _).1 (hcomm i i.2 j j.2)
    rw [elt_append, elt_append] at this
    rw [hZ, hZ]
    exact this
  have hZord : ∀ i, orderOf (Z i) = 3 := fun i => by
    obtain ⟨h3, h1⟩ := hord i i.2
    have h3' := (f4Eq_iff (K := K) _ _).1 h3
    rw [elt_append, elt_append, elt_nil] at h3'
    rw [hZ]
    refine orderOf_eq_prime (by rw [pow_succ, sq]; exact h3') (fun h => ?_)
    have : f4Eq (d.z i) [] = true := (f4Eq_iff (K := K) _ _).2 (by rw [elt_nil]; exact h)
    rw [this] at h1
    exact absurd h1 (by decide)
  have hAinv : ∀ i, A i * Z i * (A i)⁻¹ = (Z i)⁻¹ := fun i => by
    have := (f4Eq_iff (K := K) _ _).1 (hinv i i.2)
    rw [elt_append, elt_append, ← elt_reverse, ← elt_reverse] at this
    rw [hZ, hA]
    exact this
  have hAfix : ∀ i j, i ≠ j → A i * Z j * (A i)⁻¹ = Z j := fun i j hij => by
    rcases hfix i i.2 j j.2 with h | h
    · exact absurd (Fin.ext h) hij
    · have := (f4Eq_iff (K := K) _ _).1 h
      rw [elt_append, elt_append, ← elt_reverse] at this
      rw [hZ, hA]
      exact this
  refine liftableNormalizerGen_of_inverters Z A hZcomm hZord hAinv hAfix ?_
  set S0 : Set (adjointGroup ReeTag.F4.tag K) := pairCentralizing Z ∪
    (Subgroup.normalizer (Subgroup.closure (Set.range Z) : Set (adjointGroup ReeTag.F4.tag K)) :
      Set (adjointGroup ReeTag.F4.tag K)) with hS0
  set C := Subgroup.closure S0 with hC
  have hS0C : ∀ x, x ∈ S0 → x ∈ C := fun x hx => Subgroup.subset_closure hx
  have hEword : ∀ e : List ℕ, elt K (d.eWord e) ∈ Subgroup.closure (Set.range Z) := by
    intro e
    unfold F4InnerData.eWord
    rw [elt_flatten]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    rw [List.mem_range] at hi
    rw [elt_replicate]
    have h : elt K (d.z i) = Z ⟨i, hi⟩ := (hZ ⟨i, hi⟩).symm
    rw [h]
    have hz : Z ⟨i, hi⟩ ∈ Set.range Z := ⟨⟨i, hi⟩, rfl⟩
    exact pow_mem (Subgroup.subset_closure hz) _
  have hgW : elt K d.gW ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range Z) : Set (adjointGroup ReeTag.F4.tag K)) := by
    refine mem_normalizer_closure_of_conj_mem_inv (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨i, rfl⟩ := ht
      have := (f4Eq_iff (K := K) _ _).1 (hconj i i.2).1
      rw [elt_append, elt_append, ← elt_reverse] at this
      rw [hZ, this]
      exact hEword _
    · obtain ⟨i, rfl⟩ := ht
      have := (f4Eq_iff (K := K) _ _).1 (hconj i i.2).2
      rw [elt_append, elt_append, ← elt_reverse] at this
      rw [hZ, this]
      exact hEword _
  have hgenmem : ∀ k, elt K (d.genWord k) ∈ C := by
    intro k
    unfold F4InnerData.genWord
    split_ifs with h1 h2
    · have hmem : d.rootW.getD k ([], 0, 0) ∈ d.rootW := by
        rw [List.getD_eq_getElem _ _ h1]
        exact List.getElem_mem h1
      obtain ⟨⟨⟨hlt, hlt4⟩, hc1⟩, hc2⟩ := hroot _ hmem
      refine hS0C _ (Or.inl ⟨⟨(d.rootW.getD k ([], 0, 0)).2.1, by omega⟩,
        ⟨(d.rootW.getD k ([], 0, 0)).2.2, hlt4⟩, fun h => by
          have := congrArg Fin.val h
          simp only at this
          omega, ?_, ?_⟩)
      · have := (f4Eq_iff (K := K) _ _).1 hc1
        rw [elt_append, elt_append] at this
        rw [hZ]
        exact this
      · have := (f4Eq_iff (K := K) _ _).1 hc2
        rw [elt_append, elt_append] at this
        rw [hZ]
        exact this
    · exact hS0C _ (Or.inr hgW)
    · rw [← elt_reverse]
      exact hS0C _ (Or.inr (inv_mem hgW))
  have hprod : ∀ idxs : List ℕ, elt K (d.prodWord idxs) ∈ C := fun idxs => by
    unfold F4InnerData.prodWord
    rw [elt_flatten]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
    exact hgenmem k
  have htargetmem : ∀ t < 8, elt K (targetWord t) ∈ C := fun t ht => by
    rw [← (f4Eq_iff (K := K) _ _).1 (htarg t ht)]
    exact hprod _
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · rcases eq_zero_or_eq_one hK c with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htargetmem i.val (by omega)
      rwa [show targetWord i.val = targetWord (⟨i.val, hi⟩ : Fin 4).val from rfl,
        elt_targetWord_x (K := K) ⟨i.val, hi⟩] at this
  · rcases eq_zero_or_eq_one hK c with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htargetmem (i.val + 4) (by omega)
      rw [show targetWord (i.val + 4) = targetWord ((⟨i.val, hi⟩ : Fin 4).val + 4) from rfl,
        elt_targetWord_y (K := K) ⟨i.val, hi⟩] at this
      rw [yElement_one_eq]
      exact this

end Sound

end CFSG.AGLEmbedding
