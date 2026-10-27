module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoBits
import CFSG.LieType.Ree.Endo
import CFSG.LieType.Chevalley.RootConj
public import CFSG.LieType.Chevalley.NativeHolds

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.AGLEmbedding.E6Two CFSG.Monster.B.Classical.E6Adjoint

@[expose] def e6EqB (A B : ℕ) : Bool := A % 2 ^ 6084 == B % 2 ^ 6084

@[expose] def e6Eq (u v : List ℕ) : Bool := e6EqB (evalE u) (evalE v)

structure E6InnerData where
  zW : List (List ℕ)
  aW : List (List ℕ)
  rootW : List (List ℕ × ℕ × ℕ)
  targets : List (List ℕ)

namespace E6InnerData

variable (d : E6InnerData)

@[expose] def z (i : ℕ) : List ℕ := d.zW.getD i []

@[expose] def a (i : ℕ) : List ℕ := d.aW.getD i []

@[expose] def rootWord (k : ℕ) : List ℕ := (d.rootW.getD k ([], 0, 0)).1

@[expose] def prodWord (idxs : List ℕ) : List ℕ := (idxs.map d.rootWord).flatten

end E6InnerData

@[expose] def e6InnerCheck (d : E6InnerData) : Bool :=
  (List.range 4).all (fun i => (List.range 4).all fun j =>
    e6Eq (d.z i ++ d.z j) (d.z j ++ d.z i)) &&
  (List.range 4).all (fun i => e6Eq (d.z i ++ d.z i ++ d.z i) [] && !e6Eq (d.z i) []) &&
  (List.range 4).all (fun i => e6Eq (d.a i ++ d.z i ++ (d.a i).reverse) (d.z i).reverse) &&
  (List.range 4).all (fun i => (List.range 4).all fun j =>
    i == j || e6Eq (d.a i ++ d.z j ++ (d.a i).reverse) (d.z j)) &&
  d.rootW.all (fun r => decide (r.2.1 < r.2.2) && decide (r.2.2 < 4) &&
    e6Eq (r.1 ++ d.z r.2.1) (d.z r.2.1 ++ r.1) && e6Eq (r.1 ++ d.z r.2.2) (d.z r.2.2 ++ r.1)) &&
  (List.range 12).all (fun t => e6EqB (evalE (d.prodWord (d.targets.getD t []))) (letterE t))

section Sound

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

private theorem evalG_flatten (ls : List (List ℕ)) :
    evalG K ls.flatten = (ls.map (evalG K)).prod := by
  induction ls with
  | nil => simp [evalG_nil]
  | cons u ls ih => simp [List.flatten_cons, evalG_append, ih]

private theorem e6Eq_iff (u v : List ℕ) : e6Eq u v = true ↔ evalG K u = evalG K v := by
  unfold e6Eq e6EqB
  rw [beq_iff_eq]
  exact ((hasBitsE_evalG (K := K) u).eq_iff (hasBitsE_evalG v)).symm

private theorem eq_zero_or_eq_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem hasBitsE_xElement (i : Fin Tag.E6.rank) :
    HasBitsE (xElement i 1 : adjointGroup Tag.E6 K) (letterE i.val) := by
  have h1 : i.val < 6 := by
    have := i.2
    simpa [Tag.rank] using this
  have h2 : i.val % 12 < 6 := by omega
  have hidx : letterIdx i.val = 6 + i.val := by
    rw [letterIdx, ite_eq_left h2, Nat.mod_eq_of_lt (by omega : i.val < 12)]
  change RepE (xOp Tag.E6 K i 1) (letterE i.val)
  unfold letterE
  rw [hidx, xOp_eq, CFSG.Monster.B.E6.StdF4.rootVec_single]
  exact repE_rootOp (K := K) ⟨6 + i.val, CFSG.Monster.B.E6.StdF4.six_add_lt i⟩

private theorem hasBitsE_yElement (i : Fin Tag.E6.rank) :
    HasBitsE (yElement i 1 : adjointGroup Tag.E6 K) (letterE (i.val + 6)) := by
  have h1 : i.val < 6 := by
    have := i.2
    simpa [Tag.rank] using this
  have h2 : ¬ (i.val + 6) % 12 < 6 := by omega
  have hidx : letterIdx (i.val + 6) = 12 + 2 * i.val := by
    rw [letterIdx, ite_eq_right h2, show (i.val + 6) % 12 - 6 = i.val by omega]
  change RepE (yOp Tag.E6 K i 1) (letterE (i.val + 6))
  unfold letterE
  rw [hidx, yOp_eq, rootVec_neg_single]
  exact repE_rootOp (K := K) ⟨12 + 2 * i.val, twelve_add_lt i⟩

theorem liftableNormalizerGen_of_e6InnerCheck (hK : Nat.card K = 2) (d : E6InnerData)
    (hd : e6InnerCheck d = true) : LiftableNormalizerGen (adjointGroup Tag.E6 K) := by
  simp only [e6InnerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨hcomm, hord⟩, hinv⟩, hfix⟩, hroot⟩, htarg⟩ := hd
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin 4 → adjointGroup Tag.E6 K, ∀ i, Z i = evalG K (d.z i) :=
    ⟨fun i => evalG K (d.z i), fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin 4 → adjointGroup Tag.E6 K, ∀ i, A i = evalG K (d.a i) :=
    ⟨fun i => evalG K (d.a i), fun _ => rfl⟩
  have hZcomm : ∀ i j, Commute (Z i) (Z j) := fun i j => by
    have := (e6Eq_iff (K := K) _ _).1 (hcomm i i.2 j j.2)
    rw [evalG_append, evalG_append] at this
    rw [hZ, hZ]
    exact this
  have hZord : ∀ i, orderOf (Z i) = 3 := fun i => by
    obtain ⟨h3, h1⟩ := hord i i.2
    have h3' := (e6Eq_iff (K := K) _ _).1 h3
    rw [evalG_append, evalG_append, evalG_nil] at h3'
    rw [hZ]
    refine orderOf_eq_prime (by rw [pow_succ, sq]; exact h3') (fun h => ?_)
    have : e6Eq (d.z i) [] = true := (e6Eq_iff (K := K) _ _).2 (by rw [evalG_nil]; exact h)
    rw [this] at h1
    exact absurd h1 (by decide)
  have hAinv : ∀ i, A i * Z i * (A i)⁻¹ = (Z i)⁻¹ := fun i => by
    have := (e6Eq_iff (K := K) _ _).1 (hinv i i.2)
    rw [evalG_append, evalG_append, ← evalG_inv, ← evalG_inv] at this
    rw [hZ, hA]
    exact this
  have hAfix : ∀ i j, i ≠ j → A i * Z j * (A i)⁻¹ = Z j := fun i j hij => by
    rcases hfix i i.2 j j.2 with h | h
    · exact absurd (Fin.ext h) hij
    · have := (e6Eq_iff (K := K) _ _).1 h
      rw [evalG_append, evalG_append, ← evalG_inv] at this
      rw [hZ, hA]
      exact this
  refine liftableNormalizerGen_of_inverters Z A hZcomm hZord hAinv hAfix ?_
  set S0 : Set (adjointGroup Tag.E6 K) := pairCentralizing Z ∪
    (Subgroup.normalizer (Subgroup.closure (Set.range Z) : Set (adjointGroup Tag.E6 K)) :
      Set (adjointGroup Tag.E6 K)) with hS0
  set C := Subgroup.closure S0 with hC
  have hS0C : ∀ x, x ∈ S0 → x ∈ C := fun x hx => Subgroup.subset_closure hx
  have hgenmem : ∀ k, evalG K (d.rootWord k) ∈ C := by
    intro k
    unfold E6InnerData.rootWord
    by_cases h1 : k < d.rootW.length
    · have hmem : d.rootW.getD k ([], 0, 0) ∈ d.rootW := by
        rw [List.getD_eq_getElem _ _ h1]
        exact List.getElem_mem h1
      obtain ⟨⟨⟨hlt, hlt4⟩, hc1⟩, hc2⟩ := hroot _ hmem
      refine hS0C _ (Or.inl ⟨⟨(d.rootW.getD k ([], 0, 0)).2.1, by omega⟩,
        ⟨(d.rootW.getD k ([], 0, 0)).2.2, hlt4⟩, fun h => by
          have := congrArg Fin.val h
          simp only at this
          omega, ?_, ?_⟩)
      · have := (e6Eq_iff (K := K) _ _).1 hc1
        rw [evalG_append, evalG_append] at this
        rw [hZ]
        exact this
      · have := (e6Eq_iff (K := K) _ _).1 hc2
        rw [evalG_append, evalG_append] at this
        rw [hZ]
        exact this
    · rw [List.getD_eq_default _ _ (by omega), evalG_nil]
      exact one_mem _
  have hprod : ∀ idxs : List ℕ, evalG K (d.prodWord idxs) ∈ C := fun idxs => by
    unfold E6InnerData.prodWord
    rw [evalG_flatten]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
    exact hgenmem k
  have htargetmem : ∀ t < 12, ∀ g : adjointGroup Tag.E6 K, HasBitsE g (letterE t) → g ∈ C :=
    fun t ht g hg => by
      have h1 := htarg t ht
      unfold e6EqB at h1
      rw [beq_iff_eq] at h1
      have h2 := (hg.eq_iff (hasBitsE_evalG (K := K) (d.prodWord (d.targets.getD t [])))).2
        h1.symm
      rw [h2]
      exact hprod _
  rw [eq_top_iff, ← closure_xElement_yElement (τ := Tag.E6) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · rcases eq_zero_or_eq_one hK c with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 6 := by
        have := i.2
        simpa [Tag.rank] using this
      exact htargetmem i.val (by omega) _ (hasBitsE_xElement i)
  · rcases eq_zero_or_eq_one hK c with rfl | rfl
    · rw [show yElement (τ := Tag.E6) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 6 := by
        have := i.2
        simpa [Tag.rank] using this
      exact htargetmem (i.val + 6) (by omega) _ (hasBitsE_yElement i)

end Sound

end CFSG.AGLEmbedding
