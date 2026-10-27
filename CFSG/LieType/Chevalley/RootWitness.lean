module

public import CFSG.LieType.Chevalley.RootRank
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank

structure RootWitness (τ : Tag) (n : ℕ) where
  word : Fin n → List (Fin τ.rank)
  simple : Fin n → Fin τ.rank

namespace RootWitness

variable
    {τ : Tag} {n : ℕ} (W : RootWitness τ n)

@[expose] def vec
    (i : Fin n) : Fin τ.rank → ℤ :=
  (W.word i).foldr (reflect τ) (Pi.single (W.simple i) 1)

@[expose] noncomputable def root
    (i : Fin n) : Root τ :=
  ⟨(coxeterSystem τ).wordProd (W.word i) • Pi.single (W.simple i) 1,
    IsRoot.smul (isRoot_single τ (W.simple i)) _⟩

theorem root_val
    (i : Fin n) : (W.root i).1 = W.vec i := wordProd_smul _ _

@[expose] def sepWord
    (i : Fin n) : List (Fin τ.rank) :=
  W.word i ++ [W.simple i] ++ (W.word i).reverse

@[expose] def check : Bool :=
  (List.finRange n).all fun i =>
    decide (0 < height (W.vec i)) &&
    (List.finRange τ.rank).all (fun k => decide (0 ≤ W.vec i k)) &&
    decide (height ((W.sepWord i).foldr (reflect τ) (W.vec i)) < 0) &&
    (List.finRange n).all fun j => decide (i = j) ||
      (pairFree τ (W.vec i) (W.vec j) &&
        decide (0 < height ((W.sepWord i).foldr (reflect τ) (W.vec j))))

variable {W}

theorem le_pRank
    (hW : W.check = true) {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ f) :
    n * f ≤ pRank p (⊤ : Subgroup (adjointGroup τ K)) := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hW
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by rw [root_val]; exact (hW i).1.1.1
  have hnn : ∀ i k, 0 ≤ (W.root i).1 k := fun i k => by rw [root_val]; exact (hW i).1.1.2 k
  have hne0 : ∀ i, (W.root i).1 ≠ 0 := fun i h => by
    have := hpos i
    rw [h] at this
    simp [height] at this
  set w : Fin n → WeylGroup τ := fun i => (coxeterSystem τ).wordProd (W.sepWord i)
  have hact : ∀ i j, (w i) • (W.root j).1 = (W.sepWord i).foldr (reflect τ) (W.vec j) :=
    fun i j => by rw [root_val, wordProd_smul]
  have hneg : ∀ i, height ((w i) • (W.root i).1) < 0 := fun i => by
    rw [hact]
    exact (hW i).1.2
  have hsep : ∀ i j, i ≠ j → 0 < height ((w i) • (W.root j).1) := fun i j hij => by
    rw [hact]
    rcases (hW i).2 j with h | h
    · exact absurd h hij
    · exact h.2
  have hfree : ∀ i j, i ≠ j → pairFree τ (W.root i).1 (W.root j).1 = true := fun i j hij => by
    rw [root_val, root_val]
    rcases (hW i).2 j with h | h
    · exact absurd h hij
    · exact h.1
  have hroot_ne : ∀ i j, i ≠ j → W.root i ≠ W.root j := fun i j hij h => by
    have h1 := hneg i
    have h2 := hsep i j hij
    rw [h] at h1
    omega
  have hcomm : Pairwise fun i j => ∀ x y : Multiplicative K,
      Commute (rootHom (W.root i) x) (rootHom (W.root j) y) := fun i j hij x y =>
    commute_rootHom_of_not_isRoot (hpos i) (hpos j) (hroot_ne i j hij)
      (fun a b ha hb => not_isRoot_of_pairFree (hnn i) (hne0 i) (hnn j) (hne0 j)
        (hfree i j hij) ha hb) x y
  have := le_pRank_of_rootPi W.root hpos hcomm w hneg hsep hK
  rwa [Fintype.card_fin] at this

end RootWitness

@[expose] def witnessF4
    : RootWitness .F4 4 where
  word := ![([] : List (Fin 4)), ([2] : List (Fin 4)), ([3, 2] : List (Fin 4)),
    ([0, 1, 2, 3, 1, 2, 1] : List (Fin 4))]
  simple := ![(1 : Fin 4), (1 : Fin 4), (1 : Fin 4), (0 : Fin 4)]

@[expose] def witnessE6
    : RootWitness .E6 4 where
  word := ![([] : List (Fin 6)), ([4, 3] : List (Fin 6)), ([5, 4, 3, 2] : List (Fin 6)),
    ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2] : List (Fin 6))]
  simple := ![(3 : Fin 6), (2 : Fin 6), (0 : Fin 6), (0 : Fin 6)]

@[expose] def witnessE7
    : RootWitness .E7 4 where
  word := ![([] : List (Fin 7)), ([] : List (Fin 7)), ([] : List (Fin 7)), ([] : List (Fin 7))]
  simple := ![(6 : Fin 7), (4 : Fin 7), (2 : Fin 7), (1 : Fin 7)]

@[expose] def witnessE8
    : RootWitness .E8 4 where
  word := ![([] : List (Fin 8)), ([] : List (Fin 8)), ([] : List (Fin 8)), ([2, 3] : List (Fin 8))]
  simple := ![(7 : Fin 8), (5 : Fin 8), (3 : Fin 8), (1 : Fin 8)]

theorem witnessF4_check
    : witnessF4.check = true := by decide +kernel

theorem witnessE6_check
    : witnessE6.check = true := by decide +kernel

theorem witnessE7_check
    : witnessE7.check = true := by decide +kernel

theorem witnessE8_check
    : witnessE8.check = true := by decide +kernel

theorem four_mul_le_pRank
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ f) :
    4 * f ≤ pRank p (⊤ : Subgroup (adjointGroup τ K)) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact RootWitness.le_pRank witnessF4_check hK
  · exact RootWitness.le_pRank witnessE6_check hK
  · exact RootWitness.le_pRank witnessE7_check hK
  · exact RootWitness.le_pRank witnessE8_check hK

end CFSG.LieType.Chevalley
