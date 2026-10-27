module

public import CFSG.LieType.Chevalley.RootWitness
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.GH74.Filter.Witness

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley

@[expose] noncomputable def adjointQuotientEquiv
    (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

structure SepWitness (τ : Tag) (n : ℕ) extends RootWitness τ n where
  sep : Fin n → List (Fin τ.rank)

namespace SepWitness

variable {τ : Tag} {n : ℕ} (W : SepWitness τ n)

@[expose] def check : Bool :=
  (List.finRange n).all fun i =>
    decide (0 < height (W.vec i)) &&
    (List.finRange τ.rank).all (fun k => decide (0 ≤ W.vec i k)) &&
    decide (height ((W.sep i).foldr (reflect τ) (W.vec i)) < 0) &&
    (List.finRange n).all fun j => decide (i = j) ||
      (pairFree τ (W.vec i) (W.vec j) &&
        decide (0 < height ((W.sep i).foldr (reflect τ) (W.vec j))))

variable {W}

theorem root_pos
    (hW : W.check = true) (i : Fin n) : 0 < height (W.root i).1 := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hW
  rw [RootWitness.root_val]
  exact (hW i).1.1.1

theorem pi_data
    (hW : W.check = true) {K : Type} [Field K] [Finite K] :
    ∃ hcomm : Pairwise fun i j => ∀ x y : Multiplicative K,
        Commute (rootHom (W.root i) x) (rootHom (W.root j) y),
      Function.Injective
        (MonoidHom.noncommPiCoprod (fun i => rootHom (K := K) (W.root i)) hcomm) := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hW
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by
    rw [RootWitness.root_val]; exact (hW i).1.1.1
  have hnn : ∀ i k, 0 ≤ (W.root i).1 k := fun i k => by
    rw [RootWitness.root_val]; exact (hW i).1.1.2 k
  have hne0 : ∀ i, (W.root i).1 ≠ 0 := fun i h => by
    have := hpos i
    rw [h] at this
    simp [height] at this
  set w : Fin n → WeylGroup τ := fun i => (coxeterSystem τ).wordProd (W.sep i)
  have hact : ∀ i j, (w i) • (W.root j).1 = (W.sep i).foldr (reflect τ) (W.vec j) :=
    fun i j => by rw [RootWitness.root_val, wordProd_smul]
  have hneg : ∀ i, height ((w i) • (W.root i).1) < 0 := fun i => by
    rw [hact]
    exact (hW i).1.2
  have hsep : ∀ i j, i ≠ j → 0 < height ((w i) • (W.root j).1) := fun i j hij => by
    rw [hact]
    rcases (hW i).2 j with h | h
    · exact absurd h hij
    · exact h.2
  have hfree : ∀ i j, i ≠ j → pairFree τ (W.root i).1 (W.root j).1 = true := fun i j hij => by
    rw [RootWitness.root_val, RootWitness.root_val]
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
  exact ⟨hcomm, injective_rootPi W.root hpos hcomm w hneg hsep⟩

theorem le_pRank
    (hW : W.check = true) {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ f) :
    n * f ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ K)) := by
  obtain ⟨hcomm, hinj⟩ := pi_data hW (K := K)
  refine le_pRank_of_injective hp.out.one_lt (fun a b => mul_comm a b) (fun a => ?_) ?_ _ hinj
    le_top
  · funext i
    change Multiplicative.ofAdd (p • Multiplicative.toAdd (a i)) = 1
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl
  · rw [Nat.card_pi, Finset.prod_const, Finset.card_univ,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK,
      ← pow_mul, mul_comm, Fintype.card_fin]

theorem not_gen4_adjointGroup
    (hW : W.check = true) (hn : 5 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] : ¬ Gen4 (adjointGroup τ K) := by
  obtain ⟨hcomm, hinj⟩ := pi_data hW (K := K)
  refine not_gen4_of_injective _ hinj (fun a b => mul_comm a b) (fun a => ?_) ?_
  · funext i
    change Multiplicative.ofAdd (2 • Multiplicative.toAdd (a i)) = 1
    rw [nsmul_eq_mul, show ((2 : ℕ) : K) = 0 from CharP.cast_eq_zero K 2, zero_mul]
    rfl
  · rw [Nat.card_pi, Finset.prod_const, Finset.card_univ,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd,
      Fintype.card_fin]
    have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card)
    calc 2 ^ 4 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ Nat.card K ^ n := Nat.pow_le_pow_left h2 n

end SepWitness

end CFSG.GH74.Filter.Lie
