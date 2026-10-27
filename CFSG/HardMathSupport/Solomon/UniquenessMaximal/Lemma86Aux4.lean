module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {A : Type*} [Group A]

structure Decomp (X : Subgroup A) (r : ℕ) (W : Fin (r + 1) → Subgroup A) : Prop where
  le : ∀ i, W i ≤ X
  comm : ∀ i j, i ≠ j → W i ≤ Subgroup.centralizer (W j : Set A)
  indep : ∀ i, W i ⊓ (⨆ j : {j // j ≠ i}, W j) = ⊥
  conj0 : ∀ i, ∃ g ∈ X, GLBConj g (W 0) = W i
  perm : ∀ g ∈ X, ∀ i, ∃ j, GLBConj g (W i) = W j

omit [Group A] in
theorem Decomp.of_mcLaughlin {V : Type} [CommGroup V] {X : Subgroup (MulAut V)} {τ : MulAut V}
    {r : ℕ} {W : Fin (r + 1) → Subgroup (MulAut V)} (h : IsMcLaughlinDecomposition X τ r W) :
    Decomp X r W :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

namespace Decomp

variable {X : Subgroup A} {r : ℕ} {W : Fin (r + 1) → Subgroup A} (hD : Decomp X r W)
include hD

theorem commute {i j : Fin (r + 1)} (hij : i ≠ j) {x y : A} (hx : x ∈ W i) (hy : y ∈ W j) :
    x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 (hD.comm i j hij hx) y hy).symm

theorem iSupIndep : iSupIndep W := by
  intro i
  rw [disjoint_iff_inf_le]
  have h := hD.indep i
  have e : (⨆ (j : Fin (r + 1)) (_ : j ≠ i), W j) ≤ ⨆ j : {j // j ≠ i}, W j :=
    iSup₂_le fun j hj => le_iSup (fun k : {k // k ≠ i} => W k) ⟨j, hj⟩
  exact (inf_le_inf_left _ e).trans h.le

theorem inf_eq_bot {i j : Fin (r + 1)} (hij : i ≠ j) : W i ⊓ W j = ⊥ := by
  rw [eq_bot_iff]
  refine (inf_le_inf_left _ (le_iSup (fun k : {k // k ≠ i} => W k) ⟨j, hij.symm⟩)).trans
    (hD.indep i).le

theorem mem_normalizer_of_le {C : Subgroup A} (hCW : C ≤ W 0) (hC : C ≠ ⊥) {b : A} (hb : b ∈ X)
    (hbC : b ∈ Subgroup.normalizer (C : Set A)) : b ∈ Subgroup.normalizer (W 0 : Set A) := by
  obtain ⟨j, hj⟩ := hD.perm b hb 0
  by_cases hj0 : j = 0
  · subst hj0
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← mem_gLBConj (g := b), hj]
  · exfalso
    apply hC
    rw [eq_bot_iff]
    intro c hc
    have h1 : c ∈ W j := by
      rw [← hj, mem_gLBConj]
      exact hCW ((Subgroup.mem_normalizer_iff.1 hbC c).1 hc)
    have h2 : c ∈ W 0 ⊓ W j := ⟨hCW hc, h1⟩
    rwa [hD.inf_eq_bot (Ne.symm hj0)] at h2

theorem not_dvd_card_iSup [Finite A] {p : ℕ} (hp : p.Prime) (h : ∀ i, ¬ p ∣ Nat.card (W i)) :
    ¬ p ∣ Nat.card (⨆ i, W i : Subgroup A) := by
  have hcomm : Pairwise fun i j : Fin (r + 1) => ∀ x y : A, x ∈ W i → y ∈ W j → Commute x y :=
    fun i j hij x y hx hy => hD.commute hij hx hy
  let ψ := Subgroup.noncommPiCoprod (H := W) hcomm
  have hrange : ψ.range = ⨆ i, W i := Subgroup.noncommPiCoprod_range
  have hdvd : Nat.card ψ.range ∣ Nat.card (∀ i, W i) :=
    Subgroup.card_range_dvd ψ
  rw [Nat.card_pi] at hdvd
  intro hp'
  rw [← hrange] at hp'
  have := hp'.trans hdvd
  rw [Prime.dvd_finsetProd_iff hp.prime] at this
  obtain ⟨i, -, hi⟩ := this
  exact h i hi

end Decomp

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
