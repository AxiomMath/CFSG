module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open Polynomial

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_sq {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) : CharP K 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := 2 * n)
  rw [hK, ← pow_mul, mul_comm]

theorem pow_pow_frob_eq {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (x : K) :
    (x ^ 2 ^ n) ^ 2 ^ n = x := by
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card (K := K) x
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [← pow_mul, ← sq]
  exact h

theorem card_fixed_frob_le {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {x : K // x ^ 2 ^ n = x} ≤ 2 ^ n := by
  classical
  haveI := Fintype.ofFinite K
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  let p : K[X] := X ^ 2 ^ n - X
  have hdeg : p.natDegree = 2 ^ n := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  let Z : Finset K := Finset.univ.filter fun x : K => x ^ 2 ^ n = x
  have hZ : Z.val ⊆ p.roots := by
    intro x hx
    have hx2 : x ∈ Z := hx
    have hx' : x ^ 2 ^ n = x := (Finset.mem_filter.1 hx2).2
    rw [Polynomial.mem_roots hp0]
    simp [p, IsRoot, hx', sub_self]
  have h1 := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hdeg] at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1

theorem card_fixed_frob {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card {x : K // x ^ 2 ^ n = x} = 2 ^ n := by
  classical
  haveI : CharP K 2 := charP_two_of_card_sq hK
  have hup : Nat.card {x : K // x ^ 2 ^ n = x} ≤ 2 ^ n := card_fixed_frob_le hn
  let σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ x : K, σ x = x ^ 2 ^ n := fun x => rfl
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by rw [hσ, hσ]; exact pow_pow_frob_eq hK x
  let T : K →+ K := AddMonoidHom.id K + σ.toAddMonoidHom
  have hT : ∀ x : K, T x = x + σ x := fun x => rfl
  have hker : ∀ x : K, x ∈ T.ker ↔ σ x = x := by
    intro x
    rw [AddMonoidHom.mem_ker, hT, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
    exact eq_comm
  have hrange : ∀ y ∈ T.range, σ y = y := by
    rintro y ⟨x, rfl⟩
    rw [hT, map_add, hσσ, add_comm]
  have hcard : Nat.card T.ker * Nat.card T.range = Nat.card K := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index T.ker
  have hkerN : Nat.card T.ker = Nat.card {x : K // σ x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hker x)
  have hrangeN : Nat.card T.range ≤ Nat.card {x : K // σ x = x} := by
    let f : T.range → {x : K // σ x = x} := fun y => ⟨y.1, hrange y.1 y.2⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val h
    exact Nat.card_le_card_of_injective f hf
  have hsq : (2 ^ n) * (2 ^ n) ≤ Nat.card {x : K // σ x = x} * Nat.card {x : K // σ x = x} := by
    calc (2 ^ n) * (2 ^ n) = (2 ^ n) ^ 2 := (sq _).symm
      _ = Nat.card K := hK.symm
      _ = Nat.card T.ker * Nat.card T.range := hcard.symm
      _ ≤ Nat.card {x : K // σ x = x} * Nat.card {x : K // σ x = x} :=
        Nat.mul_le_mul (le_of_eq hkerN) hrangeN
  have hlow : 2 ^ n ≤ Nat.card {x : K // σ x = x} := Nat.mul_self_le_mul_self_iff.1 hsq
  have hfix : Nat.card {x : K // σ x = x} = Nat.card {x : K // x ^ 2 ^ n = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hσ])
  rw [hfix] at hlow
  exact le_antisymm hup hlow

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
