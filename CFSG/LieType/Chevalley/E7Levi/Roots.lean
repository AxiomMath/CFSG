module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
import CFSG.RankThree.Chevalley.SteinbergBID4Kernel
import CFSG.Mathlib.Decide.Nodup

public noncomputable section

namespace CFSG.LieType.Chevalley.E7Levi

open CFSG.Blueprint.Chevalley

@[expose] def e7PosRoot : Fin 63 → Fin Tag.E7.rank → ℤ :=
  (![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 1],
   ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 1, 1],
   ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 0],
   ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0],
   ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1, 1],
   ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0],
   ![0, 1, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 0, 0, 0],
   ![0, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 1],
   ![0, 1, 1, 2, 1, 0, 0], ![0, 1, 1, 2, 1, 1, 0], ![0, 1, 1, 2, 1, 1, 1],
   ![0, 1, 1, 2, 2, 1, 0], ![0, 1, 1, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 1],
   ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
   ![1, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 1],
   ![1, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 0],
   ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 1, 2, 1, 1, 0],
   ![1, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1, 1],
   ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 1, 0],
   ![1, 1, 2, 2, 1, 1, 1], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 1],
   ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 1],
   ![1, 1, 2, 3, 2, 2, 1], ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 1, 0],
   ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
   ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]] : Fin 63 → Fin 7 → ℤ)

theorem e7PosRoot_injective : Function.Injective e7PosRoot :=
  List.nodup_ofFn.1 <| CFSG.Decide.nodup_of_bitsetNodup
    (fun v : Fin Tag.E7.rank → ℤ =>
      CFSG.Decide.digitsKey 5 (fun i => if h : i < Tag.E7.rank then (v ⟨i, h⟩).toNat else 0) 7)
    (by decide +kernel)

theorem e7PosRoot_check : ∀ k : Fin 63, List.ofFn (e7PosRoot k) ∈ Tag.E7.artifactRoots ∧
    0 < height (e7PosRoot k) := by
  have hmem : ∀ k : Fin 63, List.ofFn (e7PosRoot k) ∈ Tag.E7.artifactRoots := by
    intro k
    fin_cases k <;> decide +kernel
  have hsum : ∀ k : Fin 63, 0 < (List.ofFn (e7PosRoot k)).sum := by
    decide +kernel
  intro k
  exact ⟨hmem k, by rw [CFSG.RankThree.Chevalley.height_eq_sum_ofFn]; exact hsum k⟩

theorem e7PosRoot_complete : ∀ l ∈ Tag.E7.artifactRoots, 0 < l.sum →
    ∃ k : Fin 63, List.ofFn (e7PosRoot k) = l := by
  decide +kernel

theorem isRoot_e7PosRoot (k : Fin 63) :
    IsRoot Tag.E7 (e7PosRoot k) :=
  isRoot_iff_mem_artifactRoots.2 (e7PosRoot_check k).1

theorem range_e7PosRoot :
    Set.range e7PosRoot = parabolicPosRoots Tag.E7 Set.univ := by
  ext α
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨isRoot_e7PosRoot k, fun i hi => absurd (Set.mem_univ i) hi⟩,
      isRoot_e7PosRoot k, (e7PosRoot_check k).2⟩
  · rintro ⟨-, hα, hpos⟩
    obtain ⟨k, hk⟩ := e7PosRoot_complete _ (isRoot_iff_mem_artifactRoots.1 hα)
      (by rw [← CFSG.RankThree.Chevalley.height_eq_sum_ofFn]; exact hpos)
    exact ⟨k, List.ofFn_injective hk⟩

theorem pow_two_eq_one_of_mul_eq_two_smul_one {n : ℕ} {G : Type*} [CommGroup G]
    (C A : Matrix (Fin n) (Fin n) ℤ) (hCA : C * A = (2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))
    (a : Fin n → G) (h : ∀ i, ∏ j, a j ^ C j i = 1) (k : Fin n) : a k ^ 2 = 1 := by
  have hdiag : ∀ j, ∑ i, C j i * A i k = if j = k then (2 : ℤ) else 0 := by
    intro j
    have hjk := congrFun (congrFun hCA j) k
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using hjk
  have hprod : (∏ j, a j ^ (∑ i, C j i * A i k)) = a k ^ (2 : ℤ) := by
    rw [Fintype.prod_eq_single k]
    · rw [hdiag k]
      simp
    · intro j hj
      rw [hdiag j, if_neg hj, zpow_zero]
  have hmain : a k ^ (2 : ℤ) = 1 := by
    rw [← hprod]
    calc ∏ j, a j ^ (∑ i, C j i * A i k)
        = ∏ j, ∏ i, (a j ^ C j i) ^ A i k := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Finset.prod_zpow_eq_zpow_sum]
          exact Finset.prod_congr rfl fun i _ => zpow_mul (a j) (C j i) (A i k)
      _ = ∏ i, ∏ j, (a j ^ C j i) ^ A i k := Finset.prod_comm
      _ = ∏ i, (∏ j, a j ^ C j i) ^ A i k := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [h]
  simpa using hmain

private def e7CartanInv : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  (!![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4; 8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4; 2, 3, 4, 6, 5, 4, 3] : Matrix (Fin 7) (Fin 7) ℤ)

private theorem e7Cartan_mul_e7CartanInv :
    Tag.E7.cartan * e7CartanInv = (2 : ℤ) •
      (1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) := by
  decide +kernel

theorem eq_one_of_prod_zpow_cartan_E7 {K : Type*} [Field K] [CharP K 2]
    (a : Fin Tag.E7.rank → Kˣ)
    (h : ∀ i, ∏ j, a j ^ Tag.E7.cartan j i = 1) : a = 1 := by
  have hneg : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (1 : K) + 1 = 2 := by ring
      _ = 0 := h2
  funext k
  have hk : a k ^ 2 = 1 :=
    pow_two_eq_one_of_mul_eq_two_smul_one Tag.E7.cartan e7CartanInv e7Cartan_mul_e7CartanInv a h k
  have hkK : (a k : K) ^ 2 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hk
    simpa using this
  have hmul : (a k : K) * (a k : K) = 1 := by simpa [pow_two] using hkK
  rcases mul_self_eq_one_iff.1 hmul with h1 | h1
  · exact Units.ext h1
  · exact Units.ext (h1.trans hneg)

end CFSG.LieType.Chevalley.E7Levi
