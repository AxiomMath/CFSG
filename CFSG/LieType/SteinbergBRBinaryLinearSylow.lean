module

public import CFSG.LieType.SteinbergBRLinearSmallParabolic
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder

public section

namespace CFSG.LieType.SteinbergBR.BinaryLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.SteinbergBR.BlockPar

variable {k : Type} [Field k] {n : ℕ}

theorem eq_one_of_ne_zero [Finite k] (hk : Nat.card k = 2) {x : k} (hx : x ≠ 0) : x = 1 := by
  have : Subsingleton kˣ := by
    have hcard : Nat.card kˣ = 1 := by rw [Nat.card_units, hk]
    exact (Nat.card_eq_one_iff_unique.1 hcard).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)

theorem scalars_eq_bot [Finite k] (hk : Nat.card k = 2) : scalars n k = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  have hc : (c : k) = 1 := eq_one_of_ne_zero hk c.ne_zero
  apply Subtype.ext
  change (A : Matrix (Fin n) (Fin n) k) = 1
  rw [hA, hc, map_one]

theorem upperTriangular_eq_unitriangular [Finite k] (hk : Nat.card k = 2) :
    upperTriangular n k = unitriangular n k := by
  apply le_antisymm
  · intro A hA
    refine ⟨hA, fun i => ?_⟩
    have hdet : (A : Matrix (Fin n) (Fin n) k).det = ∏ i, (A : Matrix (Fin n) (Fin n) k) i i :=
      det_of_isUpperTriangular hA
    rw [A.prop] at hdet
    have hne : (A : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
      intro h0
      rw [Finset.prod_eq_zero (f := fun j => (A : Matrix (Fin n) (Fin n) k) j j)
        (Finset.mem_univ i) h0] at hdet
      exact one_ne_zero hdet
    exact eq_one_of_ne_zero hk hne
  · intro A hA
    exact hA.1

theorem binary_linear_key [Finite k] (hn : 3 ≤ n) (hk : Nat.card k = 2) :
    (∃ P : Sylow 2 (projectiveSL n k), Subgroup.normalizer (P : Set (projectiveSL n k)) = P) ∧
      IsPGroup 2 (Outer (projectiveSL n k)) := by
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime (p := 2)
    (by rw [← Nat.card_eq_fintype_card, hk])
  have hZ := scalars_eq_bot (n := n) hk
  have hinj : Function.Injective (proj n k) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, hZ]
  have hcardU : Nat.card (projUnitriangular n k) = 2 ^ (n * (n - 1) / 2) := by
    rw [projUnitriangular, Subgroup.card_map_of_injective hinj, card_unitriangular, hk]
  have hcardP : Nat.card (projectiveSL n k) =
      2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n k)
    have h1 : Nat.card (scalars n k) = 1 := by
      rw [hZ]
      exact Subgroup.card_bot
    rw [h1, mul_one, card_SL_eq (by omega), hk] at h
    exact h.symm
  have hodd : ¬ 2 ∣ ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) :=
    two_not_dvd_prod_pow_sub_one (dvd_refl 2) (by norm_num) _ fun j hj => by
      have := (Finset.mem_Icc.1 hj).1
      omega
  have hfac : (Nat.card (projectiveSL n k)).factorization 2 = n * (n - 1) / 2 := by
    have h := ordProj_prime_pow_mul Nat.prime_two (n * (n - 1) / 2) hodd
    rw [← hcardP] at h
    exact Nat.pow_right_injective le_rfl h
  let S : Sylow 2 (projectiveSL n k) := Sylow.ofCard (projUnitriangular n k) (by
    rw [hcardU, hfac])
  refine ⟨⟨S, ?_⟩, ?_⟩
  · change Subgroup.normalizer ((projUnitriangular n k : Subgroup _) : Set _) =
      projUnitriangular n k
    rw [normalizer_projUnitriangular 2, projUpperTriangular, upperTriangular_eq_unitriangular hk]
    rfl
  · have h := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
      (K := k) (ℓ := 2) (f := 1) Nat.prime_two le_rfl hn (by rw [hk, pow_one])
    norm_num at h
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h2, pow_one])

end CFSG.LieType.SteinbergBR.BinaryLinear
