module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.HardMathSupport.Curtis.UnitaryLevi (exists_sylow_three_le_of_factorization_eq)

theorem exists_kill_set_of_landing {G J : Type} [Group G] [Group J] [Finite J] (ι : J →* G)
    (hι : Function.Injective ι) (Z : Subgroup G) (hZ : Z ≤ ι.range)
    (hZ3 : (Nat.card J).factorization 3 ≤ (Nat.card Z).factorization 3)
    (hB : ∀ z ∈ Z, z ^ 3 = 1 → ∃ B : Subgroup G, B ≤ ι.range ∧
      B ≤ Subgroup.centralizer ({z} : Set G) ∧ Finite B ∧ (∀ b ∈ B, b ^ 3 = 1) ∧
      81 ≤ Nat.card B) :
    ∃ Q : Subgroup J, Nat.card Q = 3 ^ (Nat.card J).factorization 3 ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ≠ 1 →
        81 ∣ Nat.card (Subgroup.centralizer ({s} : Set J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set XJ : Subgroup J := Z.comap ι with hXJ
  have hcard : Nat.card XJ = Nat.card Z := by
    rw [← Subgroup.card_map_of_injective hι, hXJ, Subgroup.map_comap_eq, inf_of_le_right hZ]
  have hdvd : Nat.card XJ ∣ Nat.card J := Subgroup.card_dvd_of_le le_top |>.trans (by simp)
  have hfac : (Nat.card XJ).factorization 3 = (Nat.card J).factorization 3 := by
    refine le_antisymm ?_ (hcard ▸ hZ3)
    exact (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2
      (Subgroup.card_subgroup_dvd_card XJ) 3
  obtain ⟨P, hP⟩ := exists_sylow_three_le_of_factorization_eq XJ hfac
  refine ⟨P, by rw [P.card_eq_multiplicity], fun s hs hs3 hs1 => ?_⟩
  have hsZ : ι s ∈ Z := hP hs
  obtain ⟨B, hBr, hBc, hBfin, hB3, hB81⟩ := hB (ι s) hsZ (by rw [← map_pow, hs3, map_one])
  set B1 : Subgroup J := B.comap ι with hB1
  have hcardB : Nat.card B1 = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hι, hB1, Subgroup.map_comap_eq, inf_of_le_right hBr]
  have hB1C : B1 ≤ Subgroup.centralizer ({s} : Set J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hBc hx)
  have hB1p : IsPGroup 3 B1 := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hι
    have := hB3 (ι x.1) x.2
    simpa using this
  have hfin1 : Finite B1 := Finite.of_injective _ (Subgroup.inclusion_injective hB1C)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hB1p
  have hk4 : 4 ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk, hcardB] at h1
    omega
  have h81 : 81 ∣ Nat.card B1 := by
    rw [hk]
    exact (pow_dvd_pow 3 hk4 : 3 ^ 4 ∣ 3 ^ k)
  exact h81.trans (Subgroup.card_dvd_of_le hB1C)

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
