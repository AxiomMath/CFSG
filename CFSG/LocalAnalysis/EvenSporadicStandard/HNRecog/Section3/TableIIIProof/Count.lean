module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.OrbitCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem tableIII_count [Finite G] {K : Subgroup G} {S : Set G} {P : Fin 3 → Set G}
    (hK : Nat.card K = 30720) (hS : Nat.card ↥S = 118) (hsub : ∀ i, P i ⊆ S)
    (hcover : ∀ c ∈ S, ∃ i, c ∈ P i) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hinv : ∀ i, ∀ k ∈ K, ∀ c ∈ P i, k * c * k⁻¹ ∈ P i)
    (h0 : IsConjOrbitStab K (P 0) (2 ^ 8 * 3))
    (h1 : ∀ c ∈ P 1, Nat.card ↥(K ⊓ Gx c) ∣ 2 ^ 10)
    (h2 : ∀ c ∈ P 2, Nat.card ↥(K ⊓ Gx c) = 2 ^ 7 ∨ Nat.card ↥(K ⊓ Gx c) = 2 ^ 7 * 3 ∨
      Nat.card ↥(K ⊓ Gx c) = 2 ^ 7 * 5) :
    IsOrbitPartition K S P ∧ StabCard K P ![2 ^ 8 * 3, 2 ^ 10, 2 ^ 7 * 5] := by
  obtain ⟨c0, hc0⟩ := h0.1.nonempty
  have hP0 : Nat.card ↥(P 0) = 40 := by
    have h := h0.1.card_mul_card_stab hc0
    rw [h0.2 c0 hc0, hK] at h
    omega
  have hSeq : S = P 0 ∪ P 1 ∪ P 2 := by
    ext c
    refine ⟨fun hc => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hcover c hc
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hc | hc) | hc)
      · exact hsub 0 hc
      · exact hsub 1 hc
      · exact hsub 2 hc
  have hd01 : Disjoint (P 0) (P 1) := hdisj 0 1 (by decide)
  have hd012 : Disjoint (P 0 ∪ P 1) (P 2) :=
    Set.disjoint_union_left.2 ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩
  have hsum : Nat.card ↥(P 0) + Nat.card ↥(P 1) + Nat.card ↥(P 2) = 118 := by
    rw [← hS, hSeq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq, Set.ncard_union_eq hd012 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd01 (Set.toFinite _) (Set.toFinite _)]
  have h12 : Nat.card ↥(P 1) + Nat.card ↥(P 2) = 78 := by omega
  have hstab2 : ∀ c ∈ P 2, Nat.card ↥(K ⊓ Gx c) = 2 ^ 7 * 5 := by
    intro c hc
    have hle := tableIII_card_le_of_conj_mem (hinv 2) hc
    rw [hK] at hle
    rcases h2 c hc with h | h | h
    · rw [h, show (2 : ℕ) ^ 7 = 128 by norm_num] at hle
      omega
    · rw [h, show (2 : ℕ) ^ 7 * 3 = 384 by norm_num] at hle
      omega
    · exact h
  have hd2 : 48 ∣ Nat.card ↥(P 2) := by
    refine tableIII_dvd_card_of_conj_mem (hinv 2) (fun c hc => ?_)
    rw [hstab2 c hc, hK]
    norm_num
  have hd1 : 30 ∣ Nat.card ↥(P 1) := by
    refine tableIII_dvd_card_of_conj_mem (hinv 1) (fun c hc => ?_)
    rw [hK, show (30720 : ℕ) = 30 * 2 ^ 10 by norm_num]
    exact Nat.mul_dvd_mul_left 30 (h1 c hc)
  have hP1 : Nat.card ↥(P 1) = 30 := by omega
  have hP2 : Nat.card ↥(P 2) = 48 := by omega
  have hstab1 : ∀ c ∈ P 1, Nat.card ↥(K ⊓ Gx c) = 2 ^ 10 := by
    intro c hc
    have hle := tableIII_card_le_of_conj_mem (hinv 1) hc
    rw [hK, hP1] at hle
    have hle2 := Nat.le_of_dvd (by norm_num) (h1 c hc)
    norm_num at hle hle2 ⊢
    omega
  have hne : ∀ i, Nat.card ↥(P i) ≠ 0 → (P i).Nonempty := fun i hi =>
    Set.nonempty_of_ncard_ne_zero (by rwa [← Nat.card_coe_set_eq])
  obtain ⟨c1, hc1⟩ := hne 1 (by rw [hP1]; norm_num)
  obtain ⟨c2, hc2⟩ := hne 2 (by rw [hP2]; norm_num)
  have horb1 : IsConjOrbit K (P 1) := by
    refine (tableIII_isConjOrbit_of_card_le (hinv 1) hc1 ?_).1
    rw [hP1, hstab1 c1 hc1, hK]
    norm_num
  have horb2 : IsConjOrbit K (P 2) := by
    refine (tableIII_isConjOrbit_of_card_le (hinv 2) hc2 ?_).1
    rw [hP2, hstab2 c2 hc2, hK]
    norm_num
  refine ⟨⟨hsub, hcover, hdisj, fun i => ?_⟩, fun i => ?_⟩
  · fin_cases i
    · exact h0.1
    · exact horb1
    · exact horb2
  · fin_cases i
    · exact h0.2
    · exact hstab1
    · exact hstab2

end CFSG.EvenSporadicStandard.HNRecog.Section3
