module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_conj_mem_pCoreOf {G : Type} [Group G] {H : Subgroup G} {l m : G} (hl : l ∈ H)
    (hm : m ∈ CFSG.Open.pCoreOf 2 H) : l * m * l⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hm
  have hn : (CFSG.pCore 2 ↥H).Normal := inferInstance
  exact Subgroup.mem_map.mpr ⟨⟨l, hl⟩ * m' * ⟨l, hl⟩⁻¹, hn.conj_mem m' hm' ⟨l, hl⟩, rfl⟩

theorem y4a_card_add {G : Type} [Group G] [Finite G] {M : Subgroup G} {A B : Set G}
    (hM : Nat.card ↥M = 16) (hA : A ⊆ M) (hB : B ⊆ M) (h1A : (1 : G) ∉ A) (h1B : (1 : G) ∉ B)
    (hAB : Disjoint A B) (hcover : ∀ m ∈ M, m ≠ 1 → m ∈ A ∨ m ∈ B) :
    Nat.card ↥A + Nat.card ↥B = 15 := by
  have hset : (M : Set G) = insert 1 (A ∪ B) := by
    ext m
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_union]
    constructor
    · intro hm
      by_cases h1 : m = 1
      · exact Or.inl h1
      · exact Or.inr (hcover m hm h1)
    · rintro (rfl | hmA | hmB)
      · exact M.one_mem
      · exact hA hmA
      · exact hB hmB
  have h1 : (1 : G) ∉ A ∪ B := fun h => h.elim h1A h1B
  have hcard : Nat.card ↥(M : Set G) = 16 := hM
  rw [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1, Set.ncard_union_eq hAB] at hcard
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  omega

private theorem y4aOrbitCount_isConjOrbit {G : Type} [Group G] (K : Subgroup G) (c : G) :
    IsConjOrbit K {d | ∃ k ∈ K, k * c * k⁻¹ = d} := by
  refine ⟨?_, ⟨c, 1, K.one_mem, by group⟩, ?_⟩
  · rintro k hk d ⟨x, hx, rfl⟩
    exact ⟨k * x, K.mul_mem hk hx, by group⟩
  · rintro d ⟨x, hx, rfl⟩ d' ⟨x', hx', rfl⟩
    exact ⟨x' * x⁻¹, K.mul_mem hx' (K.inv_mem hx), by group⟩

theorem y4a_card_stab_transfer {G : Type} [Group G] [Finite G] {Y Y' M : Subgroup G}
    (hY' : Y' ≤ Y) (hconj : ∀ x ∈ Y, ∃ l ∈ Y', ∀ m ∈ M, x * m * x⁻¹ = l * m * l⁻¹) {c : G}
    (hc : c ∈ M) :
    Nat.card ↥(Y' ⊓ Gx c) * Nat.card ↥Y = Nat.card ↥(Y ⊓ Gx c) * Nat.card ↥Y' := by
  have hcO : c ∈ {d | ∃ x ∈ Y, x * c * x⁻¹ = d} := ⟨1, Y.one_mem, by group⟩
  have hO := y4aOrbitCount_isConjOrbit Y c
  have hO' : IsConjOrbit Y' {d | ∃ x ∈ Y, x * c * x⁻¹ = d} := by
    refine ⟨?_, ⟨c, hcO⟩, ?_⟩
    · rintro k hk d ⟨x, hx, rfl⟩
      exact ⟨k * x, Y.mul_mem (hY' hk) hx, by group⟩
    · rintro d ⟨x, hx, rfl⟩ d' ⟨x', hx', rfl⟩
      obtain ⟨l, hl, hlx⟩ := hconj x hx
      obtain ⟨l', hl', hlx'⟩ := hconj x' hx'
      refine ⟨l' * l⁻¹, Y'.mul_mem hl' (Y'.inv_mem hl), ?_⟩
      rw [hlx c hc, hlx' c hc]
      group
  have h1 := hO.card_mul_card_stab hcO
  have h2 := hO'.card_mul_card_stab hcO
  rw [← h1, ← h2]
  ring

theorem y4a_isConjOrbit_of_card {G : Type} [Group G] [Finite G] {K : Subgroup G} {S : Set G}
    (hinv : ∀ k ∈ K, ∀ c ∈ S, k * c * k⁻¹ ∈ S) (hne : S.Nonempty)
    (hstab : ∀ c ∈ S, Nat.card ↥K = 10 * Nat.card ↥(K ⊓ Gx c)) (hS : Nat.card ↥S ≤ 15) :
    IsConjOrbit K S ∧ Nat.card ↥S = 10 := by
  have horb : ∀ c ∈ S, Nat.card ↥{d | ∃ k ∈ K, k * c * k⁻¹ = d} = 10 ∧
      {d | ∃ k ∈ K, k * c * k⁻¹ = d} ⊆ S := by
    intro c hc
    have hcO : c ∈ {d | ∃ k ∈ K, k * c * k⁻¹ = d} := ⟨1, K.one_mem, by group⟩
    refine ⟨?_, ?_⟩
    · have h := (y4aOrbitCount_isConjOrbit K c).card_mul_card_stab hcO
      rw [hstab c hc] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    · rintro d ⟨k, hk, rfl⟩
      exact hinv k hk c hc
  obtain ⟨c, hc⟩ := hne
  obtain ⟨hOcard, hOS⟩ := horb c hc
  have hSeq : S = {d | ∃ k ∈ K, k * c * k⁻¹ = d} := by
    refine Set.Subset.antisymm (fun d hd => ?_) hOS
    by_contra hdO
    obtain ⟨hOdcard, hOdS⟩ := horb d hd
    have hdisj : Disjoint {e | ∃ k ∈ K, k * c * k⁻¹ = e} {e | ∃ k ∈ K, k * d * k⁻¹ = e} := by
      rw [Set.disjoint_left]
      rintro e ⟨k, hk, rfl⟩ ⟨k', hk', hk'e⟩
      refine hdO ⟨k'⁻¹ * k, K.mul_mem (K.inv_mem hk') hk, ?_⟩
      calc k'⁻¹ * k * c * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * c * k⁻¹) * k' := by group
        _ = k'⁻¹ * (k' * d * k'⁻¹) * k' := by rw [hk'e]
        _ = d := by group
    have hunion := Set.ncard_union_eq hdisj
    have hle := Set.ncard_le_ncard (Set.union_subset hOS hOdS)
    rw [Nat.card_coe_set_eq] at hS hOcard hOdcard
    omega
  rw [hSeq]
  exact ⟨y4aOrbitCount_isConjOrbit K c, hOcard⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
