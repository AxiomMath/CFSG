module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem ff_perm_eq_one_of_pairs (σ : Equiv.Perm (Fin 6))
    (h : ∀ J : Finset (Fin 6), J.card = 2 → J.map σ.toEmbedding = J) : σ = 1 := by
  apply Equiv.ext
  intro i
  by_contra hne
  have hcard : ({i, σ i} : Finset (Fin 6)).card <
      (Finset.univ : Finset (Fin 6)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_insert_le i ({σ i} : Finset (Fin 6))
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  obtain ⟨hji, hjs⟩ := hj
  have hJ2 : ({i, j} : Finset (Fin 6)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr (Ne.symm hji)
  have hJ : ({i, j} : Finset (Fin 6)).map σ.toEmbedding = {i, j} := h {i, j} hJ2
  have hmem : σ i ∈ ({i, j} : Finset (Fin 6)).map σ.toEmbedding := by
    rw [Finset.mem_map]
    exact ⟨i, by simp, rfl⟩
  rw [hJ] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h' | h'
  · exact hne h'
  · exact hjs h'.symm

theorem ff_perm_eq_one_of_even (σ : Equiv.Perm (Fin 6))
    (h : ∀ J : Finset (Fin 6), Even J.card →
      J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ) : σ = 1 := by
  apply ff_perm_eq_one_of_pairs
  intro J hJ
  rcases h J (by rw [hJ]; exact ⟨1, rfl⟩) with h' | h'
  · exact h'
  · exfalso
    have hcard : (J.map σ.toEmbedding).card = 2 := by rw [Finset.card_map, hJ]
    have hcompl : (Jᶜ : Finset (Fin 6)).card = 4 := by
      simp [Finset.card_compl, hJ]
    rw [h', hcompl] at hcard
    omega

theorem ff_alt_trans_pairs {J J' : Finset (Fin 6)} (hJ : J.card = 2) (hJ' : J'.card = 2) :
    ∃ σ ∈ alternatingGroup (Fin 6), J.map σ.toEmbedding = J' := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq J J' (by rw [hJ, hJ'])
  by_cases hsign : Equiv.Perm.sign τ = 1
  · exact ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hsign, hτ⟩
  · have hτneg : Equiv.Perm.sign τ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
      · exact absurd h hsign
      · exact h
    have hcompl : (Jᶜ : Finset (Fin 6)).card = 4 := by
      simp [Finset.card_compl, hJ]
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < (Jᶜ).card)
    have hcJ : c ∉ J := Finset.mem_compl.mp hc
    have hdJ : d ∉ J := Finset.mem_compl.mp hd
    have hfix : ∀ x ∈ J, Equiv.swap c d x = x := fun x hx =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hcJ (h ▸ hx)) (fun h => hdJ (h ▸ hx))
    refine ⟨τ * Equiv.swap c d, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hcd, hτneg]
      decide
    · refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        change (τ * Equiv.swap c d) y ∈ J'
        rw [Equiv.Perm.mul_apply, hfix y hy]
        rw [← hτ]
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · simp [Finset.card_map, hJ, hJ']

private lemma ff_map_compl (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    Jᶜ.map σ.toEmbedding = (J.map σ.toEmbedding)ᶜ := by
  ext a
  rw [Finset.mem_compl]
  constructor
  · intro ha
    rw [Finset.mem_map] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [Finset.mem_compl] at hb
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨c, hc, hca⟩ := hmem
    have hbc : b = c := σ.toEmbedding.injective (by rw [hba, hca])
    exact hb (hbc.symm ▸ hc)
  · intro ha
    rw [Finset.mem_map] at ha
    rw [Finset.mem_map]
    refine ⟨σ.symm a, ?_, Equiv.apply_symm_apply σ a⟩
    rw [Finset.mem_compl]
    intro hmem
    exact ha ⟨σ.symm a, hmem, Equiv.apply_symm_apply σ a⟩

private lemma ff_card_two_or_four {J : Finset (Fin 6)} (hJ : Even J.card) (h0 : J ≠ ∅)
    (h1 : J ≠ Finset.univ) : J.card = 2 ∨ J.card = 4 := by
  have hle : J.card ≤ 6 := by
    have := Finset.card_le_univ J
    simpa [Fintype.card_fin] using this
  rcases hJ with ⟨k, hk⟩
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · exfalso
    exact h0 (Finset.card_eq_zero.mp (by omega))
  · left; omega
  · right; omega
  · exfalso
    exact h1 (Finset.eq_univ_of_card J (by rw [hk, Fintype.card_fin]))

theorem ff_alt_trans_even {J J' : Finset (Fin 6)} (hJ : Even J.card) (hJ' : Even J'.card)
    (h0 : J ≠ ∅) (h1 : J ≠ Finset.univ) (h0' : J' ≠ ∅) (h1' : J' ≠ Finset.univ) :
    ∃ σ ∈ alternatingGroup (Fin 6), J.map σ.toEmbedding = J' ∨ J.map σ.toEmbedding = J'ᶜ := by
  have hJc : J.card = 2 ∨ J.card = 4 := ff_card_two_or_four hJ h0 h1
  have hJ'c : J'.card = 2 ∨ J'.card = 4 := ff_card_two_or_four hJ' h0' h1'
  obtain ⟨K, hK2, hJK⟩ : ∃ K : Finset (Fin 6), K.card = 2 ∧ (J = K ∨ J = Kᶜ) := by
    rcases hJc with h | h
    · exact ⟨J, h, Or.inl rfl⟩
    · exact ⟨Jᶜ, by simp [Finset.card_compl, h], Or.inr (compl_compl J).symm⟩
  obtain ⟨K', hK'2, hJ'K'⟩ : ∃ K' : Finset (Fin 6), K'.card = 2 ∧
      (J' = K' ∨ J' = K'ᶜ) := by
    rcases hJ'c with h | h
    · exact ⟨J', h, Or.inl rfl⟩
    · exact ⟨J'ᶜ, by simp [Finset.card_compl, h], Or.inr (compl_compl J').symm⟩
  obtain ⟨σ, hσ, hmap⟩ := ff_alt_trans_pairs hK2 hK'2
  refine ⟨σ, hσ, ?_⟩
  rcases hJK with rfl | hJK
  · rcases hJ'K' with rfl | hJ'K'
    · exact Or.inl hmap
    · right
      rw [hmap, hJ'K', compl_compl]
  · rcases hJ'K' with rfl | hJ'K'
    · right
      rw [hJK, ff_map_compl, hmap]
    · left
      rw [hJK, ff_map_compl, hmap, hJ'K']

end CFSG.OddStandard.SmallF3.Omega
