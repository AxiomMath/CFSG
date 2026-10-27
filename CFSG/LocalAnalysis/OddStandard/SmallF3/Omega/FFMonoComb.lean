module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def ffF (σ : Equiv.Perm (Fin 6)) : Finset (Finset (Fin 6)) :=
  Finset.univ.filter fun J =>
    Even J.card ∧ (J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ)

@[expose] def ffK0 : Finset (Equiv.Perm (Fin 6)) :=
  {1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 4 5,
    Equiv.swap 1 3 * Equiv.swap 4 5}

@[expose] def ffF0 : Finset (Finset (Fin 6)) :=
  {∅, {0, 2}, {1, 3}, {4, 5}, {0, 1, 2, 3}, {0, 2, 4, 5}, {1, 3, 4, 5}, Finset.univ}

private instance decidableMemMonoD : DecidablePred (· ∈ monoD) := fun σ =>
  decidable_of_iff'
    ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
        (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
    (by
      show (σ ∈ alternatingGroup (Fin 6) ⊓
        Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6)))) ↔
        ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
          (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_eq_prod_prod_Iio]
      simp only [Set.mem_singleton_iff, forall_eq])

private def ffC : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5

private def ffMonoDList : Finset (Equiv.Perm (Fin 6)) :=
  {1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 4 5,
    Equiv.swap 1 3 * Equiv.swap 4 5, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, ffC, ffC * ffC * ffC}

private lemma ffMonoDList_card : ffMonoDList.card = 8 := by
  decide

private lemma ffMonoDList_subset_monoD {x : Equiv.Perm (Fin 6)} (hx : x ∈ ffMonoDList) :
    x ∈ monoD := by
  simp only [ffMonoDList, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffMonoDList_mem_of_mem_monoD {x : Equiv.Perm (Fin 6)} (hx : x ∈ monoD) :
    x ∈ ffMonoDList := by
  have hsub : (↑ffMonoDList : Set (Equiv.Perm (Fin 6))) ⊆ (monoD : Set _) := by
    intro y hy
    exact ffMonoDList_subset_monoD hy
  have hmono : (monoD : Set (Equiv.Perm (Fin 6))).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact monoD_card
  have hlist : (↑ffMonoDList : Set (Equiv.Perm (Fin 6))).ncard = 8 := by
    rw [Set.ncard_coe_finset, ffMonoDList_card]
  have hcard : (monoD : Set (Equiv.Perm (Fin 6))).ncard ≤
      (↑ffMonoDList : Set (Equiv.Perm (Fin 6))).ncard := by
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
  change x ∈ (↑ffMonoDList : Set (Equiv.Perm (Fin 6)))
  rw [heq]
  exact hx

private lemma ffF_card_list {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffMonoDList)
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) : (ffF σ).card = 8 := by
  revert h2 h1
  simp only [ffMonoDList, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffF_eq_iff_list {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffMonoDList)
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) : ffF σ = ffF0 ↔ σ ∈ ffK0 := by
  revert h2 h1
  simp only [ffMonoDList, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffF_ne_of_ne_list {σ τ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffMonoDList)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hτ : τ ∈ ffMonoDList) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hne : σ ≠ τ) (hF : ffF σ = ffF τ) : σ ∈ ffK0 ∧ τ ∈ ffK0 := by
  revert hσ2 hσ1 hτ2 hτ1 hne hF
  simp only [ffMonoDList, Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem ffInvolutions_mem_monoD :
    (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)) ∈ monoD ∧
    (Equiv.swap 0 2 * Equiv.swap 4 5 : Equiv.Perm (Fin 6)) ∈ monoD ∧
    (Equiv.swap 1 3 * Equiv.swap 4 5 : Equiv.Perm (Fin 6)) ∈ monoD ∧
    (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) ∈ monoD ∧
    (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 6)) ∈ monoD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem ffF_card {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    (ffF σ).card = 8 :=
  ffF_card_list (ffMonoDList_mem_of_mem_monoD hσ) h2 h1

theorem ffF_eq_iff {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ffF σ = ffF0 ↔ σ ∈ ffK0 :=
  ffF_eq_iff_list (ffMonoDList_mem_of_mem_monoD hσ) h2 h1

theorem ffF_ne_of_ne {σ τ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hτ : τ ∈ monoD) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hne : σ ≠ τ) (hF : ffF σ = ffF τ) :
    σ ∈ ffK0 ∧ τ ∈ ffK0 :=
  ffF_ne_of_ne_list (ffMonoDList_mem_of_mem_monoD hσ) hσ2 hσ1
    (ffMonoDList_mem_of_mem_monoD hτ) hτ2 hτ1 hne hF

theorem ffExp2_card_le (R : Subgroup (Equiv.Perm (Fin 6))) (hR : R ≤ monoD)
    (h2 : ∀ r ∈ R, r * r = 1) : Nat.card R ≤ 4 := by
  have hdvd : Nat.card R ∣ 8 := by
    have h := Subgroup.card_dvd_of_le hR
    change Nat.card R ∣ Nat.card monoD at h
    rwa [monoD_card] at h
  have hRne : R ≠ monoD := by
    intro hEq
    have hc : (ffC : Equiv.Perm (Fin 6)) ∈ R := by
      rw [hEq]
      simpa [ffC] using monoD_cycle_mem
    have hcc : ffC * ffC = 1 := h2 ffC hc
    exact (by decide : ffC * ffC ≠ (1 : Equiv.Perm (Fin 6))) hcc
  by_contra hle
  push_neg at hle
  obtain ⟨k, hk, hkR⟩ := (Nat.dvd_prime_pow (p := 2) (m := 3) Nat.prime_two).mp hdvd
  have hk3 : k = 3 := by
    rw [hkR] at hle
    interval_cases k <;> norm_num at hle
    rfl
  have h8 : Nat.card R = 8 := by rw [hkR, hk3]; norm_num
  have hcard : Nat.card monoD ≤ Nat.card R := by
    have hm : Nat.card monoD = 8 := monoD_card
    omega
  exact hRne (Subgroup.eq_of_le_of_card_ge hR hcard)

end CFSG.OddStandard.SmallF3.Omega
