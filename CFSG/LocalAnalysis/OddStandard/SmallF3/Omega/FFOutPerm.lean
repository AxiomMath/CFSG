module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem ffOut_symmDiff_card_mod {α : Type} [DecidableEq α] (A B : Finset α) :
    (symmDiff A B).card % 2 = (A.card + B.card) % 2 := by
  have h1 : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.sup_eq_union]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have h2 := Finset.card_sdiff_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h3
  omega

theorem ffOut_even_symmDiff_iff {α : Type} [DecidableEq α] (A B : Finset α) :
    Even (symmDiff A B).card ↔ (Even A.card ↔ Even B.card) := by
  have h := ffOut_symmDiff_card_mod A B
  simp only [Nat.even_iff]
  omega

private instance ffOutPermDecMem : DecidablePred (· ∈ monoD) := fun σ =>
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

private def ffOutPermC : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5

private def ffOutPermList : Finset (Equiv.Perm (Fin 6)) :=
  {1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 4 5,
    Equiv.swap 1 3 * Equiv.swap 4 5, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, ffOutPermC, ffOutPermC * ffOutPermC * ffOutPermC}

private theorem ffOutPerm_mem_iff : ∀ σ : Equiv.Perm (Fin 6), σ ∈ monoD ↔ σ ∈ ffOutPermList := by
  unfold ffOutPermList ffOutPermC
  decide +kernel

@[expose] def ffBeta : Equiv.Perm (Fin 6) := Equiv.swap 0 2

@[expose] def ffRhoPerm : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5

@[expose] def ffRhoSet : Finset (Fin 6) := {2, 3, 5}

theorem ff_beta_sign : Equiv.Perm.sign ffBeta = -1 := by
  unfold ffBeta
  exact Equiv.Perm.sign_swap (by decide)

theorem ff_beta_not_mem : ffBeta ∉ monoD := by
  intro h
  have h1 : ffBeta ∈ alternatingGroup (Fin 6) := (Subgroup.mem_inf.mp h).1
  rw [Equiv.Perm.mem_alternatingGroup, ff_beta_sign] at h1
  exact absurd h1 (by decide)

theorem ff_beta_conj_mem {σ : Equiv.Perm (Fin 6)} (h : σ ∈ monoD) :
    ffBeta * σ * ffBeta⁻¹ ∈ monoD := by
  have key : ∀ σ : Equiv.Perm (Fin 6), σ ∈ monoD → ffBeta * σ * ffBeta⁻¹ ∈ monoD := by
    unfold ffBeta
    decide +kernel
  exact key σ h

theorem ff_normalizer_cases {σ : Equiv.Perm (Fin 6)} (h : ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD) :
    σ ∈ monoD ∨ ffBeta * σ ∈ monoD := by
  have key : ∀ σ : Equiv.Perm (Fin 6), (∀ τ ∈ ffOutPermList, σ * τ * σ⁻¹ ∈ ffOutPermList) →
      σ ∈ ffOutPermList ∨ ffBeta * σ ∈ ffOutPermList := by
    unfold ffOutPermList ffOutPermC ffBeta
    decide +kernel
  rw [ffOutPerm_mem_iff, ffOutPerm_mem_iff]
  refine key σ (fun τ hτ => ?_)
  rw [← ffOutPerm_mem_iff] at hτ ⊢
  exact h τ hτ

theorem ff_normalizer_even {σ : Equiv.Perm (Fin 6)} (h : ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD)
    (hs : Equiv.Perm.sign σ = 1) : σ ∈ monoD := by
  rcases ff_normalizer_cases h with h1 | h1
  · exact h1
  · exfalso
    have h2 : ffBeta * σ ∈ alternatingGroup (Fin 6) := (Subgroup.mem_inf.mp h1).1
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, ff_beta_sign, hs] at h2
    exact absurd h2 (by decide)

theorem ff_beta_coset {σ τ : Equiv.Perm (Fin 6)} (hσ : ffBeta * σ ∈ monoD)
    (hτ : ffBeta * τ ∈ monoD) : σ⁻¹ * τ ∈ monoD := by
  have h : σ⁻¹ * τ = (ffBeta * σ)⁻¹ * (ffBeta * τ) := by group
  rw [h]
  exact monoD.mul_mem (monoD.inv_mem hσ) hτ

theorem ff_rho_coset : ffBeta * ffRhoPerm ∈ monoD := by
  unfold ffBeta ffRhoPerm
  decide +kernel

theorem ff_rho_perm_sq : ffRhoPerm * ffRhoPerm = 1 := by
  unfold ffRhoPerm
  decide +kernel

theorem ff_rho_card : ¬ Even ffRhoSet.card := by
  unfold ffRhoSet
  decide

theorem ff_rho_symmDiff :
    symmDiff (ffRhoSet.map ffRhoPerm⁻¹.toEmbedding) ffRhoSet = Finset.univ := by
  unfold ffRhoSet ffRhoPerm
  decide +kernel

@[expose] def ffConjPerm (J : Finset (Fin 6)) : Equiv.Perm (Fin 6) :=
  (if (0 ∈ J ↔ 2 ∈ J) then 1 else Equiv.swap 0 2) *
    (if (1 ∈ J ↔ 3 ∈ J) then 1 else Equiv.swap 1 3) *
      (if (4 ∈ J ↔ 5 ∈ J) then 1 else Equiv.swap 4 5)

@[expose] def ffConjSign (J : Finset (Fin 6)) : Finset (Fin 6) :=
  (if 0 ∈ J then {0, 2} else ∅) ∪ (if 1 ∈ J then {1, 3} else ∅) ∪ (if 4 ∈ J then {4, 5} else ∅)

theorem ff_conjPerm_mem {J : Finset (Fin 6)} (hJ : Even J.card) : ffConjPerm J ∈ monoD := by
  have key : ∀ J : Finset (Fin 6), Even J.card → ffConjPerm J ∈ monoD := by
    unfold ffConjPerm
    decide +kernel
  exact key J hJ

theorem ff_conjSign_even (J : Finset (Fin 6)) : Even (ffConjSign J).card := by
  have key : ∀ J : Finset (Fin 6), Even (ffConjSign J).card := by
    unfold ffConjSign
    decide +kernel
  exact key J

end CFSG.OddStandard.SmallF3.Omega
