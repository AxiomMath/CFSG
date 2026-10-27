module

public import CFSG.FeitThompson.Representations.NormalInducedBlockPartition
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L]

theorem conj_indClassFun [Fintype L] (H : Subgroup L) (f : H → ℂ) :
    (fun y => conj (indClassFun H f y)) = indClassFun H fun n => conj (f n) := by
  classical
  funext y
  rw [indClassFun_apply, indClassFun_apply, map_mul, map_sum]
  congr 1
  · rw [map_inv₀, Complex.conj_natCast]
  · refine Finset.sum_congr rfl fun t _ => ?_
    split <;> simp

theorem conjClassFun_conj (H : Subgroup L) [H.Normal] (t : L) (f : H → ℂ) :
    conjClassFun H t (fun n => conj (f n)) = fun n => conj (conjClassFun H t f n) := by
  funext n
  rw [conjClassFun_apply, conjClassFun_apply]

theorem conj_eq_self_of_conj_indClassFun_eq [Fintype L] (hodd : Odd (Nat.card L))
    (H : Subgroup L) [H.Normal] {lam : H → ℂ} (hlam : lam ∈ Irr H)
    (h : (fun y => conj (indClassFun H lam y)) = indClassFun H lam) :
    (fun n => conj (lam n)) = lam := by
  have : Fintype H := Fintype.ofFinite H
  rw [conj_indClassFun] at h
  obtain ⟨t, ht⟩ :=
    (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun H hlam
      (conj_mem_Irr hlam)).1 h.symm
  have h1 : conjClassFun H t lam = fun n => conj (lam n) := by
    have h2 := congrArg (fun f : H → ℂ => fun n => conj (f n)) ht
    simp only at h2
    rw [← conjClassFun_conj] at h2
    simpa using h2
  have hsq : conjClassFun H (t * t) lam = lam := by rw [conjClassFun_mul, h1, ht]
  have hmem : t ∈ inertiaGroup H lam := by
    obtain ⟨k, hk⟩ := hodd
    have hpow : t = (t * t) ^ (k + 1) := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = Nat.card L + 1 by omega, pow_succ,
        pow_card_eq_one', one_mul]
    rw [hpow]
    exact pow_mem (mem_inertiaGroup.2 hsq) _
  rw [← h1]
  exact mem_inertiaGroup.1 hmem

theorem conj_mem_indFam_nonprincipalIrr [Fintype L] (H : Subgroup L) {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    (fun y => conj (θ y)) ∈ indFam H (nonprincipalIrr H) := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  exact (conj_indClassFun H lam) ▸ indClassFun_mem_indFam H (conj_mem_nonprincipalIrr hlam)

theorem conj_image_indFam_nonprincipalIrr [Fintype L] (H : Subgroup L) :
    (fun θ : L → ℂ => fun y => conj (θ y)) '' indFam H (nonprincipalIrr H)
      = indFam H (nonprincipalIrr H) := by
  refine Set.eq_of_subset_of_subset ?_ fun θ hθ => ?_
  · rintro θ ⟨ψ, hψ, rfl⟩
    exact conj_mem_indFam_nonprincipalIrr H hψ
  · refine ⟨fun y => conj (θ y), conj_mem_indFam_nonprincipalIrr H hθ, ?_⟩
    funext y
    simp

theorem ne_conj_of_mem_indFam_nonprincipalIrr [Fintype L] (hodd : Odd (Nat.card L))
    (H : Subgroup L) [H.Normal] {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    θ ≠ fun y => conj (θ y) := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  obtain ⟨hlamIrr, hlamne⟩ := mem_nonprincipalIrr.1 hlam
  intro heq
  exact ne_conj_of_mem_Irr_of_ne_one_of_odd (odd_natCard_subgroup hodd H) hlamIrr hlamne
    (conj_eq_self_of_conj_indClassFun_eq hodd H hlamIrr heq.symm).symm

theorem conj_mem_irrConstituents [Fintype L] {θ χ : L → ℂ} (h : χ ∈ irrConstituents θ) :
    (fun y => conj (χ y)) ∈ irrConstituents (fun y => conj (θ y)) := by
  refine mem_irrConstituents.2 ⟨conj_mem_Irr (mem_irrConstituents.1 h).1, ?_⟩
  rw [cfInner_conj_conj]
  exact star_pos_iff.2 (mem_irrConstituents.1 h).2

theorem irrConstituents_conj [Fintype L] (θ : L → ℂ) :
    irrConstituents (fun y => conj (θ y))
      = (fun χ : L → ℂ => fun y => conj (χ y)) '' irrConstituents θ := by
  refine Set.eq_of_subset_of_subset (fun χ hχ => ?_) ?_
  · refine ⟨fun y => conj (χ y), ?_, by funext y; simp⟩
    have h := conj_mem_irrConstituents hχ
    rwa [show (fun y => conj (conj (θ y))) = θ by funext y; simp] at h
  · rintro χ ⟨ψ, hψ, rfl⟩
    exact conj_mem_irrConstituents hψ

theorem disjoint_irrConstituents_conj [Fintype L] (hodd : Odd (Nat.card L)) (H : Subgroup L)
    [H.Normal] {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    Disjoint (irrConstituents θ) (irrConstituents fun y => conj (θ y)) :=
  pairwiseDisjoint_irrConstituents H hθ (conj_mem_indFam_nonprincipalIrr H hθ)
    (ne_conj_of_mem_indFam_nonprincipalIrr hodd H hθ)

theorem conj_notMem_irrConstituents [Fintype L] (hodd : Odd (Nat.card L)) (H : Subgroup L)
    [H.Normal] {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) {χ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) : (fun y => conj (χ y)) ∉ irrConstituents θ := fun hcon =>
  Set.disjoint_left.1 (disjoint_irrConstituents_conj hodd H hθ) hcon
    (conj_mem_irrConstituents hχ)

theorem indFam_conjugate_pair_of_odd [Fintype L] (hodd : Odd (Nat.card L)) (H : Subgroup L)
    [H.Normal] {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H)) :
    (fun y => conj (θ y)) ∈ indFam H (nonprincipalIrr H) ∧
      θ ≠ (fun y => conj (θ y)) ∧
      irrConstituents (fun y => conj (θ y))
        = (fun χ : L → ℂ => fun y => conj (χ y)) '' irrConstituents θ ∧
      Disjoint (irrConstituents θ) (irrConstituents fun y => conj (θ y)) ∧
      ∀ χ ∈ irrConstituents θ, (fun y => conj (χ y)) ∉ irrConstituents θ :=
  ⟨conj_mem_indFam_nonprincipalIrr H hθ, ne_conj_of_mem_indFam_nonprincipalIrr hodd H hθ,
    irrConstituents_conj θ, disjoint_irrConstituents_conj hodd H hθ,
    fun _ hχ => conj_notMem_irrConstituents hodd H hθ hχ⟩

end CFSG.FeitThompson
