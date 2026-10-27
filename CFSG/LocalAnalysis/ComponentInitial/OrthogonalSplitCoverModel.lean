module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.LieType.Universal.Spin
open CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type*} [Field K]

theorem eq_one_of_mem_orthogonalGroup_scalars [CharP K 2] (hr : 1 ≤ r)
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (hs : g ∈ scalars K (Fin r ⊕ Fin r → K)) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hs
  set v : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨0, by omega⟩) 1 +
    Pi.single (Sum.inr ⟨0, by omega⟩) 1 with hv
  have hQv : quadPlus r K v = 1 := by
    rw [hv, quadPlus_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin r)]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  have h := map_of_mem hg v
  rw [hc, map_smul_eq_sq, hQv, mul_one] at h
  have hc1 : c = 1 := by
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    have h2 : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2'
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)
  refine LinearEquiv.ext fun x => ?_
  rw [hc, hc1, one_smul]
  rfl

theorem commutator_orthogonalGroup_quadPlus [CharP K 2] (hr : 3 ≤ r) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)⁆ =
        orthElementaryGroup (quadPlus r K) := by
  have hr0 : 0 < r := by omega
  have htail : tailSpace (plusFamily K hr0) r = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_tailSpace_plusFamily (K := K) hr0 hx
  exact orthogonal_char_two_derived_elementary (nondegenerate_polarBilin_quadPlus r K)
    (plusFamily_orth (K := K) hr0) hr
    (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily (K := K) hr0 hx)
    (Or.inl (by rw [htail, finrank_bot]))

noncomputable def statedProjOmegaPlusEquiv {K : Type} [Field K] [CharP K 2] (hr : 3 ≤ r) :
    StatedProj (StatedOmega (StatedQuadPlus r K)) ≃* orthElementaryGroup (quadPlus r K) :=
  (statedProjEquiv (coe_quadPlus r K) (commutator_orthogonalGroup_quadPlus hr)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (eq_one_of_mem_orthogonalGroup_scalars (by omega)
        (elementaryGroup_le_orthogonalGroup _ x.2) hx))).trans QuotientGroup.quotientBot)

theorem exists_mulEquiv_elementaryGroup_of_lieModel {J : Type} [Group J] {n f : ℕ}
    (h : CFSG.Blueprint.LieModel J .POmegaPlus n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧ 4 ≤ n ∧
      Nonempty (J ≃* orthElementaryGroup (quadPlus n K)) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, hK, hfin, hcard, ⟨e⟩⟩ := hc
    have hn' : 4 ≤ n := hn
    have hf : 1 ≤ f := by
      by_contra hf0
      have : f = 0 := by omega
      subst this
      have := Finite.one_lt_card (α := K)
      rw [hcard, pow_zero] at this
      exact lt_irrefl _ this
    have : CharP K 2 := by
      let _ := Fintype.ofFinite K
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
    exact ⟨K, hK, hfin, this, hcard, hn', ⟨e.trans (statedProjOmegaPlusEquiv (by omega))⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
