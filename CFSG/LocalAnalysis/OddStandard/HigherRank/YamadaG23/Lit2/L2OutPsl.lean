module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedNonsquare
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphAlt
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l2out_psl_fixed {S : Type} [Group S] {p f : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) (hL : CFSG.Blueprint.LieModel S .PSL 4 p f) (α : MulAut S)
    (hα : α ^ 2 = 1) :
    ∃ Q : Subgroup S, Group.IsPerfect Q ∧ Even (Nat.card Q) ∧ ∀ s ∈ Q, α s = s := by
  classical
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  let α' : MulAut (projectiveSL 4 K) := e.symm.trans (α.trans e)
  have haa : ∀ x, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, ← sq, hα]
    rfl
  have hα' : α' ^ 2 = 1 := by
    ext s
    rw [sq, MulAut.mul_apply]
    change α' (α' s) = s
    rw [show α' s = e (α (e.symm s)) from rfl,
      show α' (e (α (e.symm s))) = e (α (e.symm (e (α (e.symm s))))) from rfl,
      MulEquiv.symm_apply_apply, haa, MulEquiv.apply_symm_apply]
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) even_two
  have : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar K ≠ 2 := by rwa [ringChar.eq K p]
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
    exact ⟨s, hs⟩
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨P, hP, heven, hfix⟩ : ∃ P : Subgroup (projectiveSL 4 K), Group.IsPerfect P ∧
      Even (Nat.card P) ∧ ∀ s ∈ P, α' s = s := by
    obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn3).2 α'
    rw [hαeq] at hα' ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · rw [pow_zero, mul_one] at hα' ⊢
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one (fieldAut 4 K), mul_one] at hα' ⊢
        exact exists_fixed_perfect_even_conjAut hK2 h4 hn3 A hα'
      · exact exists_fixed_perfect_even_conjAut_fieldAut hp hf hcard hn3 A σ hσ hα'
    · rw [pow_one] at hα' ⊢
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one (fieldAut 4 K), mul_one] at hα' ⊢
        rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut hn3 A hα' with hA | hA
        · exact exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq hK2 h4 hn3 A hA
        · exact exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq_neg hK2 h4 hn3 A hA
      · exact exists_fixed_perfect_even_conjAut_fieldAut_dualAut hp hp2 hf hcard hn3 A σ hσ hα'
  refine ⟨P.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · haveI := hP
    exact Group.IsPerfect.map e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact heven
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h1 : e.symm (α' t) = α (e.symm t) := by
      rw [show α' t = e (α (e.symm t)) from rfl, MulEquiv.symm_apply_apply]
    change α (e.symm t) = e.symm t
    rw [← h1, hfix t ht]

end CFSG.OddStandard.HigherRank.YamadaG23
