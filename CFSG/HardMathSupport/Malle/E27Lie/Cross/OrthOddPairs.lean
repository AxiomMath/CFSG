module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_comb_isotropic [Finite K] (B : V →ₗ[K] V →ₗ[K] K) (z : Fin 3 → V) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ B (∑ i, x i • z i) (∑ i, x i • z i) = 0 := by
  classical
  have := Fintype.ofFinite K
  let P : MvPolynomial (Fin 3) K :=
    ∑ i, ∑ j, MvPolynomial.C (B (z i) (z j)) * (MvPolynomial.X i * MvPolynomial.X j)
  have heval : ∀ x : Fin 3 → K, MvPolynomial.eval x P =
      B (∑ i, x i • z i) (∑ i, x i • z i) := by
    intro x
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdeg : P.totalDegree < Fintype.card (Fin 3) := by
    have h : P.totalDegree ≤ 2 := by
      unfold P
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      have h1 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact h1
    simp only [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions (ringChar K) hdeg
  by_contra hcon
  have hcon' : ∀ x : Fin 3 → K,
      B (∑ i, x i • z i) (∑ i, x i • z i) = 0 → x = 0 := fun x hx => by
    by_contra hne
    exact hcon ⟨x, hne, hx⟩
  have h0 : MvPolynomial.eval (0 : Fin 3 → K) P = 0 := by
    rw [heval]
    simp
  have hpos : 0 < Fintype.card {x : Fin 3 → K // MvPolynomial.eval x P = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : Fintype.card {x : Fin 3 → K // MvPolynomial.eval x P = 0} ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [heval] at hx hy
    exact Subtype.ext ((hcon' x hx).trans (hcon' y hy).symm)
  have hle := Nat.le_of_dvd hpos hdvd
  have h1 := CharP.ringChar_ne_one (R := K)
  have h2 := CharP.ringChar_ne_zero_of_finite K
  omega

theorem exists_singular_of_three_le_odd [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K V) {S : Submodule K V} (h3 : 3 ≤ finrank K S) :
    ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  let b := Module.finBasis K S
  let z : Fin 3 → S := fun i => b (Fin.castLE h3 i)
  have hli : LinearIndependent K z := by
    refine b.linearIndependent.comp _ ?_
    intro i j hij
    exact Fin.castLE_injective h3 hij
  obtain ⟨c, hc0, hc⟩ := exists_comb_isotropic (polarBilin (Q.comp S.subtype)) z
  refine ⟨((∑ i, c i • z i : S) : V), (∑ i, c i • z i : S).2, ?_, ?_⟩
  · intro h
    have h' : (∑ i, c i • z i : S) = 0 := Subtype.ext h
    exact hc0 (funext fun i => (Fintype.linearIndependent_iff.mp hli c h') i)
  · rw [polarBilin_apply_apply, polar_self_eq_two_mul] at hc
    have := (mul_eq_zero.mp hc).resolve_left h2
    simpa using this

theorem exists_two_hypPairs_odd [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hd : 5 ≤ finrank K V) :
    ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
  have hS : PolarNondegOn Q ⊤ := polarNondegOn_top hQ
  obtain ⟨e, heS, he0, he⟩ := exists_singular_of_three_le_odd h2 Q
    (S := (⊤ : Submodule K V)) (by rw [finrank_top]; omega)
  obtain ⟨f, hfS, hf, hef⟩ := exists_partner_of_polarNondegOn hS heS he he0
  let P₀ : HypPair Q := ⟨e, f, he, hf, hef⟩
  have hS' : PolarNondegOn Q ((⊤ : Submodule K V) ⊓ P₀.perp) := hS.inf_perp P₀ heS hfS
  have hn := finrank_inf_perp_add_two P₀ heS hfS
  rw [finrank_top] at hn
  obtain ⟨e', he'S, he'0, he'⟩ := exists_singular_of_three_le_odd h2 Q
    (S := (⊤ : Submodule K V) ⊓ P₀.perp) (by omega)
  obtain ⟨f', hf'S, hf', hef'⟩ := exists_partner_of_polarNondegOn hS' he'S he' he'0
  let P₁ : HypPair Q := ⟨e', f', he', hf', hef'⟩
  have h01 : P₀.Orth P₁ := HypPair.orth_of_mem_perp (Submodule.mem_inf.mp he'S).2
    (Submodule.mem_inf.mp hf'S).2
  refine ⟨![P₀, P₁], fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01
  · exact h01.symm
  · exact absurd rfl hij

end CFSG.HardMathSupport.Malle.E27Lie
