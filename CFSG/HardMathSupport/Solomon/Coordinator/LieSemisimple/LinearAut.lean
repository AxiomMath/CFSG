module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.RankThree.SteinbergR3ECAFieldFixedLayerQuotient
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.FieldFixedLayer
  (linear_unitary_odd_prime_field_fixed_group_solvable_layer_quotient)
open CFSG.RankThree.LinearDescent (higher_linear_prime_semilinear_field_descent)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

private theorem exists_card_eq_pow :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

theorem perfectInLayer_fieldAut (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) : PerfectInLayer (fieldAut n K σ) := by
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow (K := K)
  exact perfectInLayer_of_isSolvable_layer_quotient _
    ((linear_unitary_odd_prime_field_fixed_group_solvable_layer_quotient
      hp hp2 hn).1 (ringChar K) f K hℓ hf hK σ hσ)

theorem perfectInLayer_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (β : MulAut (projectiveSL n K)) (hβ : β ^ p = 1) : PerfectInLayer β := by
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow (K := K)
  have hpℓ : p ≠ ringChar K := fun h => hpK (by rw [h, ringChar.Nat.cast_ringChar])
  have hdesc := higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  by_cases hlin : β ∈ linearAutGroup n K
  ·
    have hrange : linearAutGroup n K = (conjAut n K).range := by
      rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ p ∈ (conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact perfectInLayer_conjAut hpK hc.symm
  ·
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : conjAut n K A * fieldAut n K σ ∈ semilinearAutGroup n K :=
      mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
        (fieldAut_mem_semilinearAutGroup σ)
    have hne : conjAut n K A * fieldAut n K σ ≠ 1 := fun h => hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (conjAut n K A * fieldAut n K σ) = p := orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      hdesc.2.2.2.2.2.2.2 p hp hpℓ _ hmem hlin hord
    rw [hβτ]
    exact perfectInLayer_conj h _ (perfectInLayer_fieldAut hn hp hp2 τ hτ)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
