module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.FiniteField

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_pow_apply_eq_of_orderOf_eq_prime {F : Type} [Field F] [Finite F] {q f p : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hf : 1 ≤ f) (hK : Nat.card F = q ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ f) (σ : F ≃+* F) (hσord : orderOf σ = p) :
    ∃ j : ℕ, 3 ≤ q ^ (f / p) ∧ Odd (q ^ (f / p)) ∧
      ∀ x : F, σ x = x ^ ((q ^ (f / p)) ^ j) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := Fintype.ofFinite F
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F))
      (fun a b h => DFunLike.ext a b (congrFun h))
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  obtain ⟨τ, hτ, hτord, -, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hq hf hK
  obtain ⟨e, -, hσe⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.exists_ringEquiv_eq_frobenius_pow
      hq hf hK σ
  have hστ : σ = τ ^ e := by
    ext x
    rw [CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hτ e x]
    exact hσe x
  have hord : f / Nat.gcd f e = p := by
    rw [← hσord, hστ, orderOf_pow, hτord]
  set g := Nat.gcd f e with hg
  have hfg : f = p * g := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left f e)
    rw [hord] at h
    simpa [hg] using h.symm
  have hfgp : f = p * (f / p) := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hpf).symm
  have hgp : g = f / p := by
    have h1 : p * g = p * (f / p) := by rw [← hfg, ← hfgp]
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have hdvd : f / p ∣ e := hgp ▸ Nat.gcd_dvd_right f e
  have hej : e = (f / p) * (e / (f / p)) := by
    have h := Nat.div_mul_cancel hdvd
    rw [mul_comm] at h
    exact h.symm
  refine ⟨e / (f / p), ?_, ?_, ?_⟩
  · have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hfp : 1 ≤ f / p :=
      (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpf)
    exact le_trans hq3 (le_self_pow (by omega) (by omega))
  · exact hqodd.pow
  · intro x
    rw [hσe x]
    congr 1
    calc q ^ e = q ^ ((f / p) * (e / (f / p))) := by
          conv_lhs => rw [hej]
      _ = (q ^ (f / p)) ^ (e / (f / p)) := by rw [pow_mul]

end CFSG.FiniteField

end
