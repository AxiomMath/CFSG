module

public import CFSG.CGT.PushingUpLit.CGT6X.K7aLinear
public import CFSG.CGT.PushingUpLit.CGT6X.K7aExclude
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane

theorem linear_involution_surviving {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (t : MulAut (projectiveSL 3 K)) (ht : t ^ 2 = 1)
    (htout : t ∉ innSL 3 K) (Y : Subgroup (projectiveSL 3 K))
    (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K))
    (hYt : ∀ y ∈ Y, t y = y) :
    ∃ H : GL (Fin 3) K, t = conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹ ∧
      Y = (orthProj K).map (conjAut 3 K H : MulAut (projectiveSL 3 K)).toMonoidHom := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, hteq⟩ := hgen t
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hteq
    by_cases hσ : σ = 1
    ·
      subst hσ
      rw [map_one, mul_one] at hteq
      have hcop : Nat.Coprime 2 (Nat.gcd 3 (Nat.card K - 1)) :=
        Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num)
      exact absurd (inner_of_mem_linearAut_of_pow_eq_one (by norm_num) hcop
        (hteq ▸ conjAut_mem_linearAutGroup A) ht) htout
    · exfalso
      rw [hteq] at ht hYt
      exact no_SL2_field hf hK A σ hσ ht Y hY hYt
  · rw [pow_one] at hteq
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hteq
      rw [hteq] at ht hYt
      exact hteq ▸ linear_graph_surviving hf hK A ht Y hY hYt
    · exfalso
      rw [hteq] at ht hYt
      exact no_SL2_graphField hf hK A σ hσ ht Y hY hYt

end CFSG.CGT.PushingUpLit.CGT6X.K7a
