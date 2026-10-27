module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.PairTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem swap_ζ_of_normalizer_Tgrp [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) {g₀ : G}
    (hn : g₀ ∈ normalizer ((Tgrp z ι Q : Subgroup G) : Set G)) (hz : g₀ * z * g₀⁻¹ = ι τ₀) :
    g₀ * ι τ₀ * g₀⁻¹ = z ∧ g₀ * ι ρ₄ * g₀⁻¹ = ι ρ₄ := by
  have hg₀F : g₀ ∈ normalizer ((Fgrp (Tgrp z ι Q) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_Fgrp (Tgrp z ι Q) hn
  rw [Subgroup.mem_set_normalizer_iff] at hg₀F
  have hx₁F : ι τ₀ ∈ Fgrp (Tgrp z ι Q) := (mem_Fgrp_iff hC hQ).mpr ⟨0, 1, 0, by simp⟩
  have hρ₄F : ι ρ₄ ∈ Fgrp (Tgrp z ι Q) := (mem_Fgrp_iff hC hQ).mpr ⟨0, 0, 1, by simp⟩
  have hpair_zρ : pairOrder z (ι ρ₄) = N10 4 := by
    have h := pairOrder_z_Fgrp hC (0 : Fin 2) (0 : Fin 2)
    simpa using h
  have hpair_xρ : pairOrder (ι τ₀) (ι ρ₄) = N10 4 := by
    have h := pairOrder_x₁_Fgrp (G := G) hC hx (0 : Fin 2) (0 : Fin 2)
    simpa using h
  have hρ₄_notE : ι ρ₄ ∉ Egrp z ι := by
    intro he
    rw [mem_Egrp_iff hC] at he
    obtain ⟨a, b, heab⟩ := he
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at heab
    · exact (by decide : ρ₄ ≠ 1) (hC.inj (by rw [heab, map_one]))
    · exact (by decide : ρ₄ ≠ τ₀) (hC.inj heab)
    · exact hC.ne_z ρ₄ heab
    · have hzι : z = ι (ρ₄ * τ₀⁻¹) := by
        rw [map_mul, map_inv, heab]; group
      exact hC.ne_z (ρ₄ * τ₀⁻¹) hzι.symm
  have hwF : g₀ * ι τ₀ * g₀⁻¹ ∈ Fgrp (Tgrp z ι Q) := (hg₀F (ι τ₀)).mp hx₁F
  obtain ⟨i, j, k, hwk⟩ := (mem_Fgrp_iff hC hQ).mp hwF
  have hpair : pairOrder (ι τ₀) (g₀ * ι τ₀ * g₀⁻¹) = N10 1 := by
    have hconj := pairOrder_conj g₀ z (ι τ₀)
    rw [hz] at hconj
    exact hconj.trans (pairOrder_E hC).1
  have hk0 : k = 0 := by
    by_contra hk
    have hk1 : k = 1 := by
      fin_cases k
      · exact absurd rfl hk
      · rfl
    have h1 : pairOrder (ι τ₀) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * (ι ρ₄) ^ (k : ℕ)) = N10 1 := by
      rw [← hwk]; exact hpair
    have h2 : pairOrder (ι τ₀) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) = N10 1 := by
      simpa [hk1] using h1
    have h3 : (if i = 0 then N10 4 else N10 5) = N10 1 := by
      rw [← pairOrder_x₁_Fgrp (G := G) hC hx i j]; exact h2
    by_cases hi : i = 0
    · rw [if_pos hi] at h3
      exact N10_one_ne_four h3.symm
    · rw [if_neg hi] at h3
      exact N10_one_ne_five h3.symm
  have hne1 : g₀ * ι τ₀ * g₀⁻¹ ≠ 1 := by
    intro h
    have h1 : ι τ₀ = 1 := by
      calc ι τ₀ = g₀⁻¹ * (g₀ * ι τ₀ * g₀⁻¹) * g₀ := by group
        _ = 1 := by rw [h]; group
    have hτ : τ₀ = 1 := hC.inj (by rw [h1, map_one])
    have h8 : (9 : Fin 10) = 8 := by
      have hh : τ₀ 8 = (1 : Perm (Fin 10)) 8 := congrArg (fun σ : Perm (Fin 10) => σ 8) hτ
      rw [τ₀_apply_eight] at hh
      simpa using hh
    exact absurd h8 (by decide)
  have hne_x₁ : g₀ * ι τ₀ * g₀⁻¹ ≠ ι τ₀ := by
    intro h
    have heq : g₀ * z * g₀⁻¹ = g₀ * ι τ₀ * g₀⁻¹ := by rw [hz, h]
    have hz_eq : z = ι τ₀ := by
      have hc := congrArg (fun x => g₀⁻¹ * x * g₀) heq
      group at hc
      exact hc
    exact hC.ne_z τ₀ hz_eq.symm
  have hne_x₂ : g₀ * ι τ₀ * g₀⁻¹ ≠ z * ι τ₀ := by
    intro h
    have hconj : IsConj z (z * ι τ₀) := by
      rw [← h]
      exact hx.trans (isConj_iff.mpr ⟨g₀, rfl⟩)
    exact hP2 hconj
  have hwx : g₀ * ι τ₀ * g₀⁻¹ = z := by
    have h0 : g₀ * ι τ₀ * g₀⁻¹ = z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) := by
      simpa [hk0] using hwk
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at h0
    · exact absurd h0 hne1
    · exact absurd h0 hne_x₁
    · exact h0
    · exact absurd h0 hne_x₂
  have hζF : g₀ * ι ρ₄ * g₀⁻¹ ∈ Fgrp (Tgrp z ι Q) := (hg₀F (ι ρ₄)).mp hρ₄F
  obtain ⟨i', j', k', hζk⟩ := (mem_Fgrp_iff hC hQ).mp hζF
  have hk'1 : k' = 1 := by
    by_contra hk
    have hk0 : k' = 0 := by
      fin_cases k'
      · rfl
      · exact absurd rfl hk
    have hz'' : g₀⁻¹ * (ι τ₀) * g₀ = z := by
      calc g₀⁻¹ * (ι τ₀) * g₀ = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by rw [hz]
        _ = z := by group
    have hx'' : g₀⁻¹ * z * g₀ = ι τ₀ := by
      calc g₀⁻¹ * z * g₀ = g₀⁻¹ * (g₀ * ι τ₀ * g₀⁻¹) * g₀ := by rw [hwx]
        _ = ι τ₀ := by group
    have hφz : (MulAut.conj g₀).symm z = ι τ₀ := by
      rw [MulAut.conj_symm_apply]; exact hx''
    have hφx : (MulAut.conj g₀).symm (ι τ₀) = z := by
      rw [MulAut.conj_symm_apply]; exact hz''
    have hconjE : g₀⁻¹ * (z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ)) * g₀ ∈ Egrp z ι := by
      rw [mem_Egrp_iff hC]
      refine ⟨j', i', ?_⟩
      have ha : g₀⁻¹ * (z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ)) * g₀ =
          (MulAut.conj g₀).symm (z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ)) := by
        rw [MulAut.conj_symm_apply]
      rw [ha, map_mul, map_pow, map_pow, hφz, hφx]
      exact ((show Commute z (ι τ₀) from hC.comm τ₀).symm.pow_pow (i' : ℕ) (j' : ℕ)).eq
    have hmem : ι ρ₄ ∈ Egrp z ι := by
      have hEq : ι ρ₄ = g₀⁻¹ * (g₀ * ι ρ₄ * g₀⁻¹) * g₀ := by group
      rw [hEq]
      rw [show g₀ * ι ρ₄ * g₀⁻¹ = z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ) from by
        simpa [hk0] using hζk]
      exact hconjE
    exact hρ₄_notE hmem
  have hζ' : g₀ * ι ρ₄ * g₀⁻¹ = z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ) * ι ρ₄ := by
    simpa [hk'1] using hζk
  have hpair_z' : pairOrder z (g₀ * ι ρ₄ * g₀⁻¹) = N10 4 := by
    have hconj := pairOrder_conj g₀ (ι τ₀) (ι ρ₄)
    rw [hwx] at hconj
    exact hconj.trans hpair_xρ
  have hpair_x' : pairOrder (ι τ₀) (g₀ * ι ρ₄ * g₀⁻¹) = N10 4 := by
    have hconj := pairOrder_conj g₀ z (ι ρ₄)
    rw [hz] at hconj
    exact hconj.trans hpair_zρ
  have hj' : j' = 0 := by
    have h4 : (if j' = 0 then N10 4 else N10 5) = N10 4 := by
      rw [← pairOrder_z_Fgrp hC i' j', ← hζ']
      exact hpair_z'
    by_cases hj : j' = 0
    · exact hj
    · rw [if_neg hj] at h4
      exact absurd h4.symm N10_four_ne_five
  have hi' : i' = 0 := by
    have h4 : (if i' = 0 then N10 4 else N10 5) = N10 4 := by
      rw [← pairOrder_x₁_Fgrp (G := G) hC hx i' j', ← hζ']
      exact hpair_x'
    by_cases hi : i' = 0
    · exact hi
    · rw [if_neg hi] at h4
      exact absurd h4.symm N10_four_ne_five
  refine ⟨hwx, ?_⟩
  calc g₀ * ι ρ₄ * g₀⁻¹ = z ^ (i' : ℕ) * (ι τ₀) ^ (j' : ℕ) * ι ρ₄ := hζ'
    _ = ι ρ₄ := by rw [hi', hj']; simp

end CFSG.OddStandard.AltStdSec.SwapPartner
