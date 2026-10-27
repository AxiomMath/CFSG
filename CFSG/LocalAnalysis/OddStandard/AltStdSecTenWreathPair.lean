module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

section Pair

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem exists_perm_of_conj_mem (hC : CentData z ι) {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxz : ¬ IsConj z x) (g : G) (hg : g⁻¹ * z * g ∈ centralizer ({x} : Set G)) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧ σ ≠ 1 ∧ 1 ≤ Multiset.card σ.cycleType ∧
      Multiset.card σ.cycleType ≤ 5 ∧ (g * x * g⁻¹ = ι σ ∨ g * x * g⁻¹ = z * ι σ) ∧
      pairOrder (g⁻¹ * z * g) x = N10 (Multiset.card σ.cycleType) := by
  let u : G := g * x * g⁻¹
  have hu2 : u * u = 1 := by
    dsimp [u]
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hzu : u * z = z * u := by
    have hc := mem_centralizer_singleton_iff.1 hg
    have hconj := congrArg (fun w : G => g * w * g⁻¹) hc
    have hL : g * ((g⁻¹ * z * g) * x) * g⁻¹ = z * (g * x * g⁻¹) := by group
    have hR : g * (x * (g⁻¹ * z * g)) * g⁻¹ = (g * x * g⁻¹) * z := by group
    rw [hL, hR] at hconj
    dsimp [u]
    exact hconj.symm
  have humem : u ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hzu
  obtain ⟨σ, hσ | hσ⟩ := hC.cases u humem
  · have hσ2 : σ * σ = 1 := by
      apply hC.inj
      rw [map_mul, map_one, ← hσ]
      exact hu2
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, map_one] at hσ
      apply hx1
      have hx : g * x * g⁻¹ = 1 := by simpa only [u] using hσ
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [hx]; group
    have hk1 : 1 ≤ Multiset.card σ.cycleType :=
      Nat.succ_le_of_lt (Equiv.Perm.card_cycleType_pos.2 hσ1)
    have hk5 : Multiset.card σ.cycleType ≤ 5 := card_cycleType_le_five hσ2
    have hN : pairOrder z (ι σ) = N10 (Multiset.card σ.cycleType) := by
      rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ2]
    refine ⟨σ, hσ2, hσ1, hk1, hk5, ?_, ?_⟩
    · left; simpa only [u] using hσ
    · have hconj : pairOrder (g⁻¹ * z * g) x = pairOrder z u := by
        have h := pairOrder_conj g (g⁻¹ * z * g) x
        rw [show g * (g⁻¹ * z * g) * g⁻¹ = z from by group] at h
        simpa only [u] using h.symm
      rw [hconj, hσ]
      exact hN
  · have hσ2 : σ * σ = 1 := by
      have key : (z * ι σ) * (z * ι σ) = 1 := by rw [← hσ]; exact hu2
      apply hC.inj
      rw [map_mul, map_one]
      have hexp : (z * ι σ) * (z * ι σ) = ι σ * ι σ := by
        calc (z * ι σ) * (z * ι σ) = z * (ι σ * z) * ι σ := by group
          _ = z * (z * ι σ) * ι σ := by rw [← hC.comm σ]
          _ = (z * z) * (ι σ * ι σ) := by group
          _ = (1 : G) * (ι σ * ι σ) := by rw [hC.mul_self]
          _ = ι σ * ι σ := by group
      rw [hexp] at key
      exact key
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, map_one, mul_one] at hσ
      apply hxz
      rw [isConj_iff]
      refine ⟨g⁻¹, ?_⟩
      have hux : g * x * g⁻¹ = z := by simpa only [u] using hσ
      calc g⁻¹ * z * (g⁻¹)⁻¹ = g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := by rw [← hux]
        _ = x := by group
    have hk1 : 1 ≤ Multiset.card σ.cycleType :=
      Nat.succ_le_of_lt (Equiv.Perm.card_cycleType_pos.2 hσ1)
    have hk5 : Multiset.card σ.cycleType ≤ 5 := card_cycleType_le_five hσ2
    have hN : pairOrder z (ι σ) = N10 (Multiset.card σ.cycleType) := by
      rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ2]
    refine ⟨σ, hσ2, hσ1, hk1, hk5, ?_, ?_⟩
    · right; simpa only [u] using hσ
    · have hconj : pairOrder (g⁻¹ * z * g) x = pairOrder z u := by
        have h := pairOrder_conj g (g⁻¹ * z * g) x
        rw [show g * (g⁻¹ * z * g) * g⁻¹ = z from by group] at h
        simpa only [u] using h.symm
      rw [hconj, hσ, pairOrder_mul_right (p := z) (q := ι σ) (hC.comm σ)]
      exact hN

end Pair

theorem N10_mem {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    N10 k ∈ ({161280, 11520, 2304, 1536, 7680} : Finset ℕ) := by
  interval_cases k <;> simp [N10, Nat.factorial]

theorem eq_one_of_seven_dvd_N10 {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (h : 7 ∣ N10 k) : k = 1 := by
  interval_cases k <;> simp_all [N10, Nat.factorial]

theorem eq_one_of_N10_eq_N10_one {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (h : N10 k = N10 1) :
    k = 1 := by
  interval_cases k <;> simp_all [N10, Nat.factorial]

private theorem swap_mul_tau0_eq_tau0_mul_swap_cases :
    ∀ a b : Fin 10, a ≠ b → swap a b * τ₀ = τ₀ * swap a b →
      swap a b = τ₀ ∨ (swap a b 8 = 8 ∧ swap a b 9 = 9) := by
  decide

theorem eq_τ₀_or_mem_stab2_of_isSwap {σ : Perm (Fin 10)} (hσ : σ.IsSwap)
    (hc : σ * τ₀ = τ₀ * σ) : σ = τ₀ ∨ σ ∈ stab2 8 9 := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  rcases swap_mul_tau0_eq_tau0_mul_swap_cases a b hab hc with h | h
  · exact Or.inl h
  · exact Or.inr (mem_stab2.2 h)

theorem exists_isSwap_liftS8_eq {σ : Perm (Fin 10)} (hσ : σ.IsSwap) (hs : σ ∈ stab2 8 9) :
    ∃ ρ : Perm (Fin 8), ρ.IsSwap ∧ liftS8 ρ = σ := by
  obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 hs
  refine ⟨ρ, ?_, hρ⟩
  rw [Equiv.Perm.isSwap_iff_cycleType, ← cycleType_liftS8 ρ, hρ]
  exact Equiv.Perm.isSwap_iff_cycleType.1 hσ

end CFSG.OddStandard.AltStdSec.SwapPattern
