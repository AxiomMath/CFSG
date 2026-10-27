module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

structure SimpleNormalIn {G : Type*} [Group G] (c x : G) (D : Subgroup G) : Prop where
  le : D ≤ centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G)
  normal : ∀ f ∈ centralizer ({c} : Set G) ⊓ centralizer ({x} : Set G), ∀ d ∈ D, f * d * f⁻¹ ∈ D
  simple : IsSimpleGroup D
  nonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a

section Types

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem x₂_mul_self (hC : CentData z ι) : (z * ι τ₀) * (z * ι τ₀) = 1 := by
  calc (z * ι τ₀) * (z * ι τ₀) = z * (ι τ₀ * (z * ι τ₀)) := by group
    _ = z * ((ι τ₀ * z) * ι τ₀) := by group
    _ = z * ((z * ι τ₀) * ι τ₀) := by rw [← hC.comm τ₀]
    _ = (z * z) * (ι τ₀ * ι τ₀) := by group
    _ = 1 := by rw [hC.mul_self, ← map_mul, τ₀_mul_self, map_one, one_mul]

theorem x₂_ne_one (hC : CentData z ι) : z * ι τ₀ ≠ 1 := by
  intro h
  have hz : z = (ι τ₀)⁻¹ := by
    calc z = z * (ι τ₀ * (ι τ₀)⁻¹) := by group
      _ = (z * ι τ₀) * (ι τ₀)⁻¹ := by group
      _ = 1 * (ι τ₀)⁻¹ := by rw [h]
      _ = (ι τ₀)⁻¹ := by group
  rw [← map_inv] at hz
  exact hC.ne_z τ₀⁻¹ hz.symm

theorem orderOf_x₂ (hC : CentData z ι) : orderOf (z * ι τ₀) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact x₂_mul_self hC) (x₂_ne_one hC)

theorem z_mem_centralizer_x₂ (hC : CentData z ι) : z ∈ centralizer ({z * ι τ₀} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  calc z * (z * ι τ₀) = (z * z) * ι τ₀ := by rw [mul_assoc]
    _ = ι τ₀ := by rw [hC.mul_self, one_mul]
    _ = z * (ι τ₀ * z) := by rw [← hC.comm τ₀, ← mul_assoc, hC.mul_self, one_mul]
    _ = (z * ι τ₀) * z := by rw [mul_assoc]

theorem x₁_mem_centralizer_x₂ (hC : CentData z ι) : ι τ₀ ∈ centralizer ({z * ι τ₀} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  calc ι τ₀ * (z * ι τ₀) = (ι τ₀ * z) * ι τ₀ := by rw [mul_assoc]
    _ = (z * ι τ₀) * ι τ₀ := by rw [← hC.comm τ₀]

theorem card_centralizer_z (hC : CentData z ι) :
    Nat.card (centralizer ({z} : Set G)) = 7257600 := by
  have htop : centralizer ({1} : Set G) = ⊤ := by
    ext x; simp [mem_centralizer_singleton_iff]
  have h1 := hC.card_inf_centralizer (1 : Perm (Fin 10))
  simp only [map_one] at h1
  rw [htop, inf_top_eq] at h1
  rw [two_mul_card_centralizer_perm_ten (σ := (1 : Perm (Fin 10))) (by rw [mul_one]),
    cycleType_one, Multiset.card_zero] at h1
  rw [h1]
  norm_num [N10, Nat.factorial]

theorem mul_self_of_isConj {c : G} (hC : CentData z ι) (hc : IsConj z c) : c * c = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  rw [← hg]
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hC.mul_self]; group

theorem exists_perm_of_involution (hC : CentData z ι) {w : G} (hw : w ∈ centralizer ({z} : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwz : w ≠ z) :
    ∃ σ : Perm (Fin 10), σ * σ = 1 ∧ σ ≠ 1 ∧ (w = ι σ ∨ w = z * ι σ) := by
  obtain ⟨σ, hσ⟩ := hC.cases w hw
  have hσ2 : σ * σ = 1 := by
    apply hC.inj
    rw [map_mul, map_one]
    rcases hσ with h | h
    · rw [h] at hw2
      exact hw2
    · rw [h] at hw2
      have hzz : (z * ι σ) * (z * ι σ) = ι σ * ι σ := by
        calc (z * ι σ) * (z * ι σ) = z * (ι σ * (z * ι σ)) := by group
          _ = z * ((ι σ * z) * ι σ) := by group
          _ = z * ((z * ι σ) * ι σ) := by rw [← hC.comm σ]
          _ = (z * z) * (ι σ * ι σ) := by group
          _ = ι σ * ι σ := by rw [hC.mul_self, one_mul]
      rw [hzz] at hw2
      exact hw2
  refine ⟨σ, hσ2, ?_, hσ⟩
  intro hs
  rcases hσ with h | h
  · exact hw1 (by rw [h, hs, map_one])
  · exact hwz (by rw [h, hs, map_one, mul_one])

theorem pairOrder_eq_N10 (hC : CentData z ι) {σ : Perm (Fin 10)} (hσ : σ * σ = 1) :
    pairOrder z (ι σ) = N10 (Multiset.card σ.cycleType) ∧
      pairOrder z (z * ι σ) = N10 (Multiset.card σ.cycleType) := by
  constructor
  · rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ]
  · rw [pairOrder, hC.card_inf_centralizer_mul σ, two_mul_card_centralizer_perm_ten hσ]

theorem exists_type (hC : CentData z ι) (hP2 : ¬ IsConj z (z * ι τ₀)) {c : G} (hc : IsConj z c)
    (hcx : c ∈ centralizer ({z * ι τ₀} : Set G)) :
    ∃ (g : G) (σ : Perm (Fin 10)), g * z * g⁻¹ = c ∧ σ * σ = 1 ∧ σ ≠ 1 ∧
      (g⁻¹ * (z * ι τ₀) * g = ι σ ∨ g⁻¹ * (z * ι τ₀) * g = z * ι σ) ∧
      pairOrder c (z * ι τ₀) = N10 (Multiset.card σ.cycleType) ∧
      1 ≤ Multiset.card σ.cycleType ∧ Multiset.card σ.cycleType ≤ 5 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hx2sq : (z * ι τ₀) * (z * ι τ₀) = 1 := x₂_mul_self hC
  have hcomm_cx : c * (z * ι τ₀) = (z * ι τ₀) * c :=
    mem_centralizer_singleton_iff.1 hcx
  have hz_eq : z = g⁻¹ * c * g := by rw [← hg]; group
  have hwmem : g⁻¹ * (z * ι τ₀) * g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (g⁻¹ * (z * ι τ₀) * g) * z
        = (g⁻¹ * (z * ι τ₀) * g) * (g⁻¹ * c * g) := by rw [hz_eq]
      _ = g⁻¹ * ((z * ι τ₀) * c) * g := by group
      _ = g⁻¹ * (c * (z * ι τ₀)) * g := by rw [← hcomm_cx]
      _ = (g⁻¹ * c * g) * (g⁻¹ * (z * ι τ₀) * g) := by group
      _ = z * (g⁻¹ * (z * ι τ₀) * g) := by rw [← hz_eq]
  have hw2 : (g⁻¹ * (z * ι τ₀) * g) * (g⁻¹ * (z * ι τ₀) * g) = 1 := by
    calc (g⁻¹ * (z * ι τ₀) * g) * (g⁻¹ * (z * ι τ₀) * g)
        = g⁻¹ * ((z * ι τ₀) * (z * ι τ₀)) * g := by group
      _ = 1 := by rw [hx2sq]; group
  have hw1 : g⁻¹ * (z * ι τ₀) * g ≠ 1 := by
    intro h
    apply x₂_ne_one hC
    calc z * ι τ₀ = g * (g⁻¹ * (z * ι τ₀) * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hwz : g⁻¹ * (z * ι τ₀) * g ≠ z := by
    intro h
    apply hP2
    rw [isConj_iff]
    refine ⟨g, ?_⟩
    have hx2c : z * ι τ₀ = c := by
      calc z * ι τ₀ = g * (g⁻¹ * (z * ι τ₀) * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [h]
        _ = c := hg
    rw [hx2c]
    exact hg
  obtain ⟨σ, hσ2, hσ1, hσw⟩ := exists_perm_of_involution hC hwmem hw2 hw1 hwz
  have hx2gw : g * (g⁻¹ * (z * ι τ₀) * g) * g⁻¹ = z * ι τ₀ := by group
  have hpair : pairOrder c (z * ι τ₀) = N10 (Multiset.card σ.cycleType) := by
    rw [show c = g * z * g⁻¹ from hg.symm]
    rw [show z * ι τ₀ = g * (g⁻¹ * (z * ι τ₀) * g) * g⁻¹ from hx2gw.symm]
    rw [pairOrder_conj g z (g⁻¹ * (z * ι τ₀) * g)]
    rcases hσw with h | h
    · rw [h]; exact (pairOrder_eq_N10 hC hσ2).1
    · rw [h]; exact (pairOrder_eq_N10 hC hσ2).2
  refine ⟨g, σ, hg, hσ2, hσ1, hσw, hpair, ?_, ?_⟩
  · exact card_cycleType_pos.mpr hσ1
  · exact card_cycleType_le_five hσ2

end Types

end CFSG.OddStandard.AltStdSec.SwapPartner
