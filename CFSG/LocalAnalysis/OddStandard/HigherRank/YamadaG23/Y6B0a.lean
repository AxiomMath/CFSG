module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Cfg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6D8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

theorem y6_C0_comm (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : ∀ a ∈ A, ∀ c ∈ C0, a * c = c * a := by
  intro a ha c hc
  have hle : C0 ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [h.hC0, Subgroup.closure_le]
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h.u_cent a ha
    · exact h.t_cent a ha
  exact (Subgroup.mem_centralizer_iff.mp (hle hc)) a (Set.mem_singleton a)

theorem y6_z_mem_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z ∈ V := by
  rw [h.hV, ← h.u_sq]
  exact Subgroup.npow_mem_zpowers u 2

theorem y6_z_mem_A (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z ∈ A := by
  have ha1 : a₁ ∈ A := by
    rw [h.hA]
    exact Subgroup.subset_closure (by simp)
  rw [← h.rel.a1_sq]
  exact Subgroup.pow_mem A ha1 2

theorem y6_V_le_C0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : V ≤ C0 := by
  rw [h.hV, h.hC0]
  exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

theorem y6_t_mem_C0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t ∈ C0 := by
  rw [h.hC0]
  exact Subgroup.subset_closure (by simp)

theorem y6_card_C0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : Nat.card ↥C0 = 8 := by
  rw [h.hC0]
  exact y6_d8_card h.u_ord h.t_ord h.t_inv

theorem y6_card_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : Nat.card ↥V = 4 := by
  rw [h.hV, Nat.card_zpowers, h.u_ord]

theorem y6_A_inf_C0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : A ⊓ C0 = zpowers z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxA, hxC⟩ := hx
    have hxmem : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
      rwa [h.hA] at hxA
    have hcomm : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), x * b = b * x := by
      intro b hb
      have hbA : b ∈ A := by rwa [h.hA]
      exact (y6_C0_comm h b hbA x hxC).symm
    rcases y6q8_cen h.rel h.z_ne (h.hA ▸ h.card_A) x hxmem hcomm with h1 | hz
    · rw [h1]; exact Subgroup.one_mem _
    · rw [hz]; exact Subgroup.mem_zpowers z
  · exact Subgroup.zpowers_le.mpr ⟨y6_z_mem_A h, y6_V_le_C0 h (y6_z_mem_V h)⟩

theorem y6_A_inf_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : A ⊓ V = zpowers z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ A ⊓ C0 := ⟨hx.1, y6_V_le_C0 h hx.2⟩
    rwa [y6_A_inf_C0 h] at hx'
  · exact Subgroup.zpowers_le.mpr ⟨y6_z_mem_A h, y6_z_mem_V h⟩

theorem y6_card_C1 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : Nat.card ↥(A ⊔ C0) = 128 := by
  have hprod :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := A) (B := C0) (y6_C0_comm h)
  have hinf : Nat.card ↥(A ⊓ C0) = 2 := by
    rw [y6_A_inf_C0 h, Nat.card_zpowers, orderOf_eq_prime h.rel.z_sq h.z_ne]
  rw [hinf, h.card_A, y6_card_C0 h] at hprod
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
