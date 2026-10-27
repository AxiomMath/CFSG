module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YDihedral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem Ctx6.gomi6data (c : Ctx6 G L) (hLF : LFactsA c.s) (h61 : c.Fact61) (h4 : c.Four) :
    Gomi6Data c.s.fr.A (V1 c.e) (C0 c.e) (C1 c.e) c.s.t (c.d * c.s.t) := by
  have hAf : Nat.card ↥c.s.fr.A = 32 ∧ (∀ a ∈ c.s.fr.A, ∀ b ∈ c.s.fr.A, ⁅a, b⁆ ∈ c.s.fr.Z) ∧
      (∀ a ∈ c.s.fr.A, a ^ 2 ∈ c.s.fr.Z) ∧ (∃ a ∈ c.s.fr.A, ∃ b ∈ c.s.fr.A, a * b ≠ b * a) ∧
      c.s.fr.z ∈ c.s.fr.A ∧ orderOf c.s.fr.z = 2 ∧ cen c.s.fr.A = c.s.fr.Z :=
    ⟨hLF.card_A, hLF.comm_A, hLF.sq_A, hLF.nonab_A, hLF.z_mem, hLF.z_order, hLF.cen_A⟩
  have hz : orderOf c.s.fr.z = 2 := hAf.2.2.2.2.2.1
  obtain ⟨hu4, hu2⟩ := Ctx5pre.u_facts c.toCtx5.toCtx5pre hz
  refine {
    t_order := c.s.t_order
    u_order := hu4
    V_eq := c.hV
    t_inv := ?_
    C0_eq := ?_
    C1_eq := rfl
    A_card := hAf.1
    A_comm := ?_
    A_sq := ?_
    A_nonab := hAf.2.2.2.1
    sq_mem := ?_
    A_inf_C0 := ?_
    V_cent_A := ?_
    t_cent_A := ?_
    N_C0_le := h61.1
    N_C1_le := h61.2.1
    N_AV_le := h61.2.2.1
    four1 := h4.1
    four2a := h4.2.1.1
    four2b := h4.2.1.2
    four3 := h4.2.2.1
    four4 := h4.2.2.2 }
  ·
    have ht2 : c.s.t * c.s.t = 1 := by
      have h := pow_orderOf_eq_one c.s.t
      rw [c.s.t_order] at h
      simpa [pow_two] using h
    have hd2 : c.d * c.d = 1 := by
      have h := pow_orderOf_eq_one c.d
      rw [c.d_order] at h
      simpa [pow_two] using h
    have hti : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
    have hdi : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right hd2
    have hmain : c.s.t * (c.d * c.s.t) * c.s.t = c.s.t * c.d := by
      calc c.s.t * (c.d * c.s.t) * c.s.t = c.s.t * c.d * (c.s.t * c.s.t) := by group
        _ = c.s.t * c.d := by rw [ht2, mul_one]
    rw [hti, mul_inv_rev, hti, hdi]
    exact hmain
  ·
    rw [c.intro5.gen, c.hV]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
      · have hd : c.d = (c.d * c.s.t) * c.s.t⁻¹ := by group
        have h1 : c.d * c.s.t ∈ zpowers (c.d * c.s.t) ⊔ zpowers c.s.t :=
          Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
        have h2 : c.s.t⁻¹ ∈ zpowers (c.d * c.s.t) ⊔ zpowers c.s.t :=
          Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers _))
        have h3 : (c.d * c.s.t) * c.s.t⁻¹ ∈ zpowers (c.d * c.s.t) ⊔ zpowers c.s.t :=
          mul_mem h1 h2
        rwa [← hd] at h3
    · apply sup_le
      · exact Subgroup.zpowers_le.2
          (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  ·
    intro a ha b hb
    have h := hAf.2.1 a ha b hb
    rw [hu2]
    exact h
  ·
    intro a ha
    have h := hAf.2.2.1 a ha
    rw [hu2]
    exact h
  ·
    rw [hu2]
    exact hAf.2.2.2.2.1
  ·
    rw [hu2]
    intro x hx
    have hxcent : x ∈ centralizer (c.s.fr.A : Set G) := by
      have hx' : x ∈ c.e.T₁ ⊓ centralizer (c.s.fr.A : Set G) := hx.2
      exact hx'.2
    have hxcen : x ∈ cen c.s.fr.A := ⟨hx.1, hxcent⟩
    have hZ : cen c.s.fr.A = c.s.fr.Z := hAf.2.2.2.2.2.2
    rw [hZ] at hxcen
    exact hxcen
  ·
    intro a ha v hv
    have hvcent : v ∈ centralizer (c.s.fr.A : Set G) := by
      have hv' : v ∈ c.e.T₁ ⊓ centralizer (c.s.fr.A : Set G) := hv.1
      exact hv'.2
    exact (Subgroup.mem_centralizer_iff.mp hvcent) a ha
  ·
    intro a ha
    have hmono : c.s.fr.A ≤ c.s.fr.S := by
      show closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} ≤
        closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂, c.s.fr.h₀}
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have haL : a ∈ L := le_trans hmono c.s.sylow_S.1 ha
    exact (Subgroup.mem_centralizer_iff.mp c.s.t_mem) a haL

end CFSG.OddStandard.HigherRank.YamadaG23
