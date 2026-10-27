module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.FinalProof

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure Ctx3 (G : Type*) [Group G] (x : G) (T V H : Subgroup G) (f : G) : Prop where
  out : Out12 G x T V
  hc : Lemma13_1Conc x V H f
  hp : Para13 x T V H

theorem normal_Hzero_of_mem {H : Subgroup G} {f g q : G} (hg : g ∈ H) (hq : q ∈ Hzero H f) :
    g * q * g⁻¹ ∈ Hzero H f := by
  have hle : Hzero H f ≤ (Hzero H f).comap (MulAut.conj g).toMonoidHom := by
    unfold Hzero
    rw [commutator_le]
    intro a ha b hb
    show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅H, zpowers f⁆
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * (⁅g, b⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (commutator_mem_commutator (H.mul_mem hg ha) hb)
      (Subgroup.inv_mem _ (commutator_mem_commutator hg hb))
  exact hle hq

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem hI : InH x V H f := InH.of_conc c.hc c.hp

theorem H0_norm_H : ∀ g ∈ H, ∀ q ∈ Hzero H f, g * q * g⁻¹ ∈ Hzero H f :=
  fun _ hg _ hq => by
    have _hc := c
    exact normal_Hzero_of_mem hg hq

theorem H0_le : Hzero H f ≤ H := le_trans le_sup_left c.hc.b_eq.symm.le

theorem x_mem_H : x ∈ H := c.hI.x_mem

theorem x_notin_H0 : x ∉ Hzero H f := c.hc.b_not

theorem x_sq : x * x = 1 := c.out.x_sq

theorem V_le_H0 [Finite G] : V ≤ Hzero H f := InH.V_le_Hzero c.out c.hI

theorem x_comm_V {v : G} (hv : v ∈ V) : x * v = v * x := c.out.x_comm hv

theorem mem_H_iff {g : G} : g ∈ H ↔ ∃ q ∈ Hzero H f, g = q ∨ g = q * x := by
  have := (mem_sup_zpowers_invol (N := Hzero H f) c.out.x_sq
    (fun q hq => c.H0_norm_H x c.x_mem_H q hq) (g := g))
  rw [← c.hc.b_eq] at this
  exact this

theorem card_H : Nat.card H = 2 * Nat.card (Hzero H f) := by
  have := card_sup_zpowers_invol (N := Hzero H f) c.out.x_sq
    (fun q hq => c.H0_norm_H x c.x_mem_H q hq) c.hc.b_not
  rw [← c.hc.b_eq] at this
  exact this

theorem C_H0_x [Finite G] : Hzero H f ⊓ centralizer ({x} : Set G) = V := by
  apply le_antisymm
  · rintro q ⟨hqP, hqC⟩
    have hqH : q ∈ H ⊓ centralizer ({x} : Set G) := ⟨c.H0_le hqP, hqC⟩
    rw [InH.C_H_x c.out c.hI] at hqH
    obtain ⟨v, hv, h1 | h1⟩ := (c.out.mem_EV).1 hqH
    · rw [h1]; exact hv
    · exfalso
      apply c.x_notin_H0
      have : x = v⁻¹ * q := by rw [h1]; group
      rw [this]
      exact (Hzero H f).mul_mem ((Hzero H f).inv_mem (c.V_le_H0 hv)) hqP
  · intro v hv
    refine ⟨c.V_le_H0 hv, ?_⟩
    show v ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact c.x_comm_V hv

theorem Hstar_two : IsPGroup 2 ↥(H ⊔ T) := c.hp.Hstar_sylow.2.1

theorem Hstar_le_N : H ⊔ T ≤ normalizer (V : Set G) := c.hp.Hstar_sylow.1

theorem Hstar_inf_C [Finite G] : (H ⊔ T) ⊓ centralizer (V : Set G) = H :=
  eq_of_sylow_le c.hc.sylow inf_le_right (le_inf le_sup_left c.hc.sylow.1)
    (c.Hstar_two.to_le inf_le_left)

theorem T_comm_x {t : G} (ht : t ∈ T) : t * x = x * t := by
  have : t ∈ centralizer ({x} : Set G) := c.out.T_sylow.1 ht
  exact (mem_centralizer_iff.1 this x rfl).symm

theorem T_norm_H {t : G} (ht : t ∈ T) : t ∈ normalizer (H : Set G) := c.hp.T_norm ht

theorem H_C_V : H ≤ centralizer (V : Set G) := c.hc.sylow.1

theorem H_two : IsPGroup 2 ↥H := c.Hstar_two.to_le le_sup_left

theorem relIndex_le_two : H.relIndex (H ⊔ T) ≤ 2 := c.hp.Hstar_index

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
