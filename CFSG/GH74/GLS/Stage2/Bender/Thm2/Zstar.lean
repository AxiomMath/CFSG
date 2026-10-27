module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Zstar

variable {G : Type} [Group G] [Finite G]

@[expose] def CentMod (H : Subgroup G) (z : G) : Prop := ∀ k ∈ H, ⁅k, z⁆ ∈ pPrimeCoreOf 2 H

omit [Finite G] in
theorem centMod_of_mem_zStar {H : Subgroup G} {z : G} (h : z ∈ zStar H) : CentMod H z :=
  fun k hk => h.2.2.2 k hk

theorem false_of_centMod_move {H U : Subgroup G} {z t' n : G} (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U)
    (ht'U : t' ∈ U) (hne : t' ≠ z) (hn : n ∈ H) (hmove : n * z * n⁻¹ = t') (hc : CentMod H z) : False := by
  have h1 := hc n hn
  have h2 : ⁅n, z⁆ = t' * z⁻¹ := by
    simp only [commutatorElement_def]
    rw [← hmove]
  rw [h2] at h1
  have hcop := coprime_orderOf_of_mem_pPrimeCoreOf Nat.prime_two h1
  have hw : t' * z⁻¹ ∈ U := mul_mem ht'U (inv_mem hzU)
  have hdvd : orderOf (t' * z⁻¹) ∣ 2 := by
    have h3 : orderOf (⟨t' * z⁻¹, hw⟩ : ↥U) ∣ Monoid.exponent ↥U := Monoid.order_dvd_exponent _
    have h4 : Monoid.exponent ↥U ∣ 2 := hU.1.exponent_dvd_p
    have := h3.trans h4
    rwa [Subgroup.orderOf_mk] at this
  have h5 : orderOf (t' * z⁻¹) = 1 := (Nat.Coprime.symm hcop).eq_one_of_dvd hdvd
  apply hne
  have := orderOf_eq_one_iff.mp h5
  exact mul_inv_eq_one.mp this

omit [Finite G] in
theorem oResidual_normal' (p : ℕ) (Y : Type*) [Group Y] : (oResidual p Y).Normal where
  conj_mem n hn g := by
    unfold oResidual at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      have h1 : orderOf ((MulAut.conj g).toMonoidHom x) = orderOf x :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      have h2 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
      rw [h2] at h1
      show Nat.Coprime (orderOf (g * x * g⁻¹)) p
      rw [h1]
      exact hx
    | one => simp
    | mul a b _ _ iha ihb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ iha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ iha

omit [Finite G] in
theorem conj_mem_O2Of {M : Subgroup G} {m x : G} (hm : m ∈ M) (hx : x ∈ O2Of M) : m * x * m⁻¹ ∈ O2Of M := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, (oResidual_normal' 2 ↥M).conj_mem y hy _, rfl⟩

omit [Finite G] in
theorem false_of_move_M [Finite G] {M U : Subgroup G} {z t n : G} (hU : IVK.IsFourSubgroup U) (hz2 : z * z = 1)
    (hzU : z ∈ U) (htU : t ∈ U) (htz : t ≠ z) (ht1 : t ≠ 1)
    (hz : z ∈ zStar M ∨ U ⊓ O2Of M = zpowers z) (hn : n ∈ M) (hmove : n * z * n⁻¹ = t) : False := by
  rcases hz with hz | hz
  · exact false_of_centMod_move hU hzU htU htz hn hmove (centMod_of_mem_zStar hz)
  · have hzO : z ∈ O2Of M := by
      have : z ∈ U ⊓ O2Of M := by rw [hz]; exact mem_zpowers z
      exact this.2
    have htO : t ∈ O2Of M := hmove ▸ conj_mem_O2Of hn hzO
    have : t ∈ U ⊓ O2Of M := ⟨htU, htO⟩
    rw [hz] at this
    rcases eq_one_or_eq_of_mem_zpowers hz2 this with h | h
    · exact ht1 h
    · exact htz h

end Zstar

end CFSG.GH74.GLS.Stage2.Bender.Thm2
