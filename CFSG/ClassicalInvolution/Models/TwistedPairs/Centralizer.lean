module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic
public import CFSG.ClassicalInvolution.WeakCT.SpAgree

public section

namespace CFSG.ClassicalInvolution.Models.TwistedPairs

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F E : Type} [Field F] [Field E] {G : Type} [Group G] {X : Type} [Group X]
  (P : TwistedB2Model F E G)

theorem TwistedB2Model.torus_comm (s : Fˣ) (t : Eˣ) :
    Commute (P.lb (torusHom F s)) (P.sb (torusHom E t)) := by
  have h := P.conj_sl t (torusHom F s)
  rw [diagConj2_torusHom] at h
  exact Commute.symm ((commute_iff_eq _ _).2 (mul_inv_eq_iff_eq_mul.mp h))

theorem TwistedB2Model.centralizer_long (hν : ∃ t, P.nu t ≠ 1) {θ : G →* X}
    (hf : Function.Injective (θ.comp P.lb)) {m : X} (hm : m ∈ (θ.comp P.lb).range)
    (hc : ∀ a ∈ (diagTorus2 E).map (θ.comp P.sb), a * m = m * a) :
    m ∈ (diagTorus2 F).map (θ.comp P.lb) := by
  obtain ⟨A, rfl⟩ := hm
  obtain ⟨t₀, ht₀⟩ := hν
  have hB : ∀ b ∈ P.lb.range, θ b = 1 → b = 1 := by
    rintro _ ⟨B', rfl⟩ h
    have : B' = 1 := hf (by simpa using h)
    rw [this, map_one]
  have h1 := hc (θ (P.sb (torusHom E t₀))) ⟨_, ⟨t₀, rfl⟩, rfl⟩
  have hx : P.lb A ∈ P.lb.range := ⟨A, rfl⟩
  have hd : P.sb (torusHom E t₀) * P.lb A * (P.sb (torusHom E t₀))⁻¹ ∈ P.lb.range := by
    rw [P.conj_sl]
    exact ⟨_, rfl⟩
  have hcomm := commute_of_map_commute' θ P.lb.range hB hx hd (by simpa using h1.symm)
  have h2 := P.conj_sl t₀ A
  rw [← hcomm, mul_inv_cancel_right] at h2
  have hlb : Function.Injective P.lb := fun a b h => hf (by simpa using congrArg θ h)
  have hA : diagConj2 (P.nu t₀) 1 A = A := (hlb h2).symm
  exact ⟨A, mem_diagTorus2_of_diagConj2_eq ht₀ hA, rfl⟩

theorem TwistedB2Model.centralizer_short (hμ : ∃ s, P.mu s ≠ 1) {θ : G →* X}
    (hf : Function.Injective (θ.comp P.sb)) {m : X} (hm : m ∈ (θ.comp P.sb).range)
    (hc : ∀ a ∈ (diagTorus2 F).map (θ.comp P.lb), a * m = m * a) :
    m ∈ (diagTorus2 E).map (θ.comp P.sb) :=
  P.swap.centralizer_long hμ hf hm hc

end CFSG.ClassicalInvolution.Models.TwistedPairs
