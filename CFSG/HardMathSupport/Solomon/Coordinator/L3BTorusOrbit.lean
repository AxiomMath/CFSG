module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Pointwise

theorem exists_invariant_of_decomposition {Y : Type*} [Group Y] [Finite Y] {Γ : Type*} [Group Γ]
    [Finite Γ] (ρ : Γ →* MulAut Y) (R : Subgroup (MulAut Y)) (M : Subgroup Γ) (S₀ : Subgroup Y)
    (hdec : ∀ α : MulAut Y, ∃ A : Γ, ∃ r ∈ R, α = ρ A * r)
    (hR : ∀ r ∈ R, S₀.map r.toMonoidHom = S₀)
    (hM : ∀ A ∈ M, S₀.map (ρ A).toMonoidHom = S₀) (hidx : ¬ 3 ∣ M.index)
    (B : Subgroup (MulAut Y)) (hB : IsPGroup 3 B) :
    ∃ α : MulAut Y, ∀ β ∈ B, (S₀.map α.toMonoidHom).map β.toMonoidHom = S₀.map α.toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsmul : ∀ (α : MulAut Y) (S : Subgroup Y), α • S = S.map α.toMonoidHom := fun α S => rfl
  let _ : MulAction Γ (Subgroup Y) := MulAction.compHom (Subgroup Y) ρ
  have hΓsmul : ∀ (A : Γ) (S : Subgroup Y), A • S = ρ A • S := fun A S => rfl
  have horb : MulAction.orbit (MulAut Y) S₀ = MulAction.orbit Γ S₀ := by
    ext T
    constructor
    · rintro ⟨α, rfl⟩
      obtain ⟨A, r, hr, rfl⟩ := hdec α
      refine ⟨A, ?_⟩
      show ρ A • S₀ = (ρ A * r) • S₀
      rw [mul_smul, hsmul r, hR r hr]
    · rintro ⟨A, rfl⟩
      exact ⟨ρ A, rfl⟩
  have hle : M ≤ MulAction.stabilizer Γ S₀ := fun A hA => by
    rw [MulAction.mem_stabilizer_iff, hΓsmul, hsmul]
    exact hM A hA
  have hcard : ¬ 3 ∣ Nat.card (MulAction.orbit (MulAut Y) S₀) := by
    rw [horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact fun h => hidx (h.trans (Subgroup.index_dvd_of_le hle))
  obtain ⟨⟨T, hT⟩, hfix⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card
    (MulAction.orbit (MulAut Y) S₀) hcard
  obtain ⟨α, rfl⟩ := hT
  refine ⟨α, fun β hβ => ?_⟩
  have := hfix ⟨β, hβ⟩
  have h2 := congrArg Subtype.val this
  rw [← hsmul]
  exact h2

theorem map_eq_of_map_le {P : Type*} [Group P] [Finite P] (α : MulAut P) (S : Subgroup P)
    (h : S.map α.toMonoidHom ≤ S) : S.map α.toMonoidHom = S :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective α.injective])

@[expose] def FixedTorus (Y : Type*) [Group Y] : Prop :=
  ∀ B : Subgroup (MulAut Y), IsPGroup 3 B → ∃ S : Subgroup Y, S ≠ ⊥ ∧ Nat.Coprime 3 (Nat.card S) ∧
    ∀ β ∈ B, S.map β.toMonoidHom = S

theorem fixedTorus_of_decomposition {Y : Type*} [Group Y] [Finite Y] {Γ : Type*} [Group Γ]
    [Finite Γ] (ρ : Γ →* MulAut Y) (R : Subgroup (MulAut Y)) (M : Subgroup Γ) (S₀ : Subgroup Y)
    (hdec : ∀ α : MulAut Y, ∃ A : Γ, ∃ r ∈ R, α = ρ A * r)
    (hR : ∀ r ∈ R, S₀.map r.toMonoidHom = S₀)
    (hM : ∀ A ∈ M, S₀.map (ρ A).toMonoidHom = S₀) (hidx : ¬ 3 ∣ M.index)
    (hS₀ : S₀ ≠ ⊥) (hcop : Nat.Coprime 3 (Nat.card S₀)) : FixedTorus Y := by
  intro B hB
  obtain ⟨α, hα⟩ := exists_invariant_of_decomposition ρ R M S₀ hdec hR hM hidx B hB
  refine ⟨S₀.map α.toMonoidHom, ?_, ?_, hα⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ α.injective]
  · rwa [Subgroup.card_map_of_injective α.injective]

theorem FixedTorus.of_mulEquiv {Y P : Type*} [Group Y] [Group P] (e : Y ≃* P)
    (h : FixedTorus P) : FixedTorus Y := by
  intro B hB
  obtain ⟨S, hS, hcop, hfix⟩ := h (B.map (MulAut.congr e).toMonoidHom) (hB.map _)
  refine ⟨S.map e.symm.toMonoidHom, ?_, ?_, fun β hβ => ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · have hβ' := hfix ((MulAut.congr e).toMonoidHom β) ⟨β, hβ, rfl⟩
    rw [Subgroup.map_map]
    have hcomp : β.toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom β).toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hβ']

end CFSG.HardMathSupport.Solomon.Coordinator
