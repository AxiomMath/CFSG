module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Data
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Dict

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

open A44

theorem iv2_2_1_b : IV2_2_1_b := by
  intro B _ ⟨e⟩
  have hA0 : ∀ φ : MulAut B, φ ∈ A0 B ↔ (phiB e φ).1.IsA0 := fun φ => by
    rw [mem_A0_iff e, M4.isA0_iff]
  let ρ3 : G96 →* Equiv.Perm (Fin 3) := MulAction.toPermHom G96 (Fin 3)
  have hρ3 : ∀ x : G96, ∀ i : Fin 3, ρ3 x i = act3 x.1 i := fun x i => rfl
  refine ⟨ρ3.comp (phiB e).toMonoidHom, ?_, ?_⟩
  · intro σ
    have hne : ∀ a b : Fin 3, a ≠ b → σ a ≠ σ b := fun a b h => σ.injective.ne h
    obtain ⟨x, h0, h1, h2⟩ := act3_surj (σ 0) (σ 1) (σ 2) (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 1 2 (by decide))
    refine ⟨(phiB e).symm x, ?_⟩
    apply Equiv.ext
    intro i
    show ρ3 ((phiB e) ((phiB e).symm x)) i = σ i
    rw [(phiB e).apply_symm_apply, hρ3]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · ext g
    rw [MonoidHom.mem_ker, hA0]
    show ρ3 (phiB e g) = 1 ↔ _
    rw [← act3_ker _ (phiB e g).2]
    constructor
    · intro h i
      have := congrArg (fun p : Equiv.Perm (Fin 3) => p i) h
      simpa [hρ3] using this
    · intro h
      apply Equiv.ext
      intro i
      simpa [hρ3] using h i

namespace A44

theorem val_cube (x : G96) : (x ^ 3).1 = M4.mul (M4.mul x.1 x.1) x.1 := by
  rw [pow_succ, pow_two]; rfl

theorem cube_eq_one_iff {x : G96} : x ^ 3 = 1 ↔ M4.mul (M4.mul x.1 x.1) x.1 = M4.one := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [val_cube, G96.val_one] at this
  · intro h
    apply Subtype.ext
    rw [val_cube, G96.val_one]
    exact h

end A44

@[expose] noncomputable def rho4B {B : Type} [CommGroup B] (e : B ≃* Z4Z4) :
    MulAut B →* Equiv.Perm (Fin 4) :=
  (MulAction.toPermHom G96 (Fin 4)).comp (phiB e).toMonoidHom

theorem rho4B_apply {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (φ : MulAut B) (j : Fin 4) :
    rho4B e φ j = act4 (phiB e φ).1 j := rfl

end CFSG.GH74.GLS.Bg.TwoGroups
