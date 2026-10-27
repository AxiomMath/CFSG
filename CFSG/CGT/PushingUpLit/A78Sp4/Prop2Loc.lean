module

public import CFSG.CGT.PushingUpLit.A78Sp4.Prop2
public import CFSG.CGT.PushingUpLit.A78Sp4.Util
public import CFSG.CGT.PushingUpLit.A78Sp4.Data

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem sp4_prop2 (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) : ∀ g : G, cj g Z ≤ S → cj g Z ≤ V ∨ cj g Z ≤ V₂ := by
  intro g hgS
  have hZV : Z ≤ V := by rw [h.side₁.Z_eq]; exact inf_le_left
  have hA : ∀ E : Subgroup G, E ≤ T → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x ∧ x * x = 1) →
      Nat.card V ≤ Nat.card E → E = V ∨ E = V₂ := by
    intro E hET hE hcard
    apply h.base.A_S E (hET.trans h.base.T_le) hE
    exact le_antisymm (h.base.rank E hE) (h.base.card_V ▸ hcard)
  have hT : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (Z : Set G) → IsPGroup 2 P →
      ∃ n ∈ Subgroup.normalizer (Z : Set G), ∀ x ∈ P, n * x * n⁻¹ ∈ T := by
    intro P hP hP2
    rw [h.side₁.normalizer_Z] at hP ⊢
    exact exists_mem_conj_le_of_isSylowOf h.side₁.sylow_T hP hP2
  have hAJ : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ S →
      ∃ x ∈ Z.map (MulAut.conj g).toMonoidHom ⊓ J, x ≠ 1 := by
    intro g hgS
    refine exists_ne_one_inf_of_cyclic h.base.normal_J h.field.S_cyclic hgS ?_ ?_
    · rintro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
      have hzz := (h.base.elem_V z (hZV hz) z (hZV hz)).2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    · have hc : Nat.card (Z.map (MulAut.conj g).toMonoidHom) = Nat.card Z :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      rw [hc, h.side₁.card_Z]
      have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.base.two_le
      omega
  exact prop2 hZV h.cross.Z_le h.base.elem_V h.base.elem_V₂
    (h.base.card_V.trans h.base.card_V₂.symm) hA
    (map_conj_eq_of_ti h.side₁.ti) hT
    (fun x hxJ _ hxx => h.base.inv_mem x hxJ hxx) hAJ g hgS

end CFSG.CGT.PushingUpLit.A78Sp4
