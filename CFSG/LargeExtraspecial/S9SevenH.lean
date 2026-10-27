module

public import CFSG.LargeExtraspecial.S9SevenG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Abstract

variable {Y V : Type*} [Group Y] [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem exists_hom_perm_three_of_finrank_eq_two (hV : finrank (ZMod 2) V = 2)
    (ρ : Y →* (V ≃ₗ[ZMod 2] V)) {y₁ y₂ : Y} (hne : ρ y₁ * ρ y₂ ≠ ρ y₂ * ρ y₁) :
    ∃ φ : Y →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ φ.ker = ρ.ker := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : MulAction Y {v : V // v ≠ 0} :=
    { smul := fun y ω => ⟨ρ y ω.1, fun h => ω.2 ((LinearEquiv.map_eq_zero_iff _).mp h)⟩
      one_smul := fun ω => Subtype.ext (by
        change ρ 1 ω.1 = ω.1
        rw [map_one]
        rfl)
      mul_smul := fun y₁ y₂ ω => Subtype.ext (by
        change ρ (y₁ * y₂) ω.1 = ρ y₁ (ρ y₂ ω.1)
        rw [map_mul]
        rfl) }
  have hsmul : ∀ (y : Y) (ω : {v : V // v ≠ 0}), ((y • ω : {v : V // v ≠ 0}) : V) = ρ y ω.1 :=
    fun _ _ => rfl
  have hcardV : Nat.card V = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV, Nat.card_zmod]
    norm_num
  have hcardΩ : Nat.card {v : V // v ≠ 0} = 3 := by
    have h1 := Nat.card_congr (Equiv.optionSubtypeNe (0 : V))
    rw [Finite.card_option, hcardV] at h1
    omega
  set e : {v : V // v ≠ 0} ≃ Fin 3 := Finite.equivFinOfCardEq hcardΩ with he
  set ψ := MulAction.toPermHom Y {v : V // v ≠ 0} with hψ
  have hψ1 : ∀ y, (Equiv.permCongrHom e).toMonoidHom.comp ψ y = 1 ↔ ρ y = 1 := by
    intro y
    have hinj := (Equiv.permCongrHom e).injective
    constructor
    · intro h
      have h2 : ψ y = 1 := hinj (by rw [map_one]; exact h)
      refine LinearEquiv.ext fun v => ?_
      by_cases hv : v = 0
      · rw [hv, map_zero, map_zero]
      · have := congrArg (fun σ : Equiv.Perm {v : V // v ≠ 0} => ((σ ⟨v, hv⟩ : _) : V)) h2
        simpa [hψ, hsmul] using this
    · intro h
      have h2 : ψ y = 1 := Equiv.ext fun ω => Subtype.ext (by
        change ρ y ω.1 = ω.1
        rw [h]
        rfl)
      change (Equiv.permCongrHom e) (ψ y) = 1
      rw [h2, map_one]
  refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp ψ, ?_, ?_⟩
  ·
    have hne' : (Equiv.permCongrHom e).toMonoidHom.comp ψ y₁ *
        (Equiv.permCongrHom e).toMonoidHom.comp ψ y₂ ≠
        (Equiv.permCongrHom e).toMonoidHom.comp ψ y₂ *
        (Equiv.permCongrHom e).toMonoidHom.comp ψ y₁ := by
      intro h
      rw [← map_mul, ← map_mul] at h
      apply hne
      rw [← map_mul, ← map_mul]
      have h2 := (hψ1 (y₁ * y₂ * (y₂ * y₁)⁻¹)).mp (by
        rw [map_mul, map_inv, h, mul_inv_cancel])
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.mp h2
    have htop := eq_top_of_not_commute (K := ((Equiv.permCongrHom e).toMonoidHom.comp ψ).range)
      ⟨y₁, rfl⟩ ⟨y₂, rfl⟩ hne'
    exact MonoidHom.range_eq_top.mp htop
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ1]

end Abstract

variable {G : Type u} [Group G] [Finite G]

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem exists_hom_perm_three
    (hidx : Nat.card (S.Lbar g) = 2 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O))
    (hLO : ¬ S.Lbar g ≤ O) :
    ∃ φ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g)) →* Equiv.Perm (Fin 3),
      Function.Surjective φ ∧ φ.ker = O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g)) := by
  obtain ⟨ℓ, hℓL, -, hℓ⟩ := exists_ell (S := S) (g := g) (O := O) hidx
  obtain ⟨ℓ', hℓ'L, hℓ'a⟩ := X.exists_ell' hLO hℓL hℓ
  obtain ⟨-, hdim⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  obtain ⟨ρ, hρ, hρ1⟩ : ∃ ρ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g)) →*
      (↥(Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) ≃ₗ[ZMod 2]
        ↥(Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)))),
      (∀ x u, ((ρ x u : Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) : S.Qt) =
        ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) ∧
      ∀ x, ρ x = 1 ↔ ∀ u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)),
        ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
    ⟨restrictHom (S.O.subtype.comp (S.Lbar g ⊔ S.Lbar ((k : G) * g)).subtype) _
      (fun x _ hu => apply_mem_Ut x.2 hu), fun _ _ => rfl,
      fun x => restrictHom_eq_one_iff _ _ _ x⟩
  have hne : ρ ⟨ℓ, mem_sup_left hℓL⟩ * ρ ⟨ℓ', mem_sup_right hℓ'L⟩ ≠
      ρ ⟨ℓ', mem_sup_right hℓ'L⟩ * ρ ⟨ℓ, mem_sup_left hℓL⟩ := by
    intro h
    have h0 := congrArg (fun e => ((e ⟨S.cl (g * S.z * g⁻¹), cl_mem_Ut _⟩ :
      Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) : S.Qt)) h
    simp only [LinearEquiv.mul_apply, hρ] at h0
    rw [hℓ'a, map_add, X.apply_cl_a_of_mem_Lbar hℓL, X.apply_cl_b_eq hLO hℓL hℓ,
      hℓ'a, ← add_assoc, vec_add_self, zero_add] at h0
    have h2 : S.cl (g * S.z * g⁻¹) = 0 := by
      calc S.cl (g * S.z * g⁻¹) = S.cl (g * S.z * g⁻¹) +
            S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) -
            S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := (add_sub_cancel_right _ _).symm
        _ = 0 := by rw [← h0, sub_self]
    exact cl_conj_z_ne_zero S X.hyp4.conj_mem X.hyp4.conj_ne h2
  have hker : ρ.ker = O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g)) := by
    ext x
    rw [MonoidHom.mem_ker, hρ1, mem_subgroupOf]
    constructor
    · intro h
      exact X.cenU_le hLO hℓL hℓ hℓ'L hℓ'a (mem_cenU.mpr ⟨x.2, h⟩)
    · intro h u hu
      exact X.fix_Ut h hu
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_perm_three_of_finrank_eq_two hdim ρ hne
  exact ⟨φ, hφs, hφk.trans hker⟩

end Hyp97

end CFSG.LargeExtraspecial.S9
