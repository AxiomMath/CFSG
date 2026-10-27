module

public import CFSG.GH74.Uniqueness.SU.KI1r4QAct
public import CFSG.GH74.Uniqueness.SU.KI1r4QAut
public import CFSG.GH74.Uniqueness.SU.KI1r4QSyl

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.SU5
open scoped commutatorElement

variable {H : Type} [Group H]

theorem not_abelian_of_isL34Type {R : Subgroup H} (hL : IsL34Type ↥R) :
    ¬ ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
  intro h
  obtain ⟨e⟩ := isL34Type_iff.mp hL
  have h1 := h (e.symm (gen 0) : H) (e.symm (gen 0)).2 (e.symm (gen 2) : H) (e.symm (gen 2)).2
  have h2 : e.symm (gen 0) * e.symm (gen 2) = e.symm (gen 2) * e.symm (gen 0) := Subtype.ext h1
  have h3 := congrArg e h2
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
  exact absurd h3 (by decide)

theorem conj_mem_iff_of_central_commutators {R U : Subgroup H} (hUR : U ≤ R)
    (hcom : ∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) (hZU : ∀ z ∈ center ↥R, (z : H) ∈ U)
    {ρ : H} (hρ : ρ ∈ R) (u : H) : u ∈ U ↔ ρ * u * ρ⁻¹ ∈ U := by
  have key : ∀ ρ ∈ R, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    intro ρ hρ u hu
    have hc : ρ * u * ρ⁻¹ * u⁻¹ ∈ U := hZU _ (hcom ⟨ρ, hρ⟩ ⟨u, hUR hu⟩)
    have e : ρ * u * ρ⁻¹ = (ρ * u * ρ⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact U.mul_mem hc hu
  refine ⟨key ρ hρ u, fun h => ?_⟩
  have := key ρ⁻¹ (R.inv_mem hρ) _ h
  simpa [mul_assoc] using this

theorem swap_of_quaternion [Finite H] {R U₁ U₂ : Subgroup H} (hF : L34Facts R U₁ U₂) (x : H)
    (hx2 : x * x = 1) (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hQ8 : Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) :
    ∀ u : H, u ∈ U₁ ↔ x * u * x⁻¹ ∈ U₂ := by
  have hxN : x ∈ normalizer (R : Set H) :=
    Subgroup.mem_normalizer_iff.mpr (mem_iff_conj_of_involution R x hx2 hN)
  have hm1 := conj_map_eq_or hF x hxN U₁ hF.A_le hF.A_E
  have hne : U₁.map (MulAut.conj x).toMonoidHom ≠ U₁ := by
    intro heq
    have hxU : ∀ u : H, u ∈ U₁ ↔ x * u * x⁻¹ ∈ U₁ := mem_iff_conj_of_map_eq heq
    have hU16 : Nat.card U₁ = 16 := by have := hF.A_E.2; norm_num at this; exact this
    have hsq : ∀ u ∈ U₁, u * u = 1 := fun u hu => by
      have := (SU5.isElemAbelian_iff.mp hF.A_E.1).2 u hu
      rwa [pow_two] at this
    have h4 := card_fixed_ge_four U₁ hU16 hsq x hx2 hxU
    obtain ⟨e8⟩ := hQ8
    have hle : centralizer ({x} : Set H) ⊓ U₁ ≤ centralizer ({x} : Set H) ⊓ R :=
      inf_le_inf_left _ hF.A_le
    have hW : Nat.card ((centralizer ({x} : Set H) ⊓ U₁).subgroupOf
        (centralizer ({x} : Set H) ⊓ R)) = Nat.card ↥(centralizer ({x} : Set H) ⊓ U₁) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have h2 := card_le_two_of_sq_one e8 ((centralizer ({x} : Set H) ⊓ U₁).subgroupOf
        (centralizer ({x} : Set H) ⊓ R))
      (fun w hw => by
        have hwU : ((w : ↥(centralizer ({x} : Set H) ⊓ R)) : H) ∈ U₁ :=
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)).2
        exact Subtype.ext (hsq _ hwU))
    omega
  have h1 : U₁.map (MulAut.conj x).toMonoidHom = U₂ := hm1.resolve_left hne
  exact mem_iff_conj_of_map_eq h1

theorem swap_of_mul {R U₁ U₂ : Subgroup H} (hU₂R : U₂ ≤ R)
    (hcom : ∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) (hZU₂ : ∀ z ∈ center ↥R, (z : H) ∈ U₂) {x : H}
    (hswap : ∀ u : H, u ∈ U₁ ↔ x * u * x⁻¹ ∈ U₂) {r : H} (hr : r ∈ R) (u : H) :
    u ∈ U₁ ↔ (r⁻¹ * x) * u * (r⁻¹ * x)⁻¹ ∈ U₂ := by
  rw [hswap u]
  have := conj_mem_iff_of_central_commutators hU₂R hcom hZU₂ (R.inv_mem hr) (x * u * x⁻¹)
  have e : (r⁻¹ * x) * u * (r⁻¹ * x)⁻¹ = r⁻¹ * (x * u * x⁻¹) * r⁻¹⁻¹ := by group
  rw [e]
  exact this

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
