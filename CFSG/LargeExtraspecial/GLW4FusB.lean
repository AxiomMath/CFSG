module

public import CFSG.LargeExtraspecial.GLW4E
public import CFSG.LargeExtraspecial.GLW4Abs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem eq_zero_or_eq_dm {t : S.O} {V : Submodule (ZMod 2) S.Qt}
    (hrange : ∀ x, dm t x ∈ V) (honto : ∀ v ∈ V, ∃ x, dm t x = v)
    (hV6 : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {R : Set S.O} (hrt : ∀ r ∈ R, r * t = t * r)
    (hR : ∀ g ∈ omegaGroup q hq, ∃ r ∈ R, ∀ v : V,
      ((g v : V) : S.Qt) = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    {T₀ : S.Qt →ₗ[ZMod 2] S.Qt} (hker : ∀ x, dm t x = 0 → T₀ x = 0) (hT₀V : ∀ x, T₀ x ∈ V)
    (hT₀R : ∀ r ∈ R, ∀ x,
      T₀ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (T₀ x)) :
    T₀ = 0 ∨ T₀ = dm t := by
  let φ : S.Qt →ₗ[ZMod 2] V := (dm t).codRestrict V hrange
  have hφ : ∀ x, ((φ x : V) : S.Qt) = dm t x := fun x => rfl
  have hsurj : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨x, hx⟩ := honto v v.2
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective hsurj
  have hσφ : ∀ v, φ (σ v) = v := fun v => LinearMap.congr_fun hσ v
  let f : V →ₗ[ZMod 2] V := (T₀ ∘ₗ σ).codRestrict V fun v => hT₀V (σ v)
  have hf : ∀ x, ((f (φ x) : V) : S.Qt) = T₀ x := fun x => by
    change T₀ (σ (φ x)) = T₀ x
    have h0 : dm t (σ (φ x) - x) = 0 := by
      rw [map_sub, ← hφ, ← hφ, hσφ, sub_self]
    have := hker _ h0
    rwa [map_sub, sub_eq_zero] at this
  have hrdm : ∀ r ∈ R, ∀ x, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (dm t x) =
      dm t ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := fun r hr x => by
    rw [dm_apply, dm_apply, map_sub, ← Config.mul_apply, ← Config.mul_apply, hrt r hr]
  have hcomm : ∀ g ∈ omegaGroup q hq, ∀ v, f (g v) = g (f v) := by
    intro g hg v
    obtain ⟨r, hr, hrg⟩ := hR g hg
    obtain ⟨x, hx⟩ := honto v v.2
    have hv : v = φ x := Subtype.ext hx.symm
    have e : ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((φ x : V) : S.Qt)) =
        ((φ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) : V) : S.Qt) := by rw [hφ, hφ, hrdm r hr]
    have e' : g (φ x) = φ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := Subtype.ext ((hrg _).trans e)
    apply Subtype.ext
    rw [hv, e', hf, hrg, hf, hT₀R r hr]
  rcases eq_zero_or_eq_id_of_commute_omega hV6 hq f hcomm with h0 | h1
  · left
    refine LinearMap.ext fun x => ?_
    rw [← hf, h0, LinearMap.zero_apply, Submodule.coe_zero, LinearMap.zero_apply]
  · right
    refine LinearMap.ext fun x => ?_
    rw [← hf, h1, LinearMap.id_apply, hφ]

end CFSG.LargeExtraspecial.GLW4
