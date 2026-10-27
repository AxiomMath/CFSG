module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Trans

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] {z : G}

@[expose] noncomputable def FPart.transfer [Finite G] {e : Elts (Hc z) (zH z)} (f : FPart (zH z) e) :
    FPart z e.transfer where
  F := f.F.map (incl z)
  F_comm := by
    rintro _ ⟨y, -, rfl⟩
    exact coe_mul_z y
  z_mem := ⟨zH z, f.z_mem, rfl⟩
  F_s₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (f.F_s₁ y hy)
  cent := by
    have h := congrArg (Subgroup.map (incl z)) f.cent
    rw [centralizer_zH, inf_top_eq, map_centralizer_singleton, Subgroup.map_sup,
      MonoidHom.map_zpowers] at h
    exact h
  F_noOdd := by
    intro N hN hnorm hodd
    obtain ⟨hmap, hle, hcard⟩ := pullback hN
    have hN' : N.comap (incl z) = ⊥ := by
      refine f.F_noOdd _ hle (fun x hx n hn => ?_) (hcard ▸ hodd)
      have h1 : incl z x * incl z n * (incl z x)⁻¹ ∈ N := hnorm _ ⟨x, hx, rfl⟩ _ hn
      show incl z (x * n * x⁻¹) ∈ N
      rwa [map_mul, map_mul, map_inv]
    rw [← hmap, hN', Subgroup.map_bot]
  F_socle := by
    intro N hN hnorm hne
    obtain ⟨hmap, hle, hcard⟩ := pullback hN
    have hne' : N.comap (incl z) ≠ ⊥ := fun h => hne (by rw [← hmap, h, Subgroup.map_bot])
    have hz := f.F_socle _ hle (fun x hx n hn => by
      have h1 : incl z x * incl z n * (incl z x)⁻¹ ∈ N := hnorm _ ⟨x, hx, rfl⟩ _ hn
      show incl z (x * n * x⁻¹) ∈ N
      rwa [map_mul, map_mul, map_inv]) hne'
    exact hz
  T₁ := f.T₁.map (incl z)
  T₁_syl := by
    have h := isSylowIn_map f.T₁_syl
    rwa [centralizer_zH, inf_top_eq, map_centralizer_singleton] at h
  T₁_z := ⟨zH z, f.T₁_z, rfl⟩
  T₁_uniq := by
    rintro _ ⟨y, hy, rfl⟩ h2
    have : y = zH z := f.T₁_uniq y hy (by rwa [← Subgroup.orderOf_coe])
    rw [this]
    rfl
  T₁_quat := by
    obtain ⟨k, hk, ⟨e'⟩⟩ := f.T₁_quat
    exact ⟨k, hk, ⟨(Subgroup.equivMapOfInjective f.T₁ (incl z) incl_injective).symm.trans e'⟩⟩

end CFSG.GH74.Uniqueness.SU.SU13
