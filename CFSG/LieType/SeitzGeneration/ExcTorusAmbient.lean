module

public import CFSG.LieType.SeitzGeneration.ExcTorusEmbed
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem sylowTorus_of_torus_data {τ : Tag} (K : Type) [Field K] (Ω : Type) [Field Ω]
    [Algebra K Ω] {p m : ℕ} {T₀ T V : Subgroup (ModGL τ Ω)} {g : ModGL τ Ω}
    (hT : T = T₀.map (MulAut.conj g).toMonoidHom) (hT₀ : IsMulCommutative T₀)
    (hTr : T ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K Ω)))
    (hconj : ∀ P : Subgroup (adjointGroup τ K), IsPGroup p P → ∃ c : adjointGroup τ K,
      (P.map (MulAut.conj c).toMonoidHom).map
        ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype) ≤ T)
    (hV : ∀ h, h ∈ V ↔ h ∈ T₀ ∧ h ^ p = 1) (hVc : Nat.card V = p ^ m) :
    SylowTorus (adjointGroup τ K) p m := by
  let ι : adjointGroup τ K →* ModGL τ Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective (algebraMap K Ω)).comp (Subgroup.subtype_injective _)
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K Ω)) := by
    change ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine SylowTorus.of_embedding ι hι (T := T) (E := V.map (MulAut.conj g).toMonoidHom)
    (by rw [hT]; exact isMulCommutative_map _ hT₀) (hrange ▸ hTr) hconj ?_ ?_
  · intro x
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hv0, hvp⟩ := (hV v).1 hv
      refine ⟨hT ▸ ⟨v, hv0, rfl⟩, ?_⟩
      rw [← map_pow, hvp, map_one]
    · rintro ⟨hxT, hxp⟩
      rw [hT] at hxT
      obtain ⟨y, hy, rfl⟩ := hxT
      refine ⟨y, (hV y).2 ⟨hy, hcg ?_⟩, rfl⟩
      rw [map_pow, hxp, map_one]
  · rw [Subgroup.card_map_of_injective hcg, hVc]

end CFSG.LieType.SeitzGeneration
