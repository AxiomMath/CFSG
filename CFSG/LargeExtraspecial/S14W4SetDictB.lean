module

public import CFSG.LargeExtraspecial.S14W4SetDict

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Dict

open Subgroup

variable {X Y : Type*} [Group X] [Finite X] [Group Y] {T : Setting X} {ι : X →* Y}

omit [Finite X] in
theorem ι_conj (a b : X) : ι (a * b * a⁻¹) = ι a * ι b * (ι a)⁻¹ :=
  (map_mul ι (a * b) a⁻¹).trans (congrArg₂ (· * ·) (map_mul ι a b) (map_inv ι a))

theorem WU_isInv (R' : Subgroup X) (U : Subgroup Y)
    (hR : ∀ x ∈ R', x ∈ T.M → ∀ u ∈ U, ι x * u * (ι x)⁻¹ ∈ U) : IsInv T R' (WU T ι U) := by
  intro r hrR v hv
  have hv' : ∃ x ∈ U.comap ι, x ∈ T.QG ∧ T.cl x = v := T.mem_clSub_iff.mp hv
  cases hv' with
  | intro x hx =>
    cases hx with
    | intro hxU hx =>
      cases hx with
      | intro hxQ hxv =>
        subst hxv
        have hrx : (r : X) * x * (r : X)⁻¹ ∈ U.comap ι := by
          show ι ((r : X) * x * (r : X)⁻¹) ∈ U
          exact (ι_conj (ι := ι) (r : X) x).symm ▸ hR _ hrR r.2 _ hxU
        exact (congrArg (· ∈ WU T ι U) (T.ρ_cl r hxQ)).mpr
          (T.cl_mem_clSub hrx (T.conj_mem_QG r.2 hxQ))

variable {N R : Subgroup Y} {t : Y} (H : Hyp T ι N R t)
include H

theorem DW_conj (W : Submodule (ZMod 2) T.Qt) (hW : IsInv T (R.comap ι) W) {r : Y}
    (hr : r ∈ R) {d : Y} (hd : d ∈ DW T ι W) : r * d * r⁻¹ ∈ DW T ι W := by
  have hr' := H.R_lift r hr
  have hd' : ∃ x, x ∈ T.clPre W ∧ ι x = d := Subgroup.mem_map.mp hd
  cases hr' with
  | intro x hx =>
    cases hd' with
    | intro y hy =>
      cases hx with
      | intro hxM hxr =>
        cases hy with
        | intro hyW hyd =>
          subst hxr hyd
          have hQ : x * y * x⁻¹ ∈ T.QG := T.conj_mem_QG hxM hyW.1
          have hcl : T.cl (x * y * x⁻¹) ∈ W :=
            Eq.mp (congrArg (· ∈ W) (T.ρ_cl ⟨x, hxM⟩ hyW.1)) (hW ⟨x, hxM⟩ hr _ hyW.2)
          exact Subgroup.mem_map.mpr ⟨x * y * x⁻¹, ⟨hQ, hcl⟩, ι_conj x y⟩

omit [Finite X] in
theorem WU_inf_eq_bot {U₁ U₂ : Subgroup Y} (ht1 : zpowers t ≤ U₁) (h1N : U₁ ≤ N)
    (ht2 : zpowers t ≤ U₂) (h2N : U₂ ≤ N) (hint : U₁ ⊓ U₂ = zpowers t) :
    WU T ι U₁ ⊓ WU T ι U₂ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hx : ∃ x ∈ T.QG, T.cl x = v := T.exists_cl v
  cases hx with
  | intro x hx =>
    cases hx with
    | intro hxQ hxv =>
      subst hxv
      have h1 : x ∈ U₁.comap ι :=
        (clPre_WU H ht1 h1N).le (show x ∈ T.clPre (WU T ι U₁) from ⟨hxQ, hv.1⟩)
      have h2 : x ∈ U₂.comap ι :=
        (clPre_WU H ht2 h2N).le (show x ∈ T.clPre (WU T ι U₂) from ⟨hxQ, hv.2⟩)
      have h3 : x ∈ (zpowers t).comap ι := show ι x ∈ zpowers t from hint.le ⟨h1, h2⟩
      have h5 : T.cl x ∈ T.clSub (zpowers T.z) :=
        T.cl_mem_clSub ((comap_zpowers H).le h3) hxQ
      exact (Submodule.mem_bot (ZMod 2)).mp (T.clSub_zpowers_z.le h5)

end CFSG.LargeExtraspecial.S14.W4Dict
