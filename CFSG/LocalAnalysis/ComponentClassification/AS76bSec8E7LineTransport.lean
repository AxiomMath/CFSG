module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem map_conj_e7FrameLine_of
    {F F' : List (Fin Tag.E7.rank → ℤ)} {g : adjointGroup .E7 K}
    (h : ∀ d : K, g * e7FrameElt K F d * g⁻¹ = e7FrameElt K F' d) :
    (e7FrameLine K F).map (MulAut.conj g).toMonoidHom = e7FrameLine K F' := by
  rw [e7FrameLine, e7FrameLine, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨d, (h d).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨e7FrameElt K F d, ⟨d, rfl⟩, h d⟩

variable (K) in
noncomputable abbrev e7WeylRep
    (w : WeylGroup .E7) : adjointGroup .E7 K :=
  ⟨canonicalRep (coxeterSystem .E7) K w, canonicalRep_mem_adjointGroup _ K w⟩

theorem e7FrameElt_conj_weyl
    [CharP K 2] (w : WeylGroup .E7)
    {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ) (d : K) :
    e7WeylRep K w * e7FrameElt K F d * (e7WeylRep K w)⁻¹ = e7FrameElt K (F.map (w • ·)) d := by
  apply Subtype.ext
  have h := E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo (K := K) w hF (fun _ => d)
  simpa [coe_e7FrameElt, List.map_map, Function.comp_def] using h

theorem map_conj_e7FrameLine_weyl
    [CharP K 2] (w : WeylGroup .E7)
    {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ) :
    (e7FrameLine K F).map (MulAut.conj (e7WeylRep K w)).toMonoidHom =
      e7FrameLine K (F.map (w • ·)) :=
  map_conj_e7FrameLine_of (e7FrameElt_conj_weyl w hF)

theorem e7FrameElt_conj_word
    [CharP K 2] (ω : List (Fin Tag.E7.rank))
    {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ) (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd ω) * e7FrameElt K F d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd ω))⁻¹ =
      e7FrameElt K (F.map fun σ => ω.foldr (reflect .E7) σ) d := by
  rw [e7FrameElt_conj_weyl _ hF]
  simp only [wordProd_smul_eq_foldr]

theorem e7FrameElt_perm
    {F F' : List (Fin Tag.E7.rank → ℤ)} (hp : F.Perm F')
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) (d : K) :
    e7FrameElt K F d = e7FrameElt K F' d := by
  apply Subtype.ext
  rw [coe_e7FrameElt, coe_e7FrameElt]
  refine (hp.map _).prod_eq' ?_
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ ho
  intro σ σ' hσ hσ' h
  exact commute_pinnedX_of_iform_eq_zero_e7 (hr σ hσ) (hr σ' hσ') h d d

theorem e7FrameLine_perm
    {F F' : List (Fin Tag.E7.rank → ℤ)} (hp : F.Perm F')
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    e7FrameLine K F = e7FrameLine K F' := by
  rw [e7FrameLine, e7FrameLine]
  congr 1
  ext y
  simp only [Set.mem_range, e7FrameElt_perm hp hr ho]

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
