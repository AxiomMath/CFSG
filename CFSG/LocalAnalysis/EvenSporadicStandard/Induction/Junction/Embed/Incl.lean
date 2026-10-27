module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Embed.Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] (Y : Subgroup H)

omit [Finite H] in
theorem map_subtype_conjClosure_le {Lp S : Subgroup ↥Y} {S' : Subgroup H}
    (hS : S ≤ S'.comap Y.subtype) :
    (conjClosure Lp S).map Y.subtype ≤ conjClosure (Lp.map Y.subtype) S' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun g hg => ?_
  rw [← Subgroup.map_le_iff_le_comap, map_subtype_conj]
  exact map_conj_le_conjClosure (hS hg)

theorem embed_layer_eq {M T : Subgroup H} {Lp Li Ut : Subgroup ↥Y} {s : ↥Y} (hMY : M ≤ Y)
    (hMYn : (M.subgroupOf Y).Normal) (hM : IsCompIn M (centralizer (T : Set H)))
    (hperfY : ∀ P : Subgroup ↥Y, ⁅P, P⁆ = P → P ≤ M.subgroupOf Y)
    (hTU : T ≤ Ut.map Y.subtype) (hsU : s ∈ normalizer (Ut : Set ↥Y))
    (hLi : Li ≤ M.subgroupOf Y)
    (hLiC : IsCompIn Li (centralizer (Ut : Set ↥Y)))
    (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj s).toMonoidHom)
    (heq : Li ⊔ Li.map (MulAut.conj s).toMonoidHom =
      conjClosure Lp (layerIn (centralizer (Ut : Set ↥Y)))) :
    Li.map Y.subtype ⊔ (Li.map Y.subtype).map (MulAut.conj (s : H)).toMonoidHom =
      conjClosure (Lp.map Y.subtype)
        (layerIn (centralizer ((Ut.map Y.subtype : Subgroup H) : Set H))) := by
  set UH : Subgroup H := Ut.map Y.subtype with hUH
  set CH : Subgroup H := centralizer (UH : Set H) with hCH
  set Q : Subgroup ↥Y := Li ⊔ Li.map (MulAut.conj s).toMonoidHom with hQ
  have hQH : Li.map Y.subtype ⊔ (Li.map Y.subtype).map (MulAut.conj (s : H)).toMonoidHom =
      Q.map Y.subtype := by
    rw [hQ, Subgroup.map_sup, map_subtype_conj]
  rw [hQH]
  have hCT : CH ≤ centralizer (T : Set H) := Subgroup.centralizer_le (by exact_mod_cast hTU)
  have hlay : layerIn (centralizer (Ut : Set ↥Y)) ≤ (layerIn CH).comap Y.subtype := by
    rw [layerIn_le_iff]
    intro Z hZ
    have hZM : Z ≤ M.subgroupOf Y := hperfY Z (Subgroup.isPerfect_iff.1 hZ.isQuasisimple.1)
    have := isCompIn_map_subtype Y hMY hM hTU hZM hZ
    exact Subgroup.map_le_iff_le_comap.1 (le_layerIn_of_isCompIn this)
  refine le_antisymm ?_ ?_
  · rw [heq]
    exact map_subtype_conjClosure_le Y hlay
  · have hLpQ : Lp.map Y.subtype ≤ Q.map Y.subtype := Subgroup.map_mono hincl
    have hQnorm : layerIn (centralizer (Ut : Set ↥Y)) ≤ normalizer (Q : Set ↥Y) := by
      rw [heq]
      exact le_normalizer_conjClosure _ _
    have hQM : Q.map Y.subtype ≤ M := by
      have hQ' : Q ≤ M.subgroupOf Y := by
        refine sup_le hLi ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hMYn.conj_mem x (hLi hx) s
      rintro _ ⟨x, hx, rfl⟩
      exact hQ' hx
    have hQC : Q.map Y.subtype ≤ CH := by
      refine le_trans (Subgroup.map_mono ?_) (map_subtype_centralizer Y Ut |>.le.trans inf_le_left)
      refine sup_le hLiC.1 ?_
      rintro _ ⟨x, hx, rfl⟩
      refine mem_centralizer_iff.2 fun u hu => ?_
      have hu' : s⁻¹ * u * s ∈ Ut := by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Ut : Set ↥Y)).inv_mem hsU) u).1 hu
        simpa using this
      have := mem_centralizer_iff.1 (hLiC.1 hx) _ hu'
      calc u * (s * x * s⁻¹) = s * ((s⁻¹ * u * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * u * s)) * s⁻¹ := by rw [this]
        _ = (s * x * s⁻¹) * u := by group
    have hlayH : layerIn CH ≤ normalizer ((Q.map Y.subtype : Subgroup H) : Set H) := by
      rw [layerIn_le_iff]
      intro Z hZ
      have h2 : ((M ⊓ CH).subgroupOf CH).IsSubnormal := by
        have : (M ⊓ CH).subgroupOf CH = M.subgroupOf CH := by
          ext x
          simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
        rw [this]
        exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCT hM.2.2
      rcases CFSG.LocalCores.component_subnormal_subgroup hZ.2 h2 with h1 | h1
      · have hZA : Z ≤ M ⊓ CH := fun x hx =>
          (show (⟨x, hZ.1 hx⟩ : ↥CH) ∈ (M ⊓ CH).subgroupOf CH from h1 hx)
        have hZY : Z ≤ Y := (hZA.trans inf_le_left).trans hMY
        have hZD : Z ≤ CH ⊓ Y := le_inf (hZA.trans inf_le_right) hZY
        have hZc : IsCompIn Z (CH ⊓ Y) := isCompIn_of_le hZ hZD inf_le_left
        have hZt := isCompIn_comap_subtype Y hZY (Ut := Ut) hZc
        have hZn : Z.subgroupOf Y ≤ normalizer (Q : Set ↥Y) :=
          (le_layerIn_of_isCompIn hZt).trans hQnorm
        intro z hz
        have : (⟨z, hZY hz⟩ : ↥Y) ∈ normalizer (Q : Set ↥Y) := hZn hz
        have := Subgroup.le_normalizer_map (Y.subtype) ⟨⟨z, hZY hz⟩, this, rfl⟩
        rwa [Subgroup.coe_map] at this
      · have h1' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hZ.1 h1
        rw [inf_eq_left.2 (inf_le_right : M ⊓ CH ≤ CH)] at h1'
        have hZc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1'
        intro z hz
        refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun q hq => ?_)
        exact mem_centralizer_iff.1 (hZc hz) q ⟨hQM hq, hQC hq⟩
    exact conjClosure_le_of_le_normalizer hLpQ hlayH

end CFSG.EvenSporadicStandard.Induction.Junction
