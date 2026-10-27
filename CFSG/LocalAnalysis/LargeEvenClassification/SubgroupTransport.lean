module

public import CFSG.LocalAnalysis.LargeEvenClassification.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem subgroup_map_inverse_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (coordinates : Ambient ≃* Target)
    (SubgroupOfAmbient : Subgroup Ambient) :
    (SubgroupOfAmbient.map coordinates.toMonoidHom).map coordinates.symm.toMonoidHom =
      SubgroupOfAmbient := by
  have hcomposition : coordinates.symm.toMonoidHom.comp coordinates.toMonoidHom =
      MonoidHom.id Ambient := by
    ext element
    exact coordinates.symm_apply_apply element
  rw [Subgroup.map_map, hcomposition, Subgroup.map_id]

theorem subgroup_map_forward_inverse_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (coordinates : Ambient ≃* Target)
    (SubgroupOfTarget : Subgroup Target) :
    (SubgroupOfTarget.map coordinates.symm.toMonoidHom).map coordinates.toMonoidHom =
      SubgroupOfTarget := by
  have hcomposition : coordinates.toMonoidHom.comp coordinates.symm.toMonoidHom =
      MonoidHom.id Target := by
    ext element
    exact coordinates.apply_symm_apply element
  rw [Subgroup.map_map, hcomposition, Subgroup.map_id]

theorem elementary_map {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (homomorphism : Ambient →* Target) :
    IsElemAbelian prime (Elementary.map homomorphism) := CFSG.Open.IsElemAbelian.map helementary _

theorem pRank_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {Target : Type targetUniverse} [Group Target] [Finite Target] {prime : ℕ}
    (hprime : 1 < prime) (coordinates : Ambient ≃* Target) (SubgroupOfAmbient : Subgroup Ambient) :
    pRank prime (SubgroupOfAmbient.map coordinates.toMonoidHom) = pRank prime SubgroupOfAmbient := by
  have hforward : ∀ (Source : Subgroup Ambient),
      pRank prime Source ≤ pRank prime (Source.map coordinates.toMonoidHom) := by
    intro Source
    obtain ⟨Elementary, hle, helementary, hcard⟩ := pRank_witness hprime Source
    apply le_csSup
    · refine ⟨Nat.card Target, ?_⟩
      rintro rank ⟨OtherElementary, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime OtherElementary hotherCard
    · exact ⟨Elementary.map coordinates.toMonoidHom, Subgroup.map_mono hle,
        elementary_map Elementary helementary coordinates.toMonoidHom,
        (Nat.card_congr (coordinates.subgroupMap Elementary).toEquiv).symm.trans hcard⟩
  have hbackward : pRank prime (SubgroupOfAmbient.map coordinates.toMonoidHom) ≤
      pRank prime SubgroupOfAmbient := by
    obtain ⟨Elementary, hle, helementary, hcard⟩ :=
      pRank_witness hprime (SubgroupOfAmbient.map coordinates.toMonoidHom)
    have hsourceLe : Elementary.map coordinates.symm.toMonoidHom ≤ SubgroupOfAmbient := by
      have hmap := Subgroup.map_mono (f := coordinates.symm.toMonoidHom) hle
      simpa only [subgroup_map_inverse_mulEquiv] using hmap
    apply le_csSup
    · refine ⟨Nat.card Ambient, ?_⟩
      rintro rank ⟨OtherElementary, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime OtherElementary hotherCard
    · exact ⟨Elementary.map coordinates.symm.toMonoidHom, hsourceLe,
        elementary_map Elementary helementary coordinates.symm.toMonoidHom,
        (Nat.card_congr (coordinates.symm.subgroupMap Elementary).toEquiv).symm.trans hcard⟩
  exact le_antisymm hbackward (hforward SubgroupOfAmbient)

theorem centralizer_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (coordinates : Ambient ≃* Target)
    (SubgroupOfAmbient : Subgroup Ambient) :
    (Subgroup.centralizer (SubgroupOfAmbient : Set Ambient)).map coordinates.toMonoidHom =
      Subgroup.centralizer (SubgroupOfAmbient.map coordinates.toMonoidHom : Set Target) := by
  ext element
  rw [Subgroup.map_equiv_eq_comap_symm']
  change coordinates.symm element ∈ Subgroup.centralizer (SubgroupOfAmbient : Set Ambient) ↔
    element ∈ Subgroup.centralizer (SubgroupOfAmbient.map coordinates.toMonoidHom : Set Target)
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hcommutes other hother
    obtain ⟨source, hsource, rfl⟩ := hother
    have heq := congrArg coordinates (hcommutes source hsource)
    change coordinates source * element = element * coordinates source
    simpa only [map_mul, coordinates.apply_symm_apply] using heq
  · intro hcommutes other hother
    have heq := hcommutes (coordinates other) (Subgroup.mem_map.mpr ⟨other, hother, rfl⟩)
    have hmapped := congrArg coordinates.symm heq
    simpa only [map_mul, coordinates.symm_apply_apply] using hmapped

theorem isTwoLocal_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (coordinates : Ambient ≃* Target)
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) :
    IsTwoLocal (Local.map coordinates.toMonoidHom) := by
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, rfl⟩ := hlocal
  refine ⟨TwoSubgroup.map coordinates.toMonoidHom, ?_, hpgroup.map coordinates.toMonoidHom,
    Subgroup.map_equiv_normalizer_eq TwoSubgroup coordinates⟩
  intro hzero
  apply hnontrivial
  have hmap := congrArg (Subgroup.map coordinates.symm.toMonoidHom) hzero
  simpa only [subgroup_map_inverse_mulEquiv, Subgroup.map_bot] using hmap

end CFSG.LargeEvenClassification.Helpers
