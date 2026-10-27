module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def conjugateJoin {G : Type u} [Group G] (subgroup : Subgroup G) : Subgroup G :=
  ⨆ member : G, subgroup.map (MulAut.conj member).toMonoidHom

theorem le_conjugateJoin {G : Type u} [Group G] (subgroup : Subgroup G) : subgroup ≤ conjugateJoin subgroup := by
  have hidentity : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext element; simp
  have hle := le_iSup (fun member : G => subgroup.map (MulAut.conj member).toMonoidHom) (1 : G)
  rw [hidentity, Subgroup.map_id] at hle
  exact hle

theorem conjugateJoin_normal {G : Type u} [Group G] (subgroup : Subgroup G) : (conjugateJoin subgroup).Normal := by
  apply Subgroup.Normal.mk
  intro element helement member
  have hmap : (conjugateJoin subgroup).map (MulAut.conj member).toMonoidHom ≤ conjugateJoin subgroup := by
    rw [conjugateJoin, Subgroup.map_iSup]
    apply iSup_le
    intro conjugator
    rw [← subgroup_map_conj_mul]
    exact le_iSup (fun member : G => subgroup.map (MulAut.conj member).toMonoidHom) (member * conjugator)
  have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj member).toMonoidHom helement)
  exact hmem

theorem conjugateJoin_le_normal {G : Type u} [Group G]
    (subgroup normal : Subgroup G) [normal.Normal] (hle : subgroup ≤ normal) : conjugateJoin subgroup ≤ normal := by
  apply iSup_le
  intro conjugator
  rintro element ⟨representative, hrepresentative, rfl⟩
  exact (inferInstance : normal.Normal).conj_mem representative (hle hrepresentative) conjugator

end CFSG.RankThreeEvenClassification.Helpers
