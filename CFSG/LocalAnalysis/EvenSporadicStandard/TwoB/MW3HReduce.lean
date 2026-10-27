module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionMonsterW3

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.Monster.Visible CFSG.Monster.B.TwoA.Census CFSG.Monster.Spin CFSG.Monster.Griess
  CFSG.Monster.Generated

theorem center_map_subtype_map_of_injective {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (K : Subgroup G) :
    (center ↥(K.map f)).map (K.map f).subtype = ((center ↥K).map K.subtype).map f :=
  RankThree.PartOne.Torsion37.inSubgroup_center_map f hf K

theorem center_map_subtype_cent2_conj {G : Type} [Group G] (g α β : G) :
    (center ↥(cent2 (g * α * g⁻¹) (g * β * g⁻¹))).map
        (cent2 (g * α * g⁻¹) (g * β * g⁻¹)).subtype =
      ((center ↥(cent2 α β)).map (cent2 α β).subtype).map (MulAut.conj g).toMonoidHom := by
  rw [← map_conj_cent2 g α β]
  exact center_map_subtype_map_of_injective _ (MulAut.conj g).injective _

theorem map_center_centralizer_mk {G : Type} [Group G] {H : Subgroup G} {z : G} (hz : z ∈ H) :
    ((center ↥(centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H))).map
        (centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H)).subtype).map H.subtype =
      (center ↥(H ⊓ centZ z)).map (H ⊓ centZ z).subtype := by
  have hc := RankThree.PartOne.Torsion37.center_map_mulEquiv (centralizerEquivInf' hz)
  rw [Subgroup.map_map, ← hc, Subgroup.map_map]
  rfl



theorem map_centralizer_cosetRep_one_visGriess :
    (centralizer ({cosetRep 1} : Set Gvis)).map visGriess =
      cent2 (visGriess (cosetRep 1)) xGriess := by
  ext v
  constructor
  · intro hv
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
    · have h := congrArg visGriess (rhoGvis_zQ_comm c)
      rw [map_mul, map_mul] at h
      exact mem_centralizer_singleton_iff.2 h
  · intro hv
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hv
    have hvG : (v : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
      rw [← map_cent_xGriess]
      exact ⟨v, h2, rfl⟩
    have h1' : v * visGriess (cosetRep 1) = visGriess (cosetRep 1) * v :=
      mem_centralizer_singleton_iff.1 h1
    refine ⟨⟨v, hvG⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact Subtype.ext (congrArg (fun a : MGriess => (a : SpaceB ≃ₗ[ℚ] SpaceB)) h1')

theorem exists_conj_visGriess_cosetRep_one :
    ∃ g : MGriess, g * visGriess (cosetRep 1) * g⁻¹ = tGriess ∧ g * xGriess * g⁻¹ = uW3 :=
  ⟨⟨gW3, Gmat_le_AutO gW3_mem_Gmat⟩, Subtype.ext gW3_conj_h1, Subtype.ext rfl⟩

theorem center_cent2_tGriess_uW3
    (hZ : (center ↥(centralizer ({cosetRep 1} : Set Gvis))).map
        (centralizer ({cosetRep 1} : Set Gvis)).subtype =
      zpowers (rhoGvis zQ) ⊔ zpowers (cosetRep 1)) :
    (center ↥(cent2 tGriess uW3)).map (cent2 tGriess uW3).subtype =
      zpowers uW3 ⊔ zpowers tGriess := by
  obtain ⟨g, hgt, hgu⟩ := exists_conj_visGriess_cosetRep_one
  rw [← hgt, ← hgu, center_map_subtype_cent2_conj, ← map_centralizer_cosetRep_one_visGriess,
    center_map_subtype_map_of_injective _ visGriess_injective, hZ,
    Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem monsterLocalFourW3Rep_of_center_cosetRep_one
    (hZ : (Subgroup.center ↥(Subgroup.centralizer ({cosetRep 1} : Set Gvis))).map
        (Subgroup.centralizer ({cosetRep 1} : Set Gvis)).subtype =
      Subgroup.zpowers (rhoGvis zQ) ⊔ Subgroup.zpowers (cosetRep 1)) :
    MonsterLocalFourW3Rep := by
  have hw2 : orderOf (⟨uW3, uW3_mem_cent⟩ : ↥(cent tGriess)) = 2 :=
    (Subgroup.orderOf_mk uW3 uW3_mem_cent).trans orderOf_uW3
  refine ⟨⟨uW3, uW3_mem_cent⟩, hw2, ?_, Or.inl ?_, ?_⟩
  · intro hmem
    exact uW3_ne_tGriess (congrArg Subtype.val (eq_of_mem_center_cent_tGriess hmem hw2))
  · rw [Nat.card_congr (centralizerEquivInf' uW3_mem_cent).toEquiv]
    exact natCard_cent2_tGriess_uW3.trans ((tableVOrderU_eq_iff 2).2 rfl)
  · apply Subgroup.map_injective (cent tGriess).subtype_injective
    rw [map_center_centralizer_mk uW3_mem_cent, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    exact center_cent2_tGriess_uW3 hZ

end CFSG.EvenSporadicStandard.TwoB
