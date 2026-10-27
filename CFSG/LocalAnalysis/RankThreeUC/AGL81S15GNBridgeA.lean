module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G]

theorem omegaOneCenterOf_le_subgroup (T : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf T ≤ T := by
  rw [CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf, Subgroup.closure_le]
  exact fun x hx => hx.1.1

theorem map_omegaOneCenterOf_subgroupOf {M T : Subgroup G} (hTM : T ≤ M) :
    (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M)).map M.subtype =
      CFSG.Quasithin.omegaOneCenterOf T := by
  rw [CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf, MonoidHom.map_closure,
    CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨⟨hxT, hxC⟩, hx2⟩, rfl⟩
    refine ⟨⟨hxT, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, ?_⟩
    · exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hxC ⟨h, hTM hh⟩ (Subgroup.mem_subgroupOf.mpr hh))
    · simpa using congrArg Subtype.val hx2
  · rintro ⟨⟨hyT, hyC⟩, hy2⟩
    refine ⟨⟨y, hTM hyT⟩, ⟨⟨hyT, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, ?_⟩, rfl⟩
    · exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC h hh)
    · exact Subtype.ext (by simpa using hy2)

theorem omegaOneCenterOf_subgroupOf {M T : Subgroup G} (hTM : T ≤ M) :
    CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) =
      (CFSG.Quasithin.omegaOneCenterOf T).subgroupOf M := by
  rw [← map_omegaOneCenterOf_subgroupOf hTM]
  exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm

theorem uCore_eq_iSup_omegaOneCenterOf (M T : Subgroup G) :
    uCore M T =
      ⨆ m : M, (CFSG.Quasithin.omegaOneCenterOf T).map (MulAut.conj (m : G)).toMonoidHom := by
  rw [uCore, omegaOneCenterIn_eq_quasithinOmegaOneCenter, CFSG.Quasithin.omegaOneCenterOf_eq]

theorem uCore_le_of_le {M T : Subgroup G} (hTM : T ≤ M) : uCore M T ≤ M := by
  rw [uCore_eq_iSup_omegaOneCenterOf]
  refine iSup_le fun m => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact M.mul_mem (M.mul_mem m.2 (hTM (omegaOneCenterOf_le_subgroup T hz))) (M.inv_mem m.2)

theorem omegaOneCenterOf_le_uCore (M T : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf T ≤ uCore M T := by
  rw [uCore_eq_iSup_omegaOneCenterOf]
  refine le_iSup_of_le (1 : M) ?_
  intro z hz
  exact Subgroup.mem_map.mpr ⟨z, hz, by simp⟩

theorem map_gnV_eq_uCore {M T : Subgroup G} (hTM : T ≤ M) :
    (gnV (T.subgroupOf M)).map M.subtype = uCore M T := by
  change (Subgroup.normalClosure (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Set ↥M)).map
    M.subtype = uCore M T
  apply le_antisymm
  · have hUM : uCore M T ≤ M := uCore_le_of_le hTM
    haveI : ((uCore M T).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mpr (le_normalizer_uCore M T)
    have hle : Subgroup.normalClosure (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Set ↥M) ≤
        (uCore M T).subgroupOf M := by
      refine Subgroup.normalClosure_le_normal fun z hz => ?_
      have hzT : (z : G) ∈ CFSG.Quasithin.omegaOneCenterOf T := by
        rw [← map_omegaOneCenterOf_subgroupOf hTM]
        exact Subgroup.mem_map_of_mem M.subtype hz
      exact SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr (omegaOneCenterOf_le_uCore M T hzT))
    exact Subgroup.map_le_iff_le_comap.mpr hle
  · rw [uCore_eq_iSup_omegaOneCenterOf]
    refine iSup_le fun m => ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_omegaOneCenterOf_subgroupOf hTM] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hmem : m * z' * m⁻¹ ∈
        Subgroup.normalClosure (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) : Set ↥M) :=
      Subgroup.normalClosure_normal.conj_mem z'
        (Subgroup.subset_normalClosure (SetLike.mem_coe.mpr hz')) m
    exact Subgroup.mem_map_of_mem M.subtype hmem

theorem gnV_subgroupOf_eq {M T : Subgroup G} (hTM : T ≤ M) :
    gnV (T.subgroupOf M) = (uCore M T).subgroupOf M := by
  calc gnV (T.subgroupOf M)
      = Subgroup.comap M.subtype (Subgroup.map M.subtype (gnV (T.subgroupOf M))) :=
        (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm
    _ = Subgroup.comap M.subtype (uCore M T) := by rw [map_gnV_eq_uCore hTM]
    _ = (uCore M T).subgroupOf M := rfl

theorem gnC_subgroupOf_eq {M T : Subgroup G} (hTM : T ≤ M) :
    gnC (T.subgroupOf M) = (Subgroup.centralizer (uCore M T : Set G)).subgroupOf M := by
  change Subgroup.centralizer ((gnV (T.subgroupOf M) : Subgroup ↥M) : Set ↥M) = _
  rw [gnV_subgroupOf_eq hTM]
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx g hg
    have hgM : g ∈ M := uCore_le_of_le hTM hg
    exact congrArg Subtype.val (hx ⟨g, hgM⟩ (Subgroup.mem_subgroupOf.mpr hg))
  · intro hx h hh
    exact Subtype.ext (hx (h : G) (Subgroup.mem_subgroupOf.mp hh))

end CFSG.LocalAnalysis.RankThreeUC.S15
