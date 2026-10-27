module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.PushingUpLit.BHS.CStar
public import CFSG.CGT.PushingUpLit.BHS.Defs

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem omegaOneCenterIn_eq (T : Subgroup G) : omegaOneCenterIn T = omegaOneCenterOf T := by
  unfold omegaOneCenterIn omegaOneCenterOf omegaOneOf omegaOne centerOf
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, h2⟩
    refine ⟨⟨z.2, fun y hy => ?_⟩, h2⟩
    exact congrArg Subtype.val (hz ⟨y, hy⟩)
  · rintro ⟨⟨hxT, hx⟩, h2⟩
    refine ⟨⟨⟨x, hxT⟩, fun y => ?_, rfl⟩, h2⟩
    exact Subtype.ext (hx y y.2)

theorem pCoreOf_top_eq (G : Type) [Group G] :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) = CFSG.pCore 2 G := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := G)).symm, Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem charTwo_top_of_isCharacteristicP (h : CFSG.IsCharacteristicP 2 G) :
    CharTwo (⊤ : Subgroup G) := by
  intro x hx
  rw [pCoreOf_top_eq] at hx ⊢
  exact h hx.2

theorem inSubgroup_elemThompsonCenterTorsion_eq [Finite G] (T : Subgroup G) :
    inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) T = omegaOneCenterOf (thompsonJ T) := by
  rw [← elemThompson_map_subtype_eq_thompsonJ T]
  set J : Subgroup ↥T := elemThompson ↥T 2 with hJ
  unfold omegaOneCenterOf omegaOneOf centerOf
  have hset : {x : G | x ∈ J.map T.subtype ⊓ Subgroup.centralizer (J.map T.subtype : Set G) ∧
      x ^ 2 = 1} = ((elemThompsonCenterTorsion ↥T 2).map T.subtype : Set G) := by
    ext x
    simp only [Set.mem_ofPred_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
      SetLike.mem_coe, Subgroup.coe_subtype]
    constructor
    · rintro ⟨⟨⟨j, hj, rfl⟩, hc⟩, h2⟩
      refine ⟨j, ⟨⟨⟨j, hj⟩, ?_, rfl⟩, ?_⟩, rfl⟩
      · refine Subgroup.mem_center_iff.mpr fun k => ?_
        obtain ⟨k, hk⟩ := k
        exact Subtype.ext (Subtype.ext (hc (k : G) ⟨k, hk, rfl⟩))
      · exact Subtype.ext (by simpa using h2)
    · rintro ⟨z, ⟨hzc, hz2⟩, rfl⟩
      obtain ⟨j, hj, hjz⟩ := hzc
      have hzJ : z ∈ J := by rw [← hjz]; exact j.2
      refine ⟨⟨⟨z, hzJ, rfl⟩, ?_⟩, ?_⟩
      · rintro _ ⟨k, hk, rfl⟩
        have := Subgroup.mem_center_iff.mp hj ⟨k, hk⟩
        have h' := congrArg Subtype.val (congrArg Subtype.val this)
        simpa [← hjz] using h'
      · exact congrArg Subtype.val hz2
  unfold inSubgroup
  rw [hset, Subgroup.closure_eq]

theorem pushingUpS_eq_baum [Finite G] (T : Subgroup G) : pushingUpS T = baum T := by
  unfold pushingUpS baum
  rw [inSubgroup_elemThompsonCenterTorsion_eq]

theorem characteristicCoreStar_eq_cStarIn [Finite G] (T : Subgroup G) :
    characteristicCoreStar T = cStarIn ⊤ T := by
  unfold characteristicCoreStar cStarIn cgsIn
  rw [omegaOneCenterIn_eq, pushingUpS_eq_baum, top_inf_eq]
  simp only [top_inf_eq]
  congr 1
  apply le_antisymm
  · exact iSup_le fun B => iSup_le fun hB =>
      le_iSup_of_le B (le_iSup_of_le hB.2.1 (le_iSup_of_le hB.1 (le_iSup_of_le hB.2.2 le_rfl)))
  · exact iSup_le fun B => iSup_le fun hBS => iSup_le fun hB0 => iSup_le fun hBc =>
      le_iSup_of_le B (le_iSup_of_le ⟨hB0, hBS, hBc⟩ le_rfl)

theorem isSylowOf_top [Finite G] (T : Sylow 2 G) : IsSylowOf 2 (T : Subgroup G) ⊤ := by
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index
