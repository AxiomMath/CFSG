module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseTwoCentralizer
public import CFSG.Monster.Existence.TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Visible
  CFSG.Monster.Griess

theorem gmat_mem_cent_xGmat_iff {g : Gmat} :
    g ∈ cent xGmat ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Hmat := by
  rw [← Gmat_inf_centralizer_xmat, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h

theorem gmat_mem_zpowers_xGmat_iff {g : Gmat} :
    g ∈ Subgroup.zpowers xGmat ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Subgroup.zpowers xmat := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

theorem gmat_orderOf_xGmat : orderOf xGmat = 2 :=
  (Subgroup.orderOf_coe xGmat).symm.trans orderOf_xmat

theorem gmat_Qmat_le_Gmat : Qmat ≤ Gmat :=
  Qmat_le_Hmat.trans Hmat_le_Gmat

theorem gmat_Qmat_le_cent : Qmat.subgroupOf Gmat ≤ cent xGmat := fun _ hg =>
  gmat_mem_cent_xGmat_iff.2 (Qmat_le_Hmat (Subgroup.mem_subgroupOf.1 hg))

theorem gmat_rhoQvis_normal : rhoQvis.Normal := by
  rw [← pCore_Gvis]
  infer_instance

theorem gmat_Qmat_normal : ((Qmat.subgroupOf Gmat).subgroupOf (cent xGmat)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  have hgH := gmat_mem_cent_xGmat_iff.1 g.2
  have hnH := gmat_mem_cent_xGmat_iff.1 n.2
  have h := gmat_rhoQvis_normal.conj_mem ⟨_, hnH⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨_, hgH⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem gmat_isExtraspecial_Qmat : IsExtraspecialPGroup 2 (Qmat.subgroupOf Gmat) :=
  IsExtraspecialPGroup.of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe Qmat_le_Hmat).trans
      (Subgroup.subgroupOfEquivOfLe gmat_Qmat_le_Gmat).symm)
    isExtraspecialPGroup_rhoQvis

theorem gmat_center_Qmat :
    (Subgroup.center (Qmat.subgroupOf Gmat)).map (Qmat.subgroupOf Gmat).subtype =
      Subgroup.zpowers xGmat := by
  ext g
  rw [Subgroup.mem_map, gmat_mem_zpowers_xGmat_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine (center_Qmat _ (Subgroup.mem_subgroupOf.1 q.2)).1 fun r hr => ?_
    have h := Subgroup.mem_center_iff.1 hq ⟨⟨r, gmat_Qmat_le_Gmat hr⟩, Subgroup.mem_subgroupOf.2 hr⟩
    exact congrArg (fun z : Qmat.subgroupOf Gmat => ((z : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)) h
  · intro hg
    have hgQ : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Qmat :=
      (Subgroup.zpowers_le.2 xmat_mem_Qmat) hg
    refine ⟨⟨g, Subgroup.mem_subgroupOf.2 hgQ⟩, Subgroup.mem_center_iff.2 fun r => ?_, rfl⟩
    exact Subtype.ext (Subtype.ext ((center_Qmat _ hgQ).2 hg _ (Subgroup.mem_subgroupOf.1 r.2)))

theorem gmat_cent_inf_centralizer_Qmat :
    cent xGmat ⊓ Subgroup.centralizer (Qmat.subgroupOf Gmat : Set Gmat) =
      Subgroup.zpowers xGmat := by
  ext g
  rw [Subgroup.mem_inf, gmat_mem_zpowers_xGmat_iff, ← Gmat_inf_centralizer_Qmat, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨g.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    have h := Subgroup.mem_centralizer_iff.1 hc ⟨r, gmat_Qmat_le_Gmat hr⟩
      (Subgroup.mem_subgroupOf.2 hr)
    exact congrArg Subtype.val h
  · rintro ⟨-, hc⟩
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun r hr => Subtype.ext ?_⟩
    · rw [cent, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc xmat xmat_mem_Qmat).symm
    · exact Subgroup.mem_centralizer_iff.1 hc _ (Subgroup.mem_subgroupOf.1 hr)

theorem gmat_action_kernel : ∀ h ∈ cent xGmat,
    (∀ q ∈ Qmat.subgroupOf Gmat, h * q * h⁻¹ * q⁻¹ ∈ Subgroup.zpowers xGmat) ↔
      h ∈ Qmat.subgroupOf Gmat := by
  intro h hh
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hc
    refine faithful_Hmat _ (gmat_mem_cent_xGmat_iff.1 hh) fun q hq => ?_
    exact gmat_mem_zpowers_xGmat_iff.1
      (hc ⟨q, gmat_Qmat_le_Gmat hq⟩ (Subgroup.mem_subgroupOf.2 hq))
  · intro hQ q hq
    exact gmat_mem_zpowers_xGmat_iff.2 (comm_Qmat _ hQ _ (Subgroup.mem_subgroupOf.1 hq))

@[expose] noncomputable def gmatTau : Gmat := ⟨tauB, tauB_mem_Gmat⟩

theorem gmat_conj_xGmat_mem : gmatTau * xGmat * gmatTau⁻¹ ∈ Qmat.subgroupOf Gmat :=
  Subgroup.mem_subgroupOf.2 generated_group_Co1_local_recognition_hypotheses.2.2.2.2.2.2.2.2.2.2.2.1

theorem gmat_conj_xGmat_not_mem : gmatTau * xGmat * gmatTau⁻¹ ∉ Subgroup.zpowers xGmat :=
  fun h => generated_group_Co1_local_recognition_hypotheses.2.2.2.2.2.2.2.2.2.2.2.2
    (gmat_mem_zpowers_xGmat_iff.1 h)

theorem gmat_closure_cent_tau :
    Subgroup.closure ((cent xGmat : Set Gmat) ∪ {gmatTau}) = ⊤ := by
  apply Subgroup.map_injective Gmat.subtype_injective
  rw [MonoidHom.map_closure, Set.image_union, Set.image_singleton, ← Subgroup.coe_map,
    map_cent_xGmat, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

@[expose] noncomputable def gmatOddCocode : Gmat :=
  ⟨rhoEquiv (SpinLattice.DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))),
    Hmat_le_Gmat odd_cocode_inverts_triality.2.2.1⟩

theorem gmatOddCocode_mem_cent : gmatOddCocode ∈ cent xGmat :=
  gmat_mem_cent_xGmat_iff.2 odd_cocode_inverts_triality.2.2.1

theorem gmatOddCocode_relation :
    gmatOddCocode * (gmatTau * gmatOddCocode * gmatTau⁻¹) = gmatTau :=
  Subtype.ext odd_cocode_inverts_triality.2.2.2.1

theorem gmat_automorphisms_inner
    (hautH : ∀ β : MulAut Hmat, ∃ h : Hmat, β = MulAut.conj h) :
    ∀ α : MulAut Gmat, ∃ g : Gmat, α = MulAut.conj g :=
  global_inner_of_centralizer gmat_orderOf_xGmat gmat_Qmat_le_cent gmat_Qmat_normal
    gmat_isExtraspecial_Qmat gmat_center_Qmat gmat_cent_inf_centralizer_Qmat gmat_action_kernel
    (inner_of_equiv centGmatEquiv hautH) gmat_conj_xGmat_mem gmat_conj_xGmat_not_mem
    gmat_closure_cent_tau gmatOddCocode_mem_cent gmatOddCocode_relation

end CFSG.ComponentClassification.BMCase
