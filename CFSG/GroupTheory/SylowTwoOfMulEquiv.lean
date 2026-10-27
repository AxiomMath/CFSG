module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG

open CFSG.QuasithinUnique

variable {G H : Type*} [Group G] [Group H]

theorem exists_mulEquiv_map_subgroupOf_eq_of_isSylowTwoOf [Finite G] {L T : Subgroup G}
    {Y U : Subgroup H} (e : ↥L ≃* ↥Y) (hT : IsSylowTwoOf T L) (hU : IsSylowTwoOf U Y) :
    ∃ e' : ↥L ≃* ↥Y, (T.subgroupOf L).map (e' : ↥L →* ↥Y) = U.subgroupOf Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥Y := Finite.of_equiv _ e.toEquiv
  have hT' : IsPGroup 2 (T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hU' : IsPGroup 2 (U.subgroupOf Y) :=
    hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm
  have hsurj : Function.Surjective (e : ↥L →* ↥Y) := e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y
    ((hT'.toSylow hT.2.2).mapSurjective hsurj) (hU'.toSylow hU.2.2)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h := congrArg (fun P : Sylow 2 ↥Y => (P : Subgroup ↥Y)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe] at h
  rw [← h, MulEquiv.toMonoidHom_trans, ← Subgroup.map_map]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

end CFSG
