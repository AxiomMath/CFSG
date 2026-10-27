module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

@[expose] def pCoreImage (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (pCore p ↥H).map H.subtype

theorem subgroupOf_pCoreImage (p : ℕ) (H : Subgroup G) :
    (pCoreImage p H).subgroupOf H = pCore p ↥H := by
  rw [pCoreImage]
  apply (Subgroup.map_subtype_inj (H := H)).mp
  rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]

instance instNormalSubgroupOfPCoreImage (p : ℕ) (H : Subgroup G) :
    ((pCoreImage p H).subgroupOf H).Normal := by
  rw [subgroupOf_pCoreImage]
  infer_instance

end CFSG.HardMathSupport.GuralnickMalle
