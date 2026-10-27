module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem map_pCoreOf_subgroupOf (p : ℕ) {Y K : Subgroup G} (hYK : Y ≤ K) :
    (CFSG.Open.pCoreOf p (Y.subgroupOf K)).map K.subtype = CFSG.Open.pCoreOf p Y := by
  let φ : ↥(Y.subgroupOf K) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYK
  have hcomp : Y.subtype.comp φ.toMonoidHom = K.subtype.comp (Y.subgroupOf K).subtype := by
    ext y
    rfl
  unfold CFSG.Open.pCoreOf
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso]

theorem pCoreOf_subgroupOf (p : ℕ) {Y K : Subgroup G} (hYK : Y ≤ K) :
    CFSG.Open.pCoreOf p (Y.subgroupOf K) = (CFSG.Open.pCoreOf p Y).subgroupOf K := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [map_pCoreOf_subgroupOf p hYK]
  exact (Subgroup.map_subgroupOf_eq_of_le
    ((Subgroup.map_subtype_le (CFSG.pCore p Y)).trans hYK)).symm

theorem map_pCoreOf_mulEquiv {G' : Type*} [Group G'] (p : ℕ) (ψ : G ≃* G')
    (C : Subgroup G) :
    CFSG.Open.pCoreOf p (C.map ψ.toMonoidHom) =
      (CFSG.Open.pCoreOf p C).map ψ.toMonoidHom := by
  let φ : ↥C ≃* ↥(C.map ψ.toMonoidHom) := Subgroup.equivMapOfInjective C ψ.toMonoidHom ψ.injective
  have hcomp : (C.map ψ.toMonoidHom).subtype.comp φ.toMonoidHom =
      ψ.toMonoidHom.comp C.subtype := by
    ext c
    rfl
  unfold CFSG.Open.pCoreOf
  rw [Subgroup.map_map, ← CFSG.pCore_map_iso p φ, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem map_centralizer_eq_of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') (S : Set G) :
    (Subgroup.centralizer S).map e.toMonoidHom =
      Subgroup.centralizer (e.toMonoidHom '' S) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom) ?_
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  change e.symm y ∈ Subgroup.centralizer S
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hy' : e s * y = y * e s :=
    (Subgroup.mem_centralizer_iff.mp hy) (e s) ⟨s, hs, rfl⟩
  simpa using congrArg e.symm hy'

theorem centralizer_subgroupOf_singleton {K : Subgroup G} {x : G} (hx : x ∈ K) :
    (Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({⟨x, hx⟩} : Set ↥K) := by
  ext m
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem map_pCoreOf_inf_centralizer_mulEquiv {G' : Type*} [Group G'] {M : Subgroup G}
    (ψ : ↥M ≃* G') {x : G} (hx : x ∈ M) :
    ((CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({x} : Set G))).subgroupOf M).map
        ψ.toMonoidHom =
      CFSG.Open.pCoreOf 2
        (Subgroup.centralizer ({ψ ⟨x, hx⟩} : Set G')) := by
  rw [← pCoreOf_subgroupOf 2 (inf_le_left : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ M),
    Subgroup.inf_subgroupOf_left]
  have hcent : (Subgroup.centralizer ({x} : Set G)).subgroupOf M =
      Subgroup.centralizer ({⟨x, hx⟩} : Set ↥M) := by
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hcent, ← map_pCoreOf_mulEquiv 2 ψ, map_centralizer_eq_of_mulEquiv, Set.image_singleton]
  rfl

end CFSG.GroupTheory
