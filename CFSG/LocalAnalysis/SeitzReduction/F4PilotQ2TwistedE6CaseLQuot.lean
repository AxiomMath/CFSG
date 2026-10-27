module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Transfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial (index_center_eq_of_mulEquiv index_center_lt_of_lt)

section Index

theorem index_center_map_eq_of_ker_le_center {H Q : Type*} [Group H] [Group Q] (f : H →* Q)
    (hf : f.ker ≤ center H) {S : Subgroup H} (hS : ⁅S, S⁆ = S) :
    (center (S.map f)).index = (center S).index := by
  have : Group.IsPerfect S := Subgroup.isPerfect_iff.2 hS
  have hker : (f.subgroupMap S).ker ≤ center S := by
    intro x hx
    have hx' : (x : H) ∈ center H := by
      apply hf
      rw [MonoidHom.mem_ker]
      have h1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
      exact h1
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_center_iff.1 hx') y)
  rw [← CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel (f.subgroupMap S)
    (f.subgroupMap_surjective S) hker,
    Subgroup.index_comap_of_surjective _ (f.subgroupMap_surjective S)]

theorem eq_of_le_of_index_center_le_of_perfect {G : Type*} [Group G] [Finite G]
    {R N : Subgroup G} (hRN : R ≤ N) (hN : ⁅N, N⁆ = N)
    (h : (center N).index ≤ (center R).index) : R = N := by
  have : Group.IsPerfect N := Subgroup.isPerfect_iff.2 hN
  by_contra hne
  exact absurd h (not_le.2 (index_center_lt_of_lt (lt_of_le_of_ne hRN hne)))

end Index

section Quot

variable {M N : Type*} [Group M] [Group N] [Finite M] [Finite N]

theorem map_quotEquiv_perfectCore_centralizer (χ : M ⧸ center M ≃* N ⧸ center N)
    {A : Subgroup M} {B : Subgroup N}
    (h : (A.map (QuotientGroup.mk' (center M))).map χ.toMonoidHom =
      B.map (QuotientGroup.mk' (center N))) :
    ((perfectCore (centralizer (A : Set M))).map (QuotientGroup.mk' (center M))).map
        χ.toMonoidHom =
      (perfectCore (centralizer (B : Set N))).map (QuotientGroup.mk' (center N)) := by
  rw [map_perfectCore_centralizer_mk, map_perfectCore_centralizer_mk,
    CFSG.Quasithin.map_perfectCore, map_centralizer_mulEquiv, h]

theorem index_center_perfectCore_centralizer_eq (χ : M ⧸ center M ≃* N ⧸ center N)
    {A : Subgroup M} {B : Subgroup N}
    (h : (A.map (QuotientGroup.mk' (center M))).map χ.toMonoidHom =
      B.map (QuotientGroup.mk' (center N))) :
    (center (perfectCore (centralizer (A : Set M)))).index =
      (center (perfectCore (centralizer (B : Set N)))).index := by
  set PA := perfectCore (centralizer (A : Set M)) with hPA
  set PB := perfectCore (centralizer (B : Set N)) with hPB
  have h1 := map_quotEquiv_perfectCore_centralizer χ h
  rw [← hPA, ← hPB] at h1
  calc (center PA).index = (center (PA.map (QuotientGroup.mk' (center M)))).index :=
        (index_center_map_eq_of_ker_le_center _ (QuotientGroup.ker_mk' _).le
          (CFSG.Quasithin.perfectCore_perfect _)).symm
    _ = (center ((PA.map (QuotientGroup.mk' (center M))).map χ.toMonoidHom)).index :=
        index_center_eq_of_mulEquiv (Subgroup.equivMapOfInjective _ χ.toMonoidHom χ.injective)
    _ = (center (PB.map (QuotientGroup.mk' (center N)))).index := by rw [h1]
    _ = (center PB).index :=
        index_center_map_eq_of_ker_le_center _ (QuotientGroup.ker_mk' _).le
          (CFSG.Quasithin.perfectCore_perfect _)

end Quot

end CFSG.SeitzReduction.F4Pilot
