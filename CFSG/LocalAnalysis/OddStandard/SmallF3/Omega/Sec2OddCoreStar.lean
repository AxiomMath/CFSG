module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem oddCore_centralizer_of_mem_center {G : Type*} [Group G] (hG : oddCore G = ⊥) {z : G}
    (hz : z ∈ Subgroup.center G) : oddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have htop : Subgroup.centralizer ({z} : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hz)
  rw [htop]
  exact oddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm hG

theorem oddCore_centralizer_oGroup_involution_eq_bot {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    oddCore ↥(Subgroup.centralizer ({s} : Set (OGroup Q))) = ⊥ := by
  by_cases hs1 : s = 1
  · exact oddCore_centralizer_of_mem_center (oddCore_oGroup_eq_bot hQ)
      (hs1 ▸ Subgroup.one_mem _)
  by_cases hsπ : s = piOrth Q
  · exact oddCore_centralizer_of_mem_center (oddCore_oGroup_eq_bot hQ)
      (hsπ ▸ piOrth_mem_center)
  exact oddCore_centralizer_involution_eq_bot hQ hs hs1 hsπ
    (fun _ _ _ _ _ hR _ => oddCore_oGroup_eq_bot hR)

theorem oddCore_centralizer_projOrth_eq_bot {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    {s : OGroup Q} (hs : s * s = 1) :
    oddCore ↥(Subgroup.centralizer ({toProj Q s} : Set (ProjOrth Q))) = ⊥ := by
  refine oddCore_centralizer_eq_bot_of_cover (toProj Q) (QuotientGroup.mk'_surjective _) ?_ ?_
    (oddCore_centralizer_oGroup_involution_eq_bot hQ hs)
  · intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    rcases mem_piGroup_iff.mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact piOrth_mem_center
  · rw [QuotientGroup.ker_mk']
    change Nat.card (Subgroup.zpowers (piOrth Q)) ∣ 2
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact piOrth_mul_self)

@[expose] def subgroupOfCentralizerEquiv {G : Type*} [Group G] (K : Subgroup G) {h : G}
    (hh : h ∈ K) :
    ↥(K.subgroupOf (Subgroup.centralizer ({h} : Set G))) ≃*
      ↥(Subgroup.centralizer ({⟨h, hh⟩} : Set K)) where
  toFun x := ⟨⟨((x : Subgroup.centralizer ({h} : Set G)) : G), Subgroup.mem_subgroupOf.mp x.2⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (x : Subgroup.centralizer ({h} : Set G)).2))⟩
  invFun y := ⟨⟨((y : K) : G), Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.2))⟩,
    Subgroup.mem_subgroupOf.mpr (y : K).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem oddCore_centralizer_subgroup_eq_bot {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    [K.Normal] {h : G} (hh : h ∈ K) (hC : oddCore ↥(Subgroup.centralizer ({h} : Set G)) = ⊥) :
    oddCore ↥(Subgroup.centralizer ({⟨h, hh⟩} : Set K)) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (subgroupOfCentralizerEquiv K hh)
    (oddCore_eq_bot_of_normal _ hC)

theorem oddCore_centralizer_omegaProj_eq_bot {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    {s : OGroup Q} (hs : s * s = 1) (hτ : toProj Q s ∈ omegaProj hQ) :
    oddCore ↥(Subgroup.centralizer ({⟨toProj Q s, hτ⟩} : Set ↥(omegaProj hQ))) = ⊥ :=
  oddCore_centralizer_subgroup_eq_bot (omegaProj hQ) hτ
    (oddCore_centralizer_projOrth_eq_bot hQ hs)

end CFSG.OddStandard.SmallF3.Omega
