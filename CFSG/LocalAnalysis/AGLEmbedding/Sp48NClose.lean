module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Data
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section OThree

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_pCorePreimage (p : ℕ) [Fact p.Prime] (M : Subgroup G) :
    Group.IsSolvable (pCorePreimage p M) := by
  set Y' := (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    with hY'
  have hQY : CFSG.pCore 2 ↥M ≤ Y' := by
    intro x hx
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Group.IsSolvable (CFSG.pCore 2 ↥M) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).isNilpotent
    infer_instance
  have hp : Group.IsSolvable (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have := (CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M)).isNilpotent
    infer_instance
  let f : CFSG.pCore 2 ↥M →* Y' := Subgroup.inclusion hQY
  let g : Y' →* CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp Y'.subtype).codRestrict _ (fun y => y.2)
  have hY'solv : Group.IsSolvable Y' := by
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro y hy
    have hy1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (y : ↥M) = 1 := congrArg Subtype.val hy
    exact ⟨⟨y, (QuotientGroup.eq_one_iff _).mp hy1⟩, rfl⟩
  have e : Y' ≃* (pCorePreimage p M : Subgroup G) := Y'.equivMapOfInjective M.subtype
    M.subtype_injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem D1Sp48NData.pCore_eq_bot {P : Sylow 3 G} {M H R X U A V : Subgroup G}
    (h : D1Sp48NData P M H R X U A V) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
  by_contra hO
  have h3 := h.surv.ph3
  have hYK := h3.pCorePreimage_le_inf h84 hD2
  have hYn : H ⊓ M ≤ Subgroup.normalizer (pCorePreimage 3 M : Set G) :=
    inf_le_right.trans (le_normalizer_pCorePreimage 3 M)
  obtain ⟨hVV, hVK, hVN, -, hdich, -⟩ := h.piece
  rcases hdich _ hYK hYn with h1 | h1
  · exact h3.pCorePreimage_not_le hO h1
  · apply hVN
    have hVH : V ≤ H := hVK.trans inf_le_left
    have hYH : pCorePreimage 3 M ≤ H := hYK.trans inf_le_left
    apply le_glbPrimeCore_of_map_eq_bot hVH
    set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
    set Yb := ((pCorePreimage 3 M).subgroupOf H).map π with hYb
    have hle : (V.subgroupOf H).map π ≤ Yb := by
      rw [sup_glbPrimeCore_eq_preimage hYH rfl] at h1
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwv⟩ := h1 (Subgroup.mem_subgroupOf.mp hv)
      have : w = v := Subtype.ext hwv
      rw [← this]
      exact hw
    have hYsolv : Group.IsSolvable Yb := by
      have : Group.IsSolvable ((pCorePreimage 3 M).subgroupOf H) := by
        have := isSolvable_pCorePreimage 3 M
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hYH).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hYH).injective
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    have hperf := map_perfect_subgroupOf (p := 3) hVH hVV
    by_contra hne
    have : Nontrivial ((V.subgroupOf H).map π) :=
      (Subgroup.bot_or_nontrivial _).resolve_left hne
    have : Group.IsPerfect ((V.subgroupOf H).map π) := Subgroup.isPerfect_iff.mpr hperf
    have : Group.IsSolvable ((V.subgroupOf H).map π) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable _ ‹_›

end OThree

end CFSG.AGLEmbedding
