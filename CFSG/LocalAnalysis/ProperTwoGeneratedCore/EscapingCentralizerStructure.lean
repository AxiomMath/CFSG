module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem elementary_subgroup_le_involution_centralizer
    (E : Subgroup G) (hE : IsElemAbelian 2 E) (t : G) (htE : t ∈ E) :
    E ≤ Subgroup.centralizer ({t} : Set G) := by
  intro x hx
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (@mul_comm' E _ hE.1 ⟨x, hx⟩ ⟨t, htE⟩)

theorem perfect_involution_centralizer_rank_three [Group.IsPerfect G]
    (hrank : 3 ≤ twoRank G) (t : G) (ht : orderOf t = 2) :
    3 ≤ twoRank (Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨E, hE, hcard, htE⟩ := perfect_involution_rank_three_coverage hrank t ht
  rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
  apply le_csSup (pRank_set_bddAbove 2 (by decide) _)
  exact ⟨E, elementary_subgroup_le_involution_centralizer E hE t htE, hE,
    by simpa using hcard⟩

theorem subgroup_image_two_rank_eq (M : Subgroup G) (U : Subgroup M) :
    Open.pRank 2 (U.map M.subtype) = Open.pRank 2 U := by
  calc
    _ = twoRank (U.map M.subtype) := pRank_subgroup_eq_internal_top 2 (by decide) _
    _ = twoRank U := (pRank_top_eq_of_equiv 2 (by decide)
      (U.equivMapOfInjective M.subtype M.subtype_injective)).symm
    _ = Open.pRank 2 U := (pRank_subgroup_eq_internal_top 2 (by decide) U).symm

theorem centralizer_full_core_le_overgroup
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (M : Subgroup G) (U : Sylow 2 M)
    (hUH : (U : Subgroup M).map M.subtype ≤ H) :
    properTwoGenCoreGamma (U : Subgroup M) 2 ≤ H.subgroupOf M := by
  apply (gamma_le_iff _ _ 2).mpr
  intro Q hQU hQrank x hx
  have hQH : Q.map M.subtype ≤ H := (Subgroup.map_mono hQU).trans hUH
  have hQambientRank : 2 ≤ Open.pRank 2 (Q.map M.subtype) := by
    rwa [subgroup_image_two_rank_eq]
  have hnormalizer := two_generated_core_subgroup_normalizer_le S H hSH hcore
    (Q.map M.subtype) hQH hQambientRank
  exact hnormalizer (Subgroup.le_normalizer_map M.subtype
    (Subgroup.mem_map_of_mem M.subtype hx))

theorem perfect_proper_core_escaping_centralizer_structure [Group.IsPerfect G]
    (hrank : 3 ≤ twoRank G) (S : Sylow 2 G) (H : Subgroup G)
    (hH : H ≠ ⊤) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (hescape : ¬ Subgroup.centralizer ({t} : Set G) ≤ H) :
    let M := Subgroup.centralizer ({t} : Set G)
    let D := H ⊓ M
    ∀ T : Sylow 2 D, ∃ U : Sylow 2 M,
      (U : Subgroup M).map M.subtype = (T : Subgroup D).map D.subtype ∧
      twoRank M = Open.pRank 2 ((T : Subgroup D).map D.subtype) ∧
      3 ≤ twoRank M ∧
      let R := pPrimeCore 2 M
      let pi := QuotientGroup.mk' R
      let Ubar := U.mapSurjective (QuotientGroup.mk'_surjective R)
      let J := properTwoGenCoreGamma (U : Subgroup M) 2
      let Jbar := properTwoGenCoreGamma (Ubar : Subgroup (M ⧸ R)) 2
      let HM := H.subgroupOf M
      let Hbar := HM.map pi
      let tm : M := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      H < ⊤ ∧ R ≤ J ∧ J ≤ HM ∧ HM < ⊤ ∧ J.map pi = Jbar ∧
        Jbar ≤ Hbar ∧ Hbar < ⊤ ∧ (Ubar : Subgroup (M ⧸ R)) ≤ Hbar ∧
        twoRank (M ⧸ R) = twoRank M ∧ 3 ≤ twoRank (M ⧸ R) ∧
        pPrimeCore 2 (M ⧸ R) = ⊥ ∧
        pi tm ∈ Subgroup.center (M ⧸ R) ∧ orderOf (pi tm) = 2 ∧
        pi tm ∈ pCore 2 (M ⧸ R) ∧ Open.pRank 2 (pCore 2 (M ⧸ R)) = 1 ∧
        ¬ IsCharacteristicP 2 (M ⧸ R) ∧ layer (M ⧸ R) ≠ ⊥ := by
  classical
  let M := Subgroup.centralizer ({t} : Set G)
  let D := H ⊓ M
  dsimp only
  intro T
  obtain ⟨U, himage⟩ := (full_core_involution_centralizer_sylow S H hSH
    (by omega) hcore t htH ht).2 T
  have hUrankEq : Open.pRank 2 ((T : Subgroup D).map D.subtype) = twoRank M := by
    rw [← himage, subgroup_image_two_rank_eq, sylow_two_rank_eq]
  have hMrank : 3 ≤ twoRank M := perfect_involution_centralizer_rank_three hrank t ht
  have hUH : (U : Subgroup M).map M.subtype ≤ H := by
    rw [himage]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  let HM := H.subgroupOf M
  have hUHM : (U : Subgroup M) ≤ HM := by
    intro x hx
    exact hUH (Subgroup.mem_map_of_mem M.subtype hx)
  have hJHM : properTwoGenCoreGamma (U : Subgroup M) 2 ≤ HM :=
    centralizer_full_core_le_overgroup S H hSH hcore M U hUH
  have hHMproper : HM ≠ ⊤ := by
    intro htop
    apply hescape
    intro x hx
    have hmem : (⟨x, hx⟩ : M) ∈ HM := htop.symm ▸ Subgroup.mem_top _
    exact hmem
  have hJproper : properTwoGenCoreGamma (U : Subgroup M) 2 ≠ ⊤ := by
    intro htop
    exact hHMproper (top_le_iff.mp (htop ▸ hJHM))
  let tm : M := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have htmCenter : tm ∈ Subgroup.center M := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property
  have htmOrder : orderOf tm = 2 := (Subgroup.orderOf_coe tm).symm.trans ht
  let R := pPrimeCore 2 M
  let pi := QuotientGroup.mk' R
  let Ubar := U.mapSurjective (QuotientGroup.mk'_surjective R)
  let J := properTwoGenCoreGamma (U : Subgroup M) 2
  let Jbar := properTwoGenCoreGamma (Ubar : Subgroup (M ⧸ R)) 2
  let Hbar := HM.map pi
  obtain ⟨hRJ, hJimage, _, hquotRank, hquotRankThree, hOddCore,
      htbarCenter, htbarOrder, htbarCore, htwoCoreRank, hnotChar, hLayer⟩ :=
    central_involution_proper_core_local_structure hMrank tm htmCenter htmOrder U hJproper
  have hJbarHbar : Jbar ≤ Hbar := by
    change properTwoGenCoreGamma (Ubar : Subgroup (M ⧸ R)) 2 ≤ HM.map pi
    rw [← hJimage]
    exact Subgroup.map_mono hJHM
  have hHbarProper : Hbar ≠ ⊤ := by
    intro htop
    have hpreimage := congrArg (Subgroup.comap pi) htop
    have hkernel : pi.ker ≤ HM := by
      rw [QuotientGroup.ker_mk']
      exact hRJ.trans hJHM
    rw [Subgroup.comap_map_eq_self hkernel, Subgroup.comap_top] at hpreimage
    exact hHMproper hpreimage
  have hUbarHbar : (Ubar : Subgroup (M ⧸ R)) ≤ Hbar := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hUHM
  exact ⟨U, himage, hUrankEq.symm, hMrank, lt_top_iff_ne_top.mpr hH, hRJ, hJHM,
    lt_top_iff_ne_top.mpr hHMproper, hJimage, hJbarHbar,
    lt_top_iff_ne_top.mpr hHbarProper, hUbarHbar, hquotRank, hquotRankThree,
    hOddCore, htbarCenter, htbarOrder, htbarCore, htwoCoreRank, hnotChar, hLayer⟩

end CFSG.ProperTwoGeneratedCore
