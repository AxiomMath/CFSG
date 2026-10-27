module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import all CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
import CFSG.Adapters.WholeGroupLayer

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

private theorem cStarL_eq_aux {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    cStarL p H = Subgroup.centralizer (starImg p H (pLayerIn p H) : Set (StarGroup p H)) :=
  rfl

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem cStarL_eq (p : ℕ) (H : Subgroup G) :
    cStarL p H = centralizer (starImg p H (pLayerIn p H) : Set (StarGroup p H)) :=
  cStarL_eq_aux p H

theorem starImg_pLayerIn (hp : p.Prime) (H : Subgroup G) :
    starImg p H (pLayerIn p H) = CFSG.layer (StarGroup p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmain : starImg p H (pLayerIn p H) =
      (CFSG.pLayer ↥H p).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    have hsub : ((CFSG.pLayer ↥H p).map H.subtype).subgroupOf H = CFSG.pLayer ↥H p :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective (CFSG.pLayer ↥H p)
    unfold starImg pLayerIn
    rw [hsub]
  rw [hmain]
  exact CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient

theorem cStarL_eq_centralizer_layer (hp : p.Prime) (H : Subgroup G) :
    cStarL p H = centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) := by
  rw [cStarL_eq p H, starImg_pLayerIn hp]

theorem pLayerIn_eq_bot_iff (hp : p.Prime) (H : Subgroup G) :
    pLayerIn p H = ⊥ ↔ CFSG.layer (StarGroup p H) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    rw [← starImg_pLayerIn hp, h]
    simp [starImg]
  · intro h
    have hlayer : CFSG.layer (↥H ⧸ CFSG.pPrimeCore p ↥H) = ⊥ := h
    have hmapbot : (CFSG.pPrimeCore p ↥H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hple : CFSG.pLayer ↥H p ≤ CFSG.pPrimeCore p ↥H := by
      have h1 := CFSG.ComponentClassification.LBalance.Quot.comap_layer_quotient_eq
        (H := ↥H) (p := p)
      rw [hlayer] at h1
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h1
      exact sup_eq_right.mp h1.symm
    have hempty : {L : Subgroup ↥H | CFSG.IsPComponent p L} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun L hL => ?_
      have hLle : L ≤ CFSG.pPrimeCore p ↥H := (le_sSup hL).trans hple
      obtain ⟨K, hK, -, hLK, -⟩ := hL
      have hKbot : K = ⊥ := by
        have hle : K ≤ (⊥ : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
          rw [← hLK]
          exact (Subgroup.map_mono hLle).trans (le_of_eq hmapbot)
        exact le_bot_iff.mp hle
      exact (Subgroup.nontrivial_iff_ne_bot K |>.mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hK.1)) hKbot
    have hbot : CFSG.pLayer ↥H p = ⊥ := by
      change sSup {L : Subgroup ↥H | CFSG.IsPComponent p L} = ⊥
      rw [hempty, sSup_empty]
    unfold pLayerIn
    rw [hbot, Subgroup.map_bot]

theorem isComponent_starImg {J : Subgroup G} (hJ : IsPComponentIn p J H) :
    CFSG.IsComponent (starImg p H J) := by
  obtain ⟨K, hK, -, hJK, -⟩ := hJ.2
  rw [show starImg p H J = K from hJK]
  exact hK

theorem exists_isPComponentIn_starImg_eq (hp : p.Prime) {C : Subgroup (StarGroup p H)}
    (hC : CFSG.IsComponent C) : ∃ J : Subgroup G, IsPComponentIn p J H ∧ starImg p H J = C := by
  haveI : Fact p.Prime := ⟨hp⟩
  let L₀ := CFSG.ComponentClassification.CatalogueBPrimeJoin.canonicalPrimeLift (X := ↥H) p C
  have hP := (CFSG.ComponentClassification.CatalogueBPrimeJoin.canonical_prime_component_lift
    (X := ↥H) p).1 C hC
  have hL : CFSG.IsPComponent p L₀ := hP.1
  have hLC : L₀.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) = C := hP.2.1
  refine ⟨L₀.map H.subtype, ⟨Subgroup.map_subtype_le L₀, ?_⟩, ?_⟩
  · have hsub : (L₀.map H.subtype).subgroupOf H = L₀ :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L₀
    rw [hsub]
    exact hL
  · have hstar : starImg p H (L₀.map H.subtype) =
        L₀.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
      have hsub : (L₀.map H.subtype).subgroupOf H = L₀ :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective L₀
      unfold starImg
      rw [hsub]
    rw [hstar]
    exact hLC

theorem eq_of_starImg_eq (hp : p.Prime) {J J' : Subgroup G} (hJ : IsPComponentIn p J H)
    (hJ' : IsPComponentIn p J' H) (h : starImg p H J = starImg p H J') : J = J' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmap : (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) =
      (J'.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := h
  have hsub := CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq
    hJ.2 hJ'.2 hmap
  calc J = (J.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hJ.1).symm
    _ = (J'.subgroupOf H).map H.subtype := by rw [hsub]
    _ = J' := Subgroup.map_subgroupOf_eq_of_le hJ'.1

private theorem relPPrimeCore_eq_map' (hp : p.Prime) (C : Subgroup G) :
    relPPrimeCore p C = (primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype
          ((primeComplementCore (G := ↥C) p).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

theorem pCore_le_centralizer_layer (hp : p.Prime) (H : Subgroup G) :
    CFSG.pCore p (StarGroup p H) ≤
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent (CFSG.pCore p (StarGroup p H)) :=
    (CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)).isNilpotent
  have hsub : (CFSG.pCore p (StarGroup p H)).IsSubnormal :=
    (CFSG.pCore_normal (p := p) (G := StarGroup p H)).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer
    (G := StarGroup p H) inferInstance hsub).2
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem centralizer_pCore_sup_layer_le (hp : p.Prime) (H : Subgroup G) :
    centralizer ((CFSG.pCore p (StarGroup p H) ⊔ CFSG.layer (StarGroup p H) :
        Subgroup (StarGroup p H)) : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  have hgf : CFSG.generalizedFitting (StarGroup p H) =
      CFSG.pCore p (StarGroup p H) ⊔ CFSG.layer (StarGroup p H) := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore (StarGroup p H) p hO]
  rw [← hgf, ← CFSG.Fitting_eq_pcore (StarGroup p H) p hO]
  exact CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup (G := StarGroup p H)

theorem layer_inf_centralizer_le_pCore (hp : p.Prime) (H : Subgroup G) :
    CFSG.layer (StarGroup p H) ⊓
        centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  haveI hchar : (CFSG.layer (StarGroup p H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  haveI hnorm : (CFSG.layer (StarGroup p H)).Normal := inferInstance
  haveI hZcomm : IsMulCommutative
      ↥(CFSG.layer (StarGroup p H) ⊓
        centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hZnil : Group.IsNilpotent
      ↥(CFSG.layer (StarGroup p H) ⊓
        centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))) := inferInstance
  have hZnorm : (CFSG.layer (StarGroup p H) ⊓
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))).Normal := inferInstance
  have hle : CFSG.layer (StarGroup p H) ⊓
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤
      CFSG.fittingSubgroup (StarGroup p H) := by
    change CFSG.layer (StarGroup p H) ⊓
        centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤
      sSup {N : Subgroup (StarGroup p H) | N.Normal ∧ Group.IsNilpotent N}
    exact le_sSup ⟨hZnorm, hZnil⟩
  rwa [CFSG.Fitting_eq_pcore (StarGroup p H) p hO] at hle

theorem centralizer_pCore_le_of_layer_eq_bot (hp : p.Prime) (H : Subgroup G)
    (hL : CFSG.layer (StarGroup p H) = ⊥) :
    centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := by
  have h := centralizer_pCore_sup_layer_le hp H
  rwa [hL, sup_bot_eq] at h

theorem pCore_le_cStarL (hp : p.Prime) (H : Subgroup G) :
    CFSG.pCore p (StarGroup p H) ≤ cStarL p H := by
  rw [cStarL_eq_centralizer_layer hp]
  exact pCore_le_centralizer_layer hp H

theorem cStarL_inf_centralizer_le_pCore (hp : p.Prime) (H : Subgroup G) :
    cStarL p H ⊓ centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H)) ≤
      CFSG.pCore p (StarGroup p H) := by
  rw [cStarL_eq_centralizer_layer hp]
  refine le_trans ?_ (centralizer_pCore_sup_layer_le hp H)
  rw [Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · exact Subgroup.le_centralizer_iff.mp inf_le_right
  · exact Subgroup.le_centralizer_iff.mp inf_le_left

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
