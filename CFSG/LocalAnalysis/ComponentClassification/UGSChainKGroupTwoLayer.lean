module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceSwap
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {H : Type*} [Group H] [Finite H]

theorem map_twoComponent_centralizer_quotient {t : H} (ht : orderOf t = 2) {L : Subgroup H}
    (hLC : L ≤ centralizer ({t} : Set H))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H)))) :
    L.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) ∧
      IsPComponent 2 ((L.map (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
        (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set q := QuotientGroup.mk' (pPrimeCore 2 H) with hq
  set C := centralizer ({t} : Set H) with hC
  set Cb := centralizer ({q t} : Set (H ⧸ pPrimeCore 2 H)) with hCb
  have hCmap : C.map q = Cb := UnbalancedLayer.map_centralizer_eq hRodd htt
  let f : C →* Cb := (MulEquiv.subgroupCongr hCmap).toMonoidHom.comp (q.subgroupMap C)
  have hf : ∀ c : C, (f c : H ⧸ pPrimeCore 2 H) = q c := fun c => rfl
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr hCmap).surjective.comp (q.subgroupMap_surjective C)
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    have heq : f.ker = (q.domRestrict C).ker := by
      ext c
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      exact ⟨fun h => by rw [← hf, h]; rfl, fun h => Subtype.ext (by rw [hf]; exact h)⟩
    rw [heq]
    exact UnbalancingLocal.Correspondence.not_two_dvd_card_ker_restrict C
  have himage := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hfs
    hker).1.mapsTo hL
  have hLCb : L.map q ≤ Cb := hCmap ▸ map_mono hLC
  have hmap : (L.subgroupOf C).map f = (L.map q).subgroupOf Cb := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (hf c).symm⟩
    · rintro ⟨l, hl, hly⟩
      refine ⟨⟨l, hLC hl⟩, hl, Subtype.ext ?_⟩
      rw [hf]
      exact hly
  exact ⟨hLCb, hmap ▸ himage⟩

theorem outer_solvable_of_isKGroupCat {H : Type} [Group H] [Finite H]
    (hS : SchreierFor Blueprint.Catalog) (hK : SectionRank.IsKGroupCat H)
    (K : Subgroup (H ⧸ pPrimeCore 2 H)) (hKc : IsComponent K) :
    Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer (K ⧸ center K)) := by
  have hKbar : SectionRank.IsKGroupCat (H ⧸ pPrimeCore 2 H) := hK.quotient (pPrimeCore 2 H)
  have : IsSimpleGroup (K ⧸ center K) := hKc.1.2.1
  exact hS (K ⧸ center K) hKc.1.2.2 (hKbar K (center K) hKc.1.2.1)

theorem kGroup_involution_fixed_two_layer_containment_of_schreier {H : Type} [Group H] [Finite H]
    (hS : SchreierFor Blueprint.Catalog) (hK : SectionRank.IsKGroupCat H) {t : H}
    (ht : orderOf t = 2) :
    (∀ L : Subgroup H, L ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H))) → L ≤ pLayer H 2) ∧
    (pLayer (centralizer ({t} : Set H)) 2).map (centralizer ({t} : Set H)).subtype ≤
      pLayer H 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmain : ∀ L : Subgroup H, L ≤ centralizer ({t} : Set H) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set H))) → L ≤ pLayer H 2 := by
    intro L hLC hL
    obtain ⟨hLCb, hLq⟩ := map_twoComponent_centralizer_quotient ht hLC hL
    have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hlayer := (UnbalancedLayer.odd_core_free_schreier_fixed_two_layer_containment
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (UnbalancedLayer.orderOf_mk_eq_two hRodd ht)
      (outer_solvable_of_isKGroupCat hS hK)).1 _ hLCb hLq
    have hLperf : Group.IsPerfect L := by
      have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hL
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLC).toMonoidHom)
        (subgroupOfEquivOfLe hLC).surjective
    have hR : Group.IsSolvable (pPrimeCore 2 H) := Milestones.odd_order_solvable hRodd
    exact CatalogueBPrimeJoin.solvable_prime_complement_core_perfect_layer_lift hR hLperf hlayer
  refine ⟨hmain, ?_⟩
  rw [map_le_iff_le_comap]
  refine sSup_le fun L' hL' => ?_
  rw [← map_le_iff_le_comap]
  have hL'eq : (L'.map (centralizer ({t} : Set H)).subtype).subgroupOf
      (centralizer ({t} : Set H)) = L' :=
    comap_map_eq_self_of_injective (centralizer ({t} : Set H)).subtype_injective L'
  exact hmain _ (map_subtype_le L') (by rw [hL'eq]; exact hL')

end CFSG.ComponentClassification.UGSChain
