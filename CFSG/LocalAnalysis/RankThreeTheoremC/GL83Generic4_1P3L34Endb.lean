module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1End2
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34end_pRank_le (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {U : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hUS : U ≤ normalizer (S : Set G)) (hesc : ¬ normalizer (S : Set G) ≤ M) :
    Open.pRank 3 (normalizer (S : Set G)) ≤ 2 := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hU2 : 2 ≤ Open.pRank 3 U := le_pRank_of_elemAbelian_card le_rfl hU hUc
  have hH2 : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hSne, hS2, rfl⟩
  obtain ⟨F, hFH, -, hFM⟩ := exists_sylow_through3 hS hU0 hp hM hUp hU2 (hUP.trans hPM) hUS
  have hrkF : Open.pRank 3 F ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ Open.pRank 3 F := by omega
    exact hesc (le_of_three_le_pRank_inf hD1 hp hM hH2
      (h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3 (le_inf hFH.le hFM))))
  exact (pRank_eq_of_isSylowOf3 hp3 hFH) ▸ hrkF

theorem l34end_isMulCommutative_sylow {p : ℕ} [Fact p.Prime] {N F : Subgroup G}
    (hF : IsSylowOf p F N) (hFab : IsMulCommutative F) (T : Sylow p N) :
    IsMulCommutative (T : Subgroup N) := by
  obtain ⟨T₀, rfl⟩ := hF
  have hT₀ : IsMulCommutative (T₀ : Subgroup N) := by
    have := Subgroup.comap_injective_isMulCommutative (H := (T₀ : Subgroup N).map N.subtype)
      N.subtype_injective
    rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at this
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N T₀ T
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact Subgroup.map_isMulCommutative _ _

theorem l34end_isMulCommutative_sylow_quotient {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    (h : ∀ T : Sylow p N, IsMulCommutative (T : Subgroup N))
    (S : Sylow p (N ⧸ primeComplementCore (G := N) p)) :
    IsMulCommutative (S : Subgroup (N ⧸ primeComplementCore (G := N) p)) := by
  obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (primeComplementCore (G := N) p)) p S
  have := h T
  rw [Sylow.coe_mapSurjective]
  infer_instance

theorem l34end_hyp (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} {U H F : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hHtop : H ≠ ⊤) (hUH : U ≤ H) (hrk : Open.pRank 3 H ≤ 2)
    (hHab : ∀ T : Sylow 3 H, IsMulCommutative (T : Subgroup H)) (hFH : IsSylowOf 3 F H)
    (hUF : U ≤ F) (hFM : F ≤ M) :
    Gen49BHyp 3 ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      ((U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hUH hxU⟩) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hxH : x ∈ H := hUH hxU
  set O : Subgroup H := primeComplementCore (G := H) 3 with hO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hx3 : x ^ 3 = 1 := hU.2 x hxU
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = 3 :=
    orderOf_mk_of_coprime hp3 O (primeComplementCore_coprime 3) hxo
  have hab : ∀ S : Sylow 3 (H ⧸ O), IsMulCommutative (S : Subgroup (H ⧸ O)) :=
    l34end_isMulCommutative_sylow_quotient hHab
  have hF2 : 2 ≤ Open.pRank 3 F := le_pRank_of_elemAbelian_card hUF hU hUc
  have hN₁ : normalizer (F : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hFH.isPGroup hFM hF2
  have hN₂ : normalizer (U : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hUp (hUP.trans hPM)
      (le_pRank_of_elemAbelian_card le_rfl hU hUc)
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 (H ⧸ O), (Q : Subgroup (H ⧸ O)) =
      (F.subgroupOf H).map (QuotientGroup.mk' O) := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hFH)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  have hxS : QuotientGroup.mk' O ⟨x, hxH⟩ ∈ (F.subgroupOf H).map (QuotientGroup.mk' O) :=
    ⟨⟨x, hxH⟩, hUF hxU, rfl⟩
  exact
    { ne_two := by norm_num
      core_eq_bot := primeComplementCore_quotient_eq_bot 3
      catalog := (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hFH
      abelian := by
        rw [← hQ]
        exact hab Q
      le_sylow := Subgroup.map_mono (Subgroup.subgroupOf_mono H hUF)
      elemAbelian := gen49q_isElemAbelian_map _ (isElemAbelian_subgroupOf hU H)
      card_eq := by
        rw [card_map_mk_of_isPGroup hp3 O (primeComplementCore_coprime 3)
          (show IsPGroup 3 (U.subgroupOf H) from hUp.comap_subtype),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv]
        exact hUc
      pRank_le := gen49q_pRank_top_quotient_le hp3 hrk
      mem := ⟨⟨x, hxH⟩, hxU, rfl⟩
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo'
        omega
      weakClosed := fun g hg => weaklyClosed_map_mk hxo hab
        (fun Q' hxQ' g' hg' => weakClosed_sylow3 hwc Q' hxQ' g' hg') Q (hQ ▸ hxS) g
        (by rw [hQ]; exact hg)
      normalizer_S := normalizer_map_mk_le3 hp3
        (show IsPGroup 3 (F.subgroupOf H) from hFH.isPGroup.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hFH.le]; exact hN₁)
      normalizer_R := normalizer_map_mk_le3 hp3
        (show IsPGroup 3 (U.subgroupOf H) from hUp.comap_subtype)
        (by rw [Subgroup.map_subgroupOf_eq_of_le hUH]; exact hN₂)
      others := by
        rintro _ ⟨r, hr, rfl⟩ hr1 hrx
        have hrU : (r : G) ∈ U := hr
        have hr1' : (r : G) ≠ 1 := fun h => hr1 (by rw [show r = 1 from Subtype.ext h, map_one])
        have hrp : (r : G) ^ 3 = 1 := hU.2 _ hrU
        have hrx' : (r : G) ∉ zpowers x := by
          intro hmem
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
          have hrk' : r = (⟨x, hxH⟩ : H) ^ k := Subtype.ext (by rw [← hk]; rfl)
          have hmem' : QuotientGroup.mk' O r ∈ zpowers (QuotientGroup.mk' O ⟨x, hxH⟩) := by
            rw [hrk', map_zpow]
            exact zpow_mem (mem_zpowers _) k
          exact hrx (zpowers_eq_of_mem_zpowers_of_orderOf_eq_three3 hxo' hmem' hr1)
        have hCM : centralizer ({(r : G)} : Set G) ≤ M := hC _ hrU hrx'
        have := hU.1
        have hUC : U ≤ (P : Subgroup G) ⊓ centralizer ({(r : G)} : Set G) := fun g hg =>
          ⟨hUP hg, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := U)).comm ⟨g, hg⟩ ⟨r, hrU⟩))⟩
        have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
          normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
            (le_pRank_of_elemAbelian_card hUC hU hUc) hCM
        have hro : orderOf r = 3 := by
          rw [← Subgroup.orderOf_coe]
          exact orderOf_eq_prime hrp hr1'
        refine ⟨(centralizer_mk_le_map hp3 hro).trans (Subgroup.map_mono fun c hc => ?_), ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩
        · rw [← MonoidHom.map_zpowers]
          refine normalizer_map_mk_le3 hp3 (D := zpowers r)
            (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])) ?_
          rw [MonoidHom.map_zpowers]
          exact hNM }

end CFSG.LocalAnalysis.RankThreeTheoremC
