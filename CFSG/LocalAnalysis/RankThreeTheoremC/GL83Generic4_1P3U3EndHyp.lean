module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9CoverAux
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3end_weaklyClosed_map_mk {p : ℕ} [Fact p.Prime] {N F : Subgroup G}
    (hFN : IsSylowOf p F N) {a : N} (haF : (a : G) ∈ F) (hao : orderOf a = p)
    (hab : IsMulCommutative
      ((F.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))))
    (hweak : ∀ g : G, (zpowers (a : G)).map (MulAut.conj g).toMonoidHom ≤ F →
      (zpowers (a : G)).map (MulAut.conj g).toMonoidHom = zpowers (a : G))
    (g : N ⧸ primeComplementCore (G := N) p)
    (hg : (zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a)).map
      (MulAut.conj g).toMonoidHom ≤
        (F.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) :
    (zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a)).map
        (MulAut.conj g).toMonoidHom =
      zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a) := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) g
  set O := primeComplementCore (G := N) p with hO
  set Fb : Subgroup (N ⧸ O) := (F.subgroupOf N).map (QuotientGroup.mk' O) with hFb
  have hcQ : QuotientGroup.mk' O g₁ * QuotientGroup.mk' O a * (QuotientGroup.mk' O g₁)⁻¹ ∈ Fb :=
    hg ⟨_, mem_zpowers _, rfl⟩
  set K : Subgroup N := Fb.comap (QuotientGroup.mk' O) with hK
  have haQ : QuotientGroup.mk' O a ∈ Fb := ⟨a, haF, rfl⟩
  have haK : (a : G) ∈ K.map N.subtype := ⟨a, haQ, rfl⟩
  have ha'K : (g₁ : G) * a * (g₁ : G)⁻¹ ∈ K.map N.subtype :=
    ⟨g₁ * a * g₁⁻¹, by simpa only [hK, SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
      using hcQ, rfl⟩
  have hpa : IsPGroup p (zpowers (a : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hao, pow_one])
  have hpa' : IsPGroup p (zpowers ((g₁ : G) * a * (g₁ : G)⁻¹)) := by
    have := hpa.map (MulAut.conj (g₁ : G)).toMonoidHom
    rwa [MonoidHom.map_zpowers] at this
  have hFK : IsSylowOf p F (K.map N.subtype) := by
    obtain ⟨hFle, hFp, hFidx⟩ := isSylowOf_iff.1 hFN
    have hFK' : F ≤ K.map N.subtype := fun f hf =>
      ⟨⟨f, hFle hf⟩, ⟨⟨f, hFle hf⟩, hf, rfl⟩, rfl⟩
    refine isSylowOf_iff.2 ⟨hFK', hFp, fun hdvd => hFidx ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex F (K.map N.subtype) N hFK' (Subgroup.map_subtype_le K)]
    exact hdvd.mul_right _
  obtain ⟨T₂, hT₂⟩ := (hpa'.comap_subtype (K := K.map N.subtype)).exists_le_sylow
  set S₂ : Subgroup G := (T₂ : Subgroup (K.map N.subtype)).map (K.map N.subtype).subtype
  have hS₂ : IsSylowOf p S₂ (K.map N.subtype) := ⟨T₂, rfl⟩
  have h₂ : zpowers ((g₁ : G) * a * (g₁ : G)⁻¹) ≤ S₂ := fun y hy =>
    ⟨⟨y, zpowers_le.mpr ha'K hy⟩, hT₂ hy, rfl⟩
  obtain ⟨k, hkK, hk⟩ := hFK.exists_mem_conj hS₂
  have hk1 : k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k ∈ F := (hk _).mp (h₂ (mem_zpowers _))
  have hconj : (MulAut.conj (k⁻¹ * (g₁ : G))).toMonoidHom (a : G) =
      k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hw := hweak (k⁻¹ * g₁) (by
    rw [MonoidHom.map_zpowers, zpowers_le, hconj]
    exact hk1)
  have hmem : k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k ∈ zpowers (a : G) := by
    rw [← hconj, ← hw]
    exact Subgroup.mem_map_of_mem _ (mem_zpowers _)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem
  obtain ⟨kN, hkN, rfl⟩ := hkK
  have hmN : kN⁻¹ * (g₁ * a * g₁⁻¹) * kN = a ^ m := Subtype.ext (by simpa using hm.symm)
  have : IsMulCommutative Fb := hab
  have hkQ : QuotientGroup.mk' O kN ∈ Fb := hkN
  have hcomm := setLike_mul_comm hkQ hcQ
  have hcm : QuotientGroup.mk' O g₁ * QuotientGroup.mk' O a * (QuotientGroup.mk' O g₁)⁻¹ =
      QuotientGroup.mk' O a ^ m := by
    have h := congrArg (QuotientGroup.mk' O) hmN
    rwa [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, mul_assoc, ← hcomm,
      inv_mul_cancel_left] at h
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [MonoidHom.map_zpowers, zpowers_le]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcm]
    exact zpow_mem (mem_zpowers _) m
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem u3end_endgame3_hyp (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} {U H F : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hHtop : H ≠ ⊤) (hUH : U ≤ H) (hrk : Open.pRank 3 H ≤ 2) (hFH : IsSylowOf 3 F H)
    (hUF : U ≤ F) (hFM : F ≤ M) (hFab : IsMulCommutative F)
    (hwcF : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    Gen49BHyp 3 ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      ((U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hUH hxU⟩) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hxH : x ∈ H := hUH hxU
  set O : Subgroup H := primeComplementCore (G := H) 3 with hO
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hU
  have hx3 : x ^ 3 = 1 := hU.2 x hxU
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxH⟩) = 3 :=
    orderOf_mk_of_coprime hp3 O (primeComplementCore_coprime 3) hxo
  have hFb : IsMulCommutative ((F.subgroupOf H).map (QuotientGroup.mk' O)) := by
    have h1 : IsMulCommutative (F.subgroupOf H) :=
      Subgroup.comap_injective_isMulCommutative (H := F) H.subtype_injective
    infer_instance
  have hF2 : 2 ≤ Open.pRank 3 F := le_pRank_of_elemAbelian_card hUF hU hUc
  have hN₁ : normalizer (F : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hFH.isPGroup hFM hF2
  have hN₂ : normalizer (U : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hUp (hUP.trans hPM)
      (le_pRank_of_elemAbelian_card le_rfl hU hUc)
  exact
    { ne_two := by norm_num
      core_eq_bot := primeComplementCore_quotient_eq_bot 3
      catalog := (catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
      sylow := isSylowOf_top_map_mk hFH
      abelian := hFb
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
      weakClosed := fun g hg => u3end_weaklyClosed_map_mk hFH (hUF hxU) hxo hFb hwcF g hg
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
        have hUC : U ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (hU.1.is_comm.comm ⟨g, hg⟩ ⟨r, hrU⟩))
        have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
          normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
            (le_pRank_of_elemAbelian_card (le_inf hUP hUC) hU hUc) hCM
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
