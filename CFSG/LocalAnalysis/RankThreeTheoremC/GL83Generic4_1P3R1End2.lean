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

theorem gen49_mem_of_pow_eq_one_three {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {S R Γ : Subgroup Y} {x : Y} (h : Gen49BHyp p S R Γ x) {s : Y} (hs : s ∈ S)
    (hsp : s ^ p = 1) : s ∈ R := by
  by_contra hsR
  have hprime : p.Prime := Fact.out
  have := h.abelian
  have hcomm : ∀ q ∈ R, q * s = s * q := fun q hq =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := S)).comm ⟨q, h.le_sylow hq⟩ ⟨s, hs⟩)
  have hcard : Nat.card (R ⊔ zpowers s : Subgroup Y) = p ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime R hsp hsR hcomm, h.card_eq]
    ring
  have hE : IsElemAbelian p (R ⊔ zpowers s : Subgroup Y) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.elemAbelian
      (isElemAbelian_zpowers hsp) (le_centralizer_iff.mpr (zpowers_le.mpr
        (mem_centralizer_iff.mpr fun q hq => hcomm q hq)))
  have h3 := le_pRank_of_elemAbelian_card (P := (⊤ : Subgroup Y)) le_top hE hcard
  have := h.pRank_le
  omega

theorem mem_glbPrimeCore_of_mk_eq_one_three {H : Subgroup G} {r : G} (hr : r ∈ H)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore 3 H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) 3 := (QuotientGroup.eq_one_iff _).mp h
  rw [← glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_sylow_through3 (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {U H : Subgroup G} (hUp : IsPGroup p U) (hU2 : 2 ≤ Open.pRank p U) (hUM : U ≤ M)
    (hUH : U ≤ H) : ∃ F : Subgroup G, IsSylowOf p F H ∧ U ≤ F ∧ F ≤ M := by
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hUA : U ≤ H ⊓ M := le_inf hUH hUM
  obtain ⟨T₁, hT₁⟩ := (hUp.comap_subtype (K := H ⊓ M)).exists_le_sylow
  set F'' : Subgroup G := (T₁ : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  have hF''A : IsSylowOf p F'' (H ⊓ M) := ⟨T₁, rfl⟩
  have hUF'' : U ≤ F'' := fun r hr => ⟨⟨r, hUA hr⟩, hT₁ hr, rfl⟩
  have hF''M : F'' ≤ M := hF''A.le.trans inf_le_right
  have hF''H : F'' ≤ H := hF''A.le.trans inf_le_left
  have hF''p : IsPGroup p F'' := hF''A.isPGroup
  obtain ⟨T₂, hT₂⟩ := (hF''p.comap_subtype (K := H)).exists_le_sylow
  set F' : Subgroup G := (T₂ : Subgroup ↥H).map H.subtype
  have hF'H : IsSylowOf p F' H := ⟨T₂, rfl⟩
  have hF''F' : F'' ≤ F' := fun r hr => ⟨⟨r, hF''H hr⟩, hT₂ hr, rfl⟩
  refine ⟨F', hF'H, hUF''.trans hF''F', ?_⟩
  have hF'F'' : F' ≤ F'' := by
    by_contra hnle
    have hlt : F''.subgroupOf F' < ⊤ :=
      lt_top_iff_ne_top.mpr fun htop => hnle (Subgroup.subgroupOf_eq_top.mp htop)
    have : Group.IsNilpotent ↥F' := hF'H.isPGroup.isNilpotent
    obtain ⟨n, hn, hnB⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    rw [← Subgroup.subgroupOf_normalizer_eq hF''F'] at hn
    have hrk : 2 ≤ Open.pRank p F'' :=
      hU2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime hUF'')
    have hnM : (n : G) ∈ M :=
      normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hF''p hF''M hrk hn
    have hQA : F'' ⊔ zpowers (n : G) ≤ H ⊓ M :=
      sup_le hF''A.le (zpowers_le.mpr ⟨hF'H.le n.2, hnM⟩)
    have hQF' : F'' ⊔ zpowers (n : G) ≤ F' := sup_le hF''F' (zpowers_le.mpr n.2)
    have hQ : F'' ⊔ zpowers (n : G) = F'' :=
      hF''A.eq_of_le le_sup_left hQA (hF'H.isPGroup.to_le hQF')
    exact hnB (hQ ▸ mem_sup_right (mem_zpowers (n : G)))
  exact hF'F''.trans hF''M

theorem endgame3_hyp (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    (hPab : IsMulCommutative (P : Subgroup G))
    {x : G} {U H F : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (hHtop : H ≠ ⊤) (hUH : U ≤ H) (hrk : Open.pRank 3 H ≤ 2) (hFH : IsSylowOf 3 F H)
    (hUF : U ≤ F) (hFM : F ≤ M) :
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
  have hab : ∀ S : Sylow 3 (H ⧸ O), IsMulCommutative (S : Subgroup (H ⧸ O)) :=
    isMulCommutative_sylow_quotient (N := H) fun _ hQ => isMulCommutative_of_isPGroup3 hPab hQ
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
        have hrP : (r : G) ∈ (P : Subgroup G) := hUP hrU
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
        have hPC : (P : Subgroup G) ≤ centralizer ({(r : G)} : Set G) := fun g hg =>
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨g, hg⟩ ⟨r, hrP⟩))
        have hNM : normalizer ((zpowers (r : G) : Subgroup G) : Set G) ≤ M :=
          normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM (by
            rw [inf_of_le_left hPC]
            omega) hCM
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
