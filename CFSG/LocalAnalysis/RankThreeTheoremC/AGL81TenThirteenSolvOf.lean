module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

namespace SolvThree

theorem map_mk_le_iff_le_hyp111Pre {p : ℕ} {H I : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hIH : I ≤ H) :
    (I.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K ↔
      I ≤ hyp111Pre p H K := by
  unfold hyp111Pre
  rw [Subgroup.map_le_iff_le_comap]
  constructor
  · intro h x hx
    exact ⟨⟨x, hIH hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · intro h x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_subgroupOf.mp hx))
    have hwx' : w = x := H.subtype_injective hwx
    rwa [hwx'] at hw

theorem oUpperTwo_subgroupOf {H I : Subgroup G} (hIH : I ≤ H) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo I).subgroupOf H =
      CFSG.ComponentClassification.AS76b.oUpperTwo (I.subgroupOf H) := by
  have h1 : (CFSG.ComponentClassification.AS76b.oUpperTwo (I.subgroupOf H)).map H.subtype =
      CFSG.ComponentClassification.AS76b.oUpperTwo I := by
    rw [SUPair.map_oUpperTwo, Subgroup.subgroupOf_map_subtype, inf_of_le_left hIH]
  rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem map_oUpperTwo_top_eq {p : ℕ} {H I₀ : Subgroup G} (hI₀H : I₀ ≤ H) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup ↥I₀)).map
        ((QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hI₀H)) =
      ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  rw [SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map,
    CFSG.AGLEmbeddingD2.range_mk_comp_inclusion hI₀H, oUpperTwo_subgroupOf hI₀H,
    SUPair.map_oUpperTwo]

theorem map_subtype_oUpperTwo_sup_pCore (I₀ : Subgroup G) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup ↥I₀) ⊔
        CFSG.pCore 2 ↥I₀).map I₀.subtype =
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ⊔ pCoreOf 2 I₀ := by
  rw [Subgroup.map_sup, SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem ne_top_of_isTwoLocal (hS : Setting G) {H : Subgroup G} (hH : IsTwoLocal H) : H ≠ ⊤ := by
  obtain ⟨S, hS1, hS2, rfl⟩ := hH
  intro htop
  haveI : IsSimpleGroup G := hS.simple
  have hSn : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hSn.eq_bot_or_eq_top with h | h
  · exact hS1 h
  · subst h
    have hG2 : IsPGroup 2 G := hS2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZ := hG2.bot_lt_center
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hZ' | hZ'
    · exact hZ.ne' hZ'
    · obtain ⟨x, y, hxy⟩ := hS.nonab
      exact hxy (Subgroup.mem_center_iff.mp (hZ' ▸ Subgroup.mem_top y) x)

theorem pCoreOf_two_d1X0_le_centralizer {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hKn : K.Normal) :
    pCoreOf 2 (d1X0 p M H) ≤ centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := primeComplementCore (G := H) p with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  set Cn := centralizer (K : Set (H ⧸ O)) with hCn
  haveI : K.Normal := hKn
  haveI : Cn.Normal := by rw [hCn]; infer_instance
  set V := pCoreOf 2 (d1X0 p M H) with hV
  set W : Subgroup ↥H := V.comap π with hW
  have hV2 : IsPGroup 2 V := pCoreOf_isPGroup 2 _
  set QH : Subgroup ↥H := Q.subgroupOf H with hQH
  have hQp : IsPGroup p QH := hd.base.2.1.comap_of_injective H.subtype H.subtype_injective
  have hQW : QH ≤ normalizer (W : Set ↥H) := by
    intro q hq
    have hqX0 : π q ∈ d1X0 p M H :=
      Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr ⟨q.2, hd.base.1 (Subgroup.mem_subgroupOf.mp hq)⟩)
    have hqN := localGroup_le_normalizer_pCoreOf 2 (d1X0 p M H) hqX0
    rw [Subgroup.mem_normalizer_iff] at hqN ⊢
    intro w
    simp only [hW, Subgroup.mem_comap, map_mul, map_inv]
    exact hqN (π w)
  have hWp : ¬ p ∣ Nat.card W := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : π (x : ↥H) ∈ V := x.2
    obtain ⟨n, hn⟩ := hV2 ⟨π x, h1⟩
    have h2 : (π (x : ↥H)) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hxH : orderOf (x : ↥H) = p := by rw [Subgroup.orderOf_coe, hx]
    have h3 : orderOf (π (x : ↥H)) ∣ Nat.gcd (2 ^ n) p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) ((orderOf_map_dvd π _).trans (dvd_of_eq hxH))
    have hg : Nat.gcd (2 ^ n) p = 1 :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
    have h5 : (x : ↥H) ∈ O := (QuotientGroup.eq_one_iff _).mp h3
    have hO' : p.Coprime (Nat.card O) := primeComplementCore_coprime p
    have h6 : p ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨(x : ↥H), h5⟩ : ↥O)
      rwa [Subgroup.orderOf_mk, hxH] at this
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO' h6)
  obtain ⟨S, hSQ⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp Nat.prime_two hQp
    hQW hWp
  set S₁ : Subgroup ↥H := (S : Subgroup ↥W).map W.subtype with hS₁
  have hS₁G2 : IsPGroup 2 (S₁.map H.subtype) := (S.isPGroup'.map _).map _
  have hQS₁ : Q ≤ normalizer ((S₁.map H.subtype : Subgroup G) : Set G) := by
    intro q hq
    have hqH := hd.le_H hq
    have hqS := hSQ (Subgroup.mem_subgroupOf.mpr hq : (⟨q, hqH⟩ : ↥H) ∈ QH)
    rw [Subgroup.mem_normalizer_iff] at hqS ⊢
    intro g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨q, hqH⟩ * s * ⟨q, hqH⟩⁻¹, (hqS s).mp hs, rfl⟩
    · rintro ⟨s, hs, hsg⟩
      have hgH : g ∈ H := by
        have : g = q⁻¹ * (q * g * q⁻¹) * q := by group
        rw [this, ← hsg]
        exact H.mul_mem (H.mul_mem (H.inv_mem hqH) s.2) hqH
      refine ⟨⟨g, hgH⟩, (hqS ⟨g, hgH⟩).mpr ?_, rfl⟩
      have : (⟨q, hqH⟩ : ↥H) * ⟨g, hgH⟩ * ⟨q, hqH⟩⁻¹ = s := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hsg.symm)
      rw [this]
      exact hs
  have hS₁X := hd.b3 (S₁.map H.subtype) hS₁G2 (Subgroup.map_subtype_le _) hQS₁
  have hS₁C : S₁ ≤ Cn.comap π := by
    unfold d1PlusCore at hS₁X
    exact (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hS₁X
  intro v hv
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O v
  have hwW : w ∈ W := hv
  obtain ⟨a, m, hm, hwm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  obtain ⟨n, hn⟩ := hV2 ⟨π w, hv⟩
  have hvord : orderOf (π w) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hn
    simpa using this
  have hcop : m.Coprime (orderOf (π w)) :=
    (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hm)).coprime_dvd_right hvord
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  set w₂ := (w ^ m) ^ c with hw₂
  have hw₂W : w₂ ∈ W := W.pow_mem (W.pow_mem hwW m) c
  have hπw₂ : π w₂ = π w := by rw [hw₂, map_pow, map_pow, hc]
  have hw₂pow : w₂ ^ 2 ^ a = 1 := by
    rw [hw₂, ← pow_mul, ← pow_mul, show m * (c * 2 ^ a) = 2 ^ a * m * c by ring, pow_mul, ← hwm,
      pow_orderOf_eq_one, one_pow]
  have hw₂2 : IsPGroup 2 (zpowers (⟨w₂, hw₂W⟩ : ↥W)) := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw₂pow, one_zpow]
  obtain ⟨S', hS'⟩ := hw₂2.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq ↥W S S'
  have hmem : (⟨w₂, hw₂W⟩ : ↥W) ∈ (S' : Subgroup ↥W) := hS' (mem_zpowers _)
  rw [← hu, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨s, hs, hsw⟩ := hmem
  have hsC : π (s : ↥H) ∈ Cn := hS₁C ⟨s, hs, rfl⟩
  have hw₂eq : w₂ = (u : ↥H) * (s : ↥H) * (u : ↥H)⁻¹ := by
    have := congrArg (fun z : ↥W => (z : ↥H)) hsw
    simpa [MulAut.conj_apply] using this.symm
  rw [← hπw₂, hw₂eq, map_mul, map_mul, map_inv]
  exact (inferInstance : Cn.Normal).conj_mem _ hsC _

theorem pRank_three_top_le {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hS : Setting G)
    (hd : AGL81CfgData 3 P M H Q K) :
    pRank 3 (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : (3 : ℕ).Coprime (Nat.card (primeComplementCore (G := H) 3)) :=
    primeComplementCore_coprime 3
  have h1 := pRank_map_mk_eq_pRank_map_subtype Nat.prime_three (primeComplementCore (G := H) 3) hO
    (⊤ : Subgroup ↥H)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, h1]
  exact (local_pRank_le_evenRank 3 Nat.prime_three (by decide) H hd.maxH.1).trans hS.rank.le

end SolvThree

open SolvThree

variable (G) in
theorem agl81TenThirteenSolvThree_of (h9 : AGL81NineCompetitorQ G) (h31 : KFactThreeOne)
    (hK : KFactThreeFourSolvThree) (hst : AGL81TenThreeSolvStructCfg G)
    (h12 : AGL81TenTwelveSolvSigma G) : AGL81TenThirteenSolvThree G := by
  intro hS h3σ P M H Q K hd L hL I₀ hI₀ hb hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hin := kFactInputs_of_cfg h9 hS hd
  obtain ⟨R, E, hER, hE, hEc, hcore⟩ := hin.core
  have hLM : IsSubnormal L M := hL.subnormal
  have hI₀M : I₀ ≤ H ⊓ M := le_inf_of_cZero hLM hI₀
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  set O := primeComplementCore (G := H) 3 with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  set σ : ↥I₀ →* ↥H ⧸ O := π.comp (Subgroup.inclusion hI₀H) with hσ
  have hσrange : σ.range = (I₀.subgroupOf H).map π :=
    CFSG.AGLEmbeddingD2.range_mk_comp_inclusion hI₀H
  have hσY : σ.range ≤ d1X0 3 M H := by
    rw [hσrange]
    exact map_mk_le_d1X0 hI₀M
  have hσsub : IsSubnormal σ.range (d1X0 3 M H) := by
    rw [hσrange]
    exact isSubnormal_map_mk_d1X0 (isSubnormal_inf_of_cZero hLM hI₀)
  have hJ := map_oUpperTwo_top_eq (p := 3) hI₀H
  have hOH : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ H :=
    (oUpperTwo_le_self I₀).trans hI₀H
  have hJC : ¬ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup ↥I₀)).map σ ≤
      centralizer (K : Set (H ⧸ O)) := by
    rw [hJ]
    exact fun h => hX ((map_mk_le_centralizer_iff (K := K) hOH).mp h)
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hK0 : d1KBar 3 M H ≠ ⊥ := by
    rw [← hd.kbar]
    exact fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  have hZ : Subgroup.center K = ⊥ := by
    have h := center_d1KBar_eq_bot_of_escape h31 hS.kProper he hd.base hd.le_H
      (ne_top_of_isTwoLocal hS hd.maxH.1) hK0
    rw [hd.kbar]
    exact h
  have hcond : SolvThreeAutCond (d1X0 3 M H) σ := by
    by_cases h3 : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3))
    · exact Or.inl h3
    · right
      obtain ⟨y, hyHM, ⟨k, hk⟩, hyN, g, hg, hyg⟩ := (hst hS P M H Q K hd L hL I₀ hI₀ hb).2 h3
      have hyH : y ∈ H := hyHM.1
      let α : ↥I₀ →* ↥I₀ :=
        { toFun := fun x => ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN x).mp x.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun x x' => Subtype.ext (by simp [mul_assoc]) }
      refine ⟨π ⟨y, hyH⟩, ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyHM, rfl⟩, ⟨k, ?_⟩, α,
        fun x => ?_, ⟨g, hg⟩, ?_⟩
      · rw [← map_pow]
        have : (⟨y, hyH⟩ : ↥H) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
        rw [this, map_one]
      · show π (Subgroup.inclusion hI₀H (α x)) = π ⟨y, hyH⟩ * π (Subgroup.inclusion hI₀H x) *
          (π ⟨y, hyH⟩)⁻¹
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      · intro hmem
        apply hyg
        have h1 := Subgroup.mem_map_of_mem I₀.subtype hmem
        rw [map_subtype_oUpperTwo_sup_pCore] at h1
        simpa [α, mul_assoc] using h1
  have hdir : SolvThreeDirectCond (d1X0 3 M H)
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup ↥I₀)).map σ) := by
    rw [hJ]
    exact (hst hS P M H Q K hd L hL I₀ hI₀ hb).1
  have hker : Nat.Coprime 3 (Nat.card σ.ker) := by
    have hle : σ.ker.map (Subgroup.inclusion hI₀H) ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hcard : Nat.card σ.ker = Nat.card (σ.ker.map (Subgroup.inclusion hI₀H)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hI₀H)).symm
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (primeComplementCore_coprime 3)
  obtain ⟨hJK, htarget⟩ := hK (H ⧸ O) K (d1X0 3 M H) E R ↥I₀ σ hin.normal hin.list hZ
    (pRank_three_top_le hS hd) hin.rank hin.cent hin.comp hER hE hEc hcore
    (pCoreOf_two_d1X0_le_centralizer hd Nat.prime_three (by decide) hin.normal) hker hσY hσsub hb
    hcond hdir hJC
  have hIK : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre 3 H K := by
    rw [hJ] at hJK
    exact (map_mk_le_iff_le_hyp111Pre hOH).mp hJK
  refine ⟨?_, hIK⟩
  rcases htarget with hA6 | htarget
  · exact hA6
  exfalso
  rw [hJ] at hJK
  set J := ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map π with hJdef
  have hJX0 : J ≤ d1X0 3 M H := map_mk_le_d1X0 ((oUpperTwo_le_self I₀).trans hI₀M)
  have hJsub : IsSubnormal J (K ⊓ d1X0 3 M H) := by
    have h1 := (isSubnormal_map_mk_d1X0 (p := 3) (isSubnormal_oUpperTwo_inf_of_cZero hLM hI₀)).inf
      (K ⊓ d1X0 3 M H)
    rwa [inf_of_le_left (le_inf hJK hJX0), inf_of_le_right inf_le_right] at h1
  have hO2I : ((pCoreOf 2 I₀).subgroupOf H).map π ≤ centralizer (K : Set (H ⧸ O)) := by
    refine le_trans ?_ (pCoreOf_two_d1X0_le_centralizer hd Nat.prime_three (by decide) hin.normal)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal ?_ ?_
    · refine isSubnormal_map_mk_d1X0 (IsSubnormal.step (pCoreOf_le 2 I₀) ?_
        (isSubnormal_inf_of_cZero hLM hI₀))
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 I₀)).mpr
        (localGroup_le_normalizer_pCoreOf 2 I₀)
    · exact ((pCoreOf_isPGroup 2 I₀).comap_of_injective H.subtype H.subtype_injective).map π
  have hJ3 : IsPGroup 3 J := by
    rintro ⟨j, hj⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hj
    have hcube : (h : G) ^ 3 ∈ pCoreOf 2 I₀ :=
      CFSG.AGLEmbedding.IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hb _
        (Subgroup.mem_subgroupOf.mp hh)
    have hC : π h ^ 3 ∈ centralizer (K : Set (H ⧸ O)) := by
      rw [← map_pow]
      exact hO2I (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (by simpa using hcube)))
    have hK3 : π h ^ 3 ∈ K := K.pow_mem (hJK (Subgroup.mem_map_of_mem π hh)) 3
    have hz : (⟨π h ^ 3, hK3⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hC) k k.2)
    rw [hZ, Subgroup.mem_bot] at hz
    simpa using congrArg Subtype.val hz
  have hJdir : SolvThreeDirectCond (d1X0 3 M H) J := (hst hS P M H Q K hd L hL I₀ hI₀ hb).1
  have hJbot : J = ⊥ := h12 hS h3σ P M H Q K hd L hL I₀ hI₀ hb htarget J hJdef hJK hJ3 hJsub hJdir
  exact hX ((map_mk_le_centralizer_iff (K := K) hOH).mp (by rw [← hJdef, hJbot]; exact bot_le))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
