module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
public import CFSG.LocalAnalysis.ComponentClassification.Sol78SwapBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAAlternatingSmallDegree
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

variable {X : Type} [Group X]

theorem le_pRank_of_elementaryAbelian {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H]
    {E : Subgroup H} (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem three_le_pRank_of_coreQuotient {J : Type*} [Group J] [Finite J] {n : ℕ} (hn : 8 ≤ n)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) : 3 ≤ CFSG.pRank 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, hEc⟩ := UnbalancedGS.AlternatingModel.exists_elementaryAbelian_eight hn
  have h1 : 3 ≤ CFSG.pRank 2 (alternatingGroup (Fin n)) :=
    le_pRank_of_elementaryAbelian one_lt_two hE hEc
  have h2 : CFSG.pRank 2 (J ⧸ pPrimeCore 2 J) = CFSG.pRank 2 (alternatingGroup (Fin n)) := by
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
    exact SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e
  have h3 : CFSG.pRank 2 (J ⧸ pPrimeCore 2 J) = CFSG.pRank 2 J :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (pPrimeCore_coprime_card (p := 2) (G := J)))
  omega

theorem isPLocal_centralizer_of_orderOf_eq_two {G : Type*} [Group G] {y : G}
    (hy : orderOf y = 2) : CFSG.IsPLocal 2 (centralizer ({y} : Set G)) := by
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  refine ⟨zpowers y, ?_, ?_, ?_⟩
  · intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hy
    norm_num at hy
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  · ext g
    rw [mem_centralizer_singleton_iff, mem_normalizer_iff]
    constructor
    · intro hg w
      constructor
      · intro hw
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        have : g * y ^ k * g⁻¹ = y ^ k := by
          rw [(Commute.zpow_right (show Commute g y from hg) k).eq]; group
        rw [this]
        exact zpow_mem_zpowers y k
      · intro hw
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw
        have : w = y ^ k := by
          have h' : w = g⁻¹ * (g * w * g⁻¹) * g := by group
          rw [h', ← hk, ((Commute.zpow_right (show Commute g y from hg) k).inv_left).eq]
          group
        rw [this]
        exact zpow_mem_zpowers y k
    · intro hg
      have hmem : g * y * g⁻¹ ∈ zpowers y := (hg y).mp (mem_zpowers y)
      rcases UnbalancedGS.SmallReeExclusion.eq_one_or_eq_of_mem_zpowers hyy hmem with h | h
      · exfalso
        have : y = 1 := by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [this, orderOf_one] at hy
        norm_num at hy
      · calc g * y = (g * y * g⁻¹) * g := by group
          _ = y * g := by rw [h]

theorem mem_coreActionKernel_of_commute {J : Subgroup X} {y : X}
    (hy : ∀ j ∈ J, j * y = y * j) : y ∈ UnbalancedLayer.coreActionKernel J := by
  refine ⟨mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩, fun j hj => ?_⟩
  · have : y * w * y⁻¹ = w := by rw [← hy w hw]; group
    rw [this]
    exact hw
  · have hu := hy _ hw
    have h1 : w = y * w * y⁻¹ := by
      calc w = y⁻¹ * (y * w * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * w * y⁻¹)) := by rw [hu]
        _ = y * w * y⁻¹ := by group
    rw [h1]
    exact hw
  · have : j⁻¹ * y⁻¹ * j * y = 1 := by
      have h2 : y⁻¹ * j = j * y⁻¹ := by
        calc y⁻¹ * j = y⁻¹ * (j * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * j) * y⁻¹ := by rw [hy j hj]
          _ = j * y⁻¹ := by group
      calc j⁻¹ * y⁻¹ * j * y = j⁻¹ * (y⁻¹ * j) * y := by group
        _ = j⁻¹ * (j * y⁻¹) * y := by rw [h2]
        _ = 1 := by group
    rw [this]
    exact one_mem _

theorem oPrimeResidualOf_core_sup_eq [Finite X] {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) :
    oPrimeResidualOf 2 (pPrimeCoreOf 2 C ⊔ J) = J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCoreOf 2 C with hO
  set Y := O ⊔ J with hY
  have hON : O ≤ normalizer (J : Set X) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJC hJ
  have hJY : J ≤ Y := le_sup_right
  apply le_antisymm
  ·
    have hYN : Y ≤ normalizer (J : Set X) := sup_le hON le_normalizer
    let := Subgroup.normal_subgroupOf_of_le_normalizer hYN
    set N := J.subgroupOf Y with hN
    have hcard := card_sup_mul_card_inf' hON
    have hNcard : Nat.card N = Nat.card J :=
      Nat.card_congr (subgroupOfEquivOfLe hJY).toEquiv
    have hYcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hJpos : 0 < Nat.card J := Nat.card_pos
    have hdvd : Nat.card (Y ⧸ N) ∣ Nat.card O := by
      refine ⟨Nat.card (O ⊓ J : Subgroup X), ?_⟩
      have h1 : Nat.card (Y ⧸ N) * Nat.card J * Nat.card (O ⊓ J : Subgroup X) =
          Nat.card O * Nat.card J := by
        calc Nat.card (Y ⧸ N) * Nat.card J * Nat.card (O ⊓ J : Subgroup X) =
            (Nat.card (Y ⧸ N) * Nat.card N) * Nat.card (O ⊓ J : Subgroup X) := by rw [hNcard]
          _ = Nat.card Y * Nat.card (O ⊓ J : Subgroup X) := by rw [← hYcard]
          _ = Nat.card O * Nat.card J := hcard
      have h2 : (Nat.card (Y ⧸ N) * Nat.card (O ⊓ J : Subgroup X)) * Nat.card J =
          Nat.card O * Nat.card J := by
        rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_right hJpos h2).symm
    have hOodd : Nat.Coprime 2 (Nat.card O) := by
      rw [hO, pPrimeCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := C)
    have hYodd : Nat.Coprime 2 (Nat.card (Y ⧸ N)) := Nat.Coprime.coprime_dvd_right hdvd hOodd
    unfold oPrimeResidualOf oPrimeResidual
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    have h1 : orderOf (QuotientGroup.mk' N y) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    have h2 := orderOf_dvd_natCard (QuotientGroup.mk' N y)
    have h3 : orderOf (QuotientGroup.mk' N y) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k hYodd))
        h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  ·
    have hres : CatalogueBPrimeJoin.primeResidual 2 J = ⊤ :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJ).2.1
    intro j hj
    have hjT : (⟨j, hj⟩ : J) ∈ CatalogueBPrimeJoin.primeResidual 2 J := by
      rw [hres]; exact mem_top _
    rw [CatalogueBPrimeJoin.primeResidual_eq_closure] at hjT
    have hmap : (closure {x : J | ∃ k : ℕ, orderOf x = 2 ^ k}).map (inclusion hJY) ≤
        oPrimeResidual 2 Y := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
      exact subset_closure ⟨k, by rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]⟩
    exact ⟨inclusion hJY ⟨j, hj⟩, hmap ⟨_, hjT, rfl⟩, rfl⟩

theorem mem_solomonFamily_of_isAltTwoComponent [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    (h : SolAltLit.IsAltTwoComponent t J n) : J ∈ solomonFamily X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hJC, hJ, -⟩ := h
  set C := centralizer ({t} : Set X) with hC
  have hCT : centralizer ((zpowers t : Subgroup X) : Set X) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hJinf : J ⊓ C = J := inf_eq_left.mpr hJC
  have hlayer : pLayerOf 2 J = J := by
    apply le_antisymm
    · exact sSup_le fun K hK => hK.1
    · exact le_sSup ⟨le_rfl, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le le_rfl hJC hJ⟩
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hJC hJ, zpowers t, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht
    norm_num at ht
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  · rw [zpowers_le]
    exact mem_coreActionKernel_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hJC hj))
  · rw [hCT, hJinf, hlayer, oPrimeResidualOf_core_sup_eq hJC hJ]
    exact ⟨hJC, hJ⟩

theorem oddResidualIn_eq_oPrimeResidualOf (Y : Subgroup X) :
    FooteLit.oddResidualIn Y = oPrimeResidualOf 2 Y := by
  unfold FooteLit.oddResidualIn oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    refine ⟨⟨x, hx⟩, ⟨k, Subtype.ext ?_⟩, rfl⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, pow_orderOf_eq_one]
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    refine ⟨y.2, ?_⟩
    have hdvd : orderOf (y : X) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

theorem isSolomonMember_of_isAltTwoComponent [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    (h : SolAltLit.IsAltTwoComponent t J n) : FooteLit.IsSolomonMember J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hJC, hJ, -⟩ := h
  set C := centralizer ({t} : Set X) with hC
  have hCT : centralizer ((zpowers t : Subgroup X) : Set X) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hJinf : J ⊓ C = J := inf_eq_left.mpr hJC
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hJC hJ, zpowers t, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht
    norm_num at ht
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  · rw [zpowers_le]
    exact mem_coreActionKernel_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hJC hj))
  · rw [hCT, hJinf, oddResidualIn_eq_oPrimeResidualOf]
    change IsPCompIn 2 C (oPrimeResidualOf 2 (pPrimeCoreOf 2 C ⊔ J))
    rw [oPrimeResidualOf_core_sup_eq hJC hJ]
    exact ⟨hJC, hJ⟩

end CFSG.ComponentClassification.Sol78
