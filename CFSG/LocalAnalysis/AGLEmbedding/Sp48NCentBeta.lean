module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentApply
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.Sp48NRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeLift
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Ree

variable {X : Type} [Group X] [Finite X]

theorem zpowers_inf_eq_bot_of_pow_three_not_mem {t z : X} {K : Subgroup X} (ht : t ^ 3 = z)
    (hzp : orderOf z = 3) (hzK : z ∉ K) : Subgroup.zpowers t ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  have ht9 : t ^ 3 ^ 2 = 1 := by
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ht, ← hzp, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ht9)
  have hp : IsPGroup 3 (Subgroup.zpowers t ⊓ K : Subgroup X) :=
    (IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])).to_le inf_le_left
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := (Subgroup.zpowers t ⊓ K : Subgroup X)) 3
    (by
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      have h1 : Nat.card (Subgroup.zpowers t ⊓ K : Subgroup X) ≠ 1 := fun h =>
        hne (Subgroup.card_eq_one.mp h)
      rw [hn] at h1 ⊢
      exact dvd_pow_self 3 (by rintro rfl; exact h1 (pow_zero 3)))
  have hcz : (z : X) ∈ Subgroup.zpowers (c : X) :=
    mem_zpowers_of_orderOf_eq_of_isCyclic (Z := Subgroup.zpowers t)
      (ht ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers t) 3) c.2.1
      (by rw [hzp, Subgroup.orderOf_coe, hc])
  exact hzK ((Subgroup.zpowers_le.mpr c.2.2) hcz)

theorem exists_mem_sylow_cube {Tb : Sylow 3 X} {t z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = 3) (ht : t ^ 3 = z) : ∃ t' ∈ (Tb : Subgroup X), t' ^ 3 = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht9 : t ^ 3 ^ 2 = 1 := by
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ht, ← hzp, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ht9)
  have hpt : IsPGroup 3 (Subgroup.zpowers t) := IsPGroup.of_card (n := i)
    (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hpt.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q Tb
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hQ (Subgroup.mem_zpowers t))
  · rw [conj_pow, ht, Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

theorem exists_involution_of_ree {Tb : Sylow 3 X} {X₀ : Subgroup X}
    (hred : ReducedNongeneration 3 X Tb X₀) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = 3) {K : Subgroup X} (hKn : K.Normal) (hzK : z ∉ K)
    (hKR4 : KFactReeBorelMaximal) (hKJ : KFactReeInvolution) {d : TauCeti.ValidLieTypeIndex}
    (hRee : IsReeGTwoIndex 3 d) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    {t : X} (ht : t ^ 3 = z) :
    ∃ J ∈ X₀, J ^ 2 = 1 ∧ J ≠ 1 ∧ ∃ Y : Subgroup X, IsPGroup 3 Y ∧ Y ≤ X₀ ∧
      Y ≤ Subgroup.centralizer ({J} : Set X) ∧ 9 * 3 ^ d.1.fieldExponent ≤ Nat.card Y ∧
      d.1.fieldExponent + 1 ≤ CFSG.Open.pRank 3 Y ∧
      ¬ Subgroup.centralizer ({J} : Set X) ≤ X₀ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Tb hKn.isSubnormal
  obtain ⟨J, hJN, hJ2, hconj, hVel, hVcard, hCB⟩ := hKJ K d hRee he T
  have hn := hRee.three_le_fieldExponent
  set U : Subgroup X := (Tb : Subgroup X) ⊓ K with hU
  set J' : X := (J : X) with hJ'
  set V : Subgroup X := ((T : Subgroup K) ⊓ Subgroup.centralizer ({J} : Set K)).map K.subtype
  have hVel' : IsElemAbelian 3 V := elementary_abelian_map 3 hVel K.subtype
  have hVcard' : Nat.card V = 3 ^ d.1.fieldExponent := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hVcard]
  have hVU : V ≤ U := by
    rw [← hT]
    exact Subgroup.map_mono inf_le_left
  have hVJ : V ≤ Subgroup.centralizer ({J'} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hv.2))
  have hU3 : 3 ≤ CFSG.Open.pRank 3 U :=
    hn.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨V, hVU, hVel', hVcard'⟩)
  have hNU : Subgroup.normalizer (U : Set X) ≤ X₀ :=
    (normalizer_le_weakCore 3 inf_le_left (le_trans (by norm_num) hU3)
      (hU3.trans (pRank_mono 3 hp le_sup_left))).trans hred.weakCore_le
  have hTbX : (Tb : Subgroup X) ≤ X₀ :=
    Subgroup.le_normalizer.trans ((normalizer_le_weakCore_of_rank 3 hp _
      hred.three_le_pRank).trans hred.weakCore_le)
  have hKX : ¬ K ≤ X₀ := by
    intro hK
    apply hred.ne_top
    rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top T, hT]
    exact sup_le hNU hK
  have hBX : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map K.subtype ≤ X₀ := by
    refine (Subgroup.le_normalizer_map K.subtype).trans ?_
    rw [hT]
    exact hNU
  have hCX : ¬ (Subgroup.centralizer ({J} : Set K)).map K.subtype ≤ X₀ := by
    intro hYX
    have hK : K = (Subgroup.normalizer ((T : Subgroup K) : Set K) ⊔
        Subgroup.centralizer ({J} : Set K)).map K.subtype := by
      rw [((hKR4 K d hRee he T).not_le_iff_codisjoint.mp hCB).eq_top, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    apply hKX
    rw [hK, Subgroup.map_sup]
    exact sup_le hBX hYX
  have hJ'N : J' ∈ Subgroup.normalizer (U : Set X) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map K.subtype ⟨J, hJN, rfl⟩
  have hJ'2 : J' ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hJ2, pow_orderOf_eq_one, Subgroup.coe_one]
  have hJ'1 : J' ≠ 1 := fun h => by
    rw [show J = 1 from Subtype.ext h, orderOf_one] at hJ2
    omega
  have hUN : ∀ y ∈ (Tb : Subgroup X), y ∈ Subgroup.normalizer (U : Set X) := fun y hy =>
    mem_normalizer_inf_of_mem_normalizer (Subgroup.le_normalizer hy)
      ((Subgroup.normalizer_eq_top K).symm ▸ Subgroup.mem_top y)
  obtain ⟨t', ht'Tb, ht'⟩ := exists_mem_sylow_cube (Tb := Tb) hz hzp ht
  set A : Subgroup X := Subgroup.zpowers t' with hA
  have hATb : A ≤ Tb := Subgroup.zpowers_le.mpr ht'Tb
  have hAU : A ⊓ U = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
      (zpowers_inf_eq_bot_of_pow_three_not_mem ht' hzp hzK).le)
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; omega
  have hA9 : Nat.card A = 9 := by
    rw [hA, Nat.card_zpowers]
    have h9 : t' ^ 3 ^ 2 = 1 := by
      rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, ht', ← hzp, pow_orderOf_eq_one]
    obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h9)
    have hi' : i = 2 := by
      by_contra hne
      have hdvd : orderOf t' ∣ 3 := by
        rw [hi]; simpa using pow_dvd_pow 3 (show i ≤ 1 by omega)
      exact hz1 (ht' ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
    rw [hi, hi']; norm_num
  have hYP : A ⊔ U ≤ Tb := sup_le hATb inf_le_left
  have hconj' : ∀ y ∈ A ⊔ U, ∃ u ∈ U, y * J' * y⁻¹ = u * J' * u⁻¹ := by
    intro y hy
    have hyN := hUN y (hYP hy)
    set c : K := ⟨y * J' * y⁻¹, hKn.conj_mem _ J.2 y⟩
    have hmemT : ∀ k : K, k ∈ (T : Subgroup K) ↔ (k : X) ∈ U := fun k => by
      rw [← hT]
      exact ⟨fun hk => ⟨k, hk, rfl⟩, fun ⟨k', hk', hkk'⟩ => (Subtype.ext hkk' : k' = k) ▸ hk'⟩
    have hcN : c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [hmemT, hmemT]
      exact Subgroup.mem_normalizer_iff.mp ((mul_mem (mul_mem hyN hJ'N) (inv_mem hyN))) k
    have hc2 : orderOf c = 2 := by
      rw [← Subgroup.orderOf_coe c, ← hJ2, ← Subgroup.orderOf_coe J]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective J'
    obtain ⟨u, hu, hcu⟩ := hconj c hcN hc2
    exact ⟨u, (hmemT u).mp hu, by simpa [c] using congrArg Subtype.val hcu⟩
  have hcount := card_mul_card_inf_centralizer_eq (fun y hy => hUN y (hATb hy)) hconj'
  rw [hAU, Subgroup.card_bot, mul_one, hA9] at hcount
  have hUJ : 3 ^ d.1.fieldExponent ≤ Nat.card (U ⊓ Subgroup.centralizer ({J'} : Set X) :
      Subgroup X) := hVcard' ▸ Subgroup.card_le_of_le (le_inf hVU hVJ)
  refine ⟨J', hNU hJ'N, hJ'2, hJ'1, (A ⊔ U) ⊓ Subgroup.centralizer ({J'} : Set X),
    Tb.isPGroup'.to_le (inf_le_left.trans hYP), inf_le_left.trans (hYP.trans hTbX), inf_le_right,
    hcount ▸ Nat.mul_le_mul_left 9 hUJ, ?_, ?_⟩
  ·
    have hztV : z ∉ V := fun hzV => hzK (Subgroup.mem_inf.mp (hVU hzV)).2
    have hztC : z ∈ Subgroup.centralizer (V : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hz v
    have hzt3 : z ^ 3 = 1 := by rw [← hzp, pow_orderOf_eq_one]
    have hzA : z ∈ A := ht' ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers t') 3
    exact succ_le_pRank_of_isElemAbelian hp hVel' hVcard' hztC hzt3 hztV
      (le_inf (hVU.trans le_sup_right) hVJ)
      ⟨Subgroup.mem_sup_left hzA, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hz J').symm⟩
  · intro hCJ
    apply hCX
    rintro _ ⟨k, hk, rfl⟩
    exact hCJ (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)))

end Ree

section Beta

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem odd_card_primeCore_of_lt (hext : D1Extremal 3 P M H R) {d : G}
    (hRd : R ≤ Subgroup.centralizer ({d} : Set G)) {Y : Subgroup G} (hY : IsPGroup 3 Y)
    (hRY : R < Y) (hYC : Y ≤ M ⊓ Subgroup.centralizer ({d} : Set G))
    (hCM : ¬ Subgroup.centralizer ({d} : Set G) ≤ M) :
    Odd (Nat.card (primeComplementCore (G := Subgroup.centralizer ({d} : Set G)) 3)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G)
  set OC := primeComplementCore (G := C) 3
  have hOC := primeComplementCore_coprime (G := C) 3
  have hOsub : (OC.map C.subtype).subgroupOf C = OC :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective OC
  have hOn : ((OC.map C.subtype).subgroupOf C).Normal := by
    rw [hOsub]
    infer_instance
  have hOcard : Nat.card (OC.map C.subtype) = Nat.card OC :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hOM : OC.map C.subtype ≤ M := by
    rintro _ ⟨o, ho, rfl⟩
    exact hext.mem_of_mem_primeCore hRd ho
  have hrank : 3 ≤ CFSG.Open.pRank 3 Y :=
    hext.three_le_pRank.trans (pRank_mono 3 hp hRY.le)
  have hodd := odd_card_of_twoLocals_le hp hY (hYC.trans inf_le_right) hCM
    (Subgroup.map_subtype_le _) hOn (hOcard ▸ hOC) hOM fun T hT hT1 hPT =>
      hext.le_of_card_lt (hYC.trans inf_le_left) hY hrank (Subgroup.card_lt_of_lt hRY)
        ⟨T, hT1, hT, rfl⟩ hPT
  rwa [hOcard] at hodd

theorem d1Sp48NCentBetaResidue_of (hβ : KFactBeta) (hId : KFactCaseTwoReeId)
    (hKR4 : KFactReeBorelMaximal) (hKJ : KFactReeInvolution) : D1Sp48NCentBetaResidue := by
  intro G _ _ P M H R X U A V d hloc hext hd hO3 hdZ hd1 hCH hY hinv hO Tb K hred hR4 hcat hzZ
    hK hKn huniq hzK hsolv hB
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hd.elem_X.2 d (hd.center_le hdZ)) hd1
  have hzp : orderOf (QuotientGroup.mk' (primeComplementCore (G := C) 3)
      ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) = 3 :=
    orderOf_mk_of_coprime hp _ (primeComplementCore_coprime 3)
      (by rw [← Subgroup.orderOf_coe]; exact hd3)
  obtain ⟨hs, hn, hc, hAut, T, hTnc, hΓ⟩ :=
    hred.exists_sylow_of_not_mem hR4 hcat hzZ hzp hK hKn hzK hβ
  obtain ⟨B, L, f, hf, hL⟩ := hB
  obtain ⟨dR, hRee, he⟩ := hId K hs hn hc T hTnc hΓ hAut B L hL f hf
  have hRC : R ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hdZ.2 r hr)
  obtain ⟨w, hwR, hw3⟩ := D1Sp48NData.exists_cube hd (hd.center_le hdZ)
  have ht : (QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨w, hRC hwR⟩) ^ 3 =
      QuotientGroup.mk' (primeComplementCore (G := C) 3)
        ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
    rw [← map_pow]
    exact congrArg _ (Subtype.ext (by simpa using hw3))
  obtain ⟨J, hJX, hJ2, hJ1, Ys, hYp, hYX, hYJ, hYcard, hYrk, hCJ⟩ :=
    exists_involution_of_ree hred hzZ hzp hKn hzK hKR4 hKJ hRee he ht
  obtain ⟨Y, hY3, hRY, hYC⟩ := hY
  have hodd := odd_card_primeCore_of_lt hext hRC hY3 hRY hYC
    (fun h => hCH (inf_le_left.trans h))
  have hn3 := hRee.three_le_fieldExponent
  have hR : Nat.card R ≤ Nat.card Ys := by
    rw [hd.card_R]
    refine le_trans ?_ hYcard
    calc 3 ^ 5 = 9 * 3 ^ 3 := by norm_num
      _ ≤ 9 * 3 ^ dR.1.fieldExponent :=
        Nat.mul_le_mul_left 9 (Nat.pow_le_pow_right (by norm_num) hn3)
  have hRr : CFSG.Open.pRank 3 R < CFSG.Open.pRank 3 Ys := by
    have := D1Sp48NData.pRank_le hd
    omega
  exact hCJ (hext.centralizer_le_of_reducedCentralizer hRC hodd hJX hJ2 hJ1 hYp hYX hYJ hR hRr)

end Beta

end CFSG.AGLEmbedding
