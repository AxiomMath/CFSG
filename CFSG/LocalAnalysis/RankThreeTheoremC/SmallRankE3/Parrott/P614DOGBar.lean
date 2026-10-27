module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOGSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOGL34
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_eq_map relPPrimeCore_conj_mem coprime_card_relPPrimeCore)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

abbrev kb (H K : Subgroup G) : Subgroup (Bar ↥H) := (K.subgroupOf H).map (barMk ↥H)

abbrev qb (H Q : Subgroup G) : Subgroup (Bar ↥H) := (Q.subgroupOf H).map (barMk ↥H)

theorem map_subtype_primeComplementCore (H : Subgroup G) :
    (primeComplementCore (G := ↥H) 3).map H.subtype = rankThreePrimeCore 3 H :=
  (relPPrimeCore_eq_map Nat.prime_three H).symm

theorem barMk_eq_one_iff {H : Subgroup G} (h : ↥H) :
    barMk ↥H h = 1 ↔ (h : G) ∈ rankThreePrimeCore 3 H := by
  rw [← map_subtype_primeComplementCore, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm

theorem kb_normal {H K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G)) :
    (kb H K).Normal :=
  haveI : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

variable {M H Q K : Subgroup G} {x z : G}

theorem pPrimeCore_eq_inf (hD : Data278 M H x z Q K) :
    CFSG.pPrimeCore 3 ↥K = (K ⊓ rankThreePrimeCore 3 H).subgroupOf K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K).Normal := by
    constructor
    intro n hn k
    rw [mem_subgroupOf] at hn ⊢
    exact ⟨K.mul_mem (K.mul_mem k.2 hn.1) (K.inv_mem k.2),
      relPPrimeCore_conj_mem hn.2 (hD.K_le k.2)⟩
  have hc : Nat.Coprime 3 (Nat.card ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_relPPrimeCore Nat.prime_three H)
  have hle : (K ⊓ rankThreePrimeCore 3 H).subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K :=
    le_sSup ⟨hn, hc⟩
  set N₃ : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype with hN₃
  have hN₃s : N₃.subgroupOf K = CFSG.pPrimeCore 3 ↥K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hN₃n : (N₃.subgroupOf K).Normal := by
    rw [hN₃s]
    exact CFSG.pPrimeCore_normal
  have hKD : K ⊓ rankThreePrimeCore 3 H ≤ N₃ := by
    have h := map_mono (f := K.subtype) hle
    rwa [map_subgroupOf_eq_of_le inf_le_left] at h
  rcases hD.K_max N₃ (map_subtype_le _) hN₃n hKD with h | h
  · rw [← hN₃s, h]
  · exfalso
    have htop : CFSG.pPrimeCore 3 ↥K = ⊤ := by rw [← hN₃s, h, subgroupOf_self]
    obtain ⟨e⟩ := hD.iso
    have : Subsingleton (Kbar K) := by
      unfold Kbar
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 : Nat.card (Kbar K) = 1 := Nat.card_unique
    rw [Nat.card_congr e.toEquiv, card_psl] at h1
    norm_num at h1

theorem nonempty_kb_equiv (hD : Data278 M H x z Q K) :
    Nonempty (↥(kb H K) ≃* PSL(3, GaloisField 2 2)) := by
  obtain ⟨eK⟩ := hD.iso
  let ψ : ↥K →* ↥(kb H K) := ((barMk ↥H).comp (inclusion hD.K_le)).codRestrict (kb H K)
    (fun k => ⟨inclusion hD.K_le k, mem_subgroupOf.mpr k.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, k', hk', rfl⟩
    exact ⟨⟨k', mem_subgroupOf.mp hk'⟩, Subtype.ext rfl⟩
  have hker : CFSG.pPrimeCore 3 ↥K = ψ.ker := by
    rw [pPrimeCore_eq_inf hD]
    ext k
    rw [mem_subgroupOf, MonoidHom.mem_ker, mem_inf]
    constructor
    · rintro ⟨-, hkD⟩
      exact Subtype.ext ((barMk_eq_one_iff (inclusion hD.K_le k)).mpr hkD)
    · intro h
      exact ⟨k.2, (barMk_eq_one_iff (inclusion hD.K_le k)).mp (congrArg Subtype.val h)⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans eK)⟩

theorem pRank_top_bar (hD : Data278 M H x z Q K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar ↥H)) = 2 := by
  have hsurj : Function.Surjective (barMk ↥H) := QuotientGroup.mk'_surjective _
  have hker : ¬ 3 ∣ Nat.card ↥((⊤ : Subgroup ↥H) ⊓ (barMk ↥H).ker) := by
    rw [top_inf_eq, K2.qs_ker]
    exact K2.qs_not_dvd_core
  rw [← Subgroup.map_top_of_surjective _ hsurj,
    K2.pRank_map_eq_of_coprime_ker _ Nat.prime_three hker,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, hD.rank]

theorem centralizer_kb_eq_bot (hD : Data278 M H x z Q K) :
    centralizer (kb H K : Set (Bar ↥H)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := kb_normal hD.K_le hD.K_normal
  obtain ⟨e⟩ := nonempty_kb_equiv hD
  have hno : ¬ 3 ∣ Nat.card (centralizer (kb H K : Set (Bar ↥H))) := by
    intro h3
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hco : orderOf (c : Bar ↥H) = 3 := by rw [Subgroup.orderOf_coe, hc]
    have hc3 : (c : Bar ↥H) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (c : Bar ↥H)
      rwa [hco] at h
    have hcK : ∀ n ∈ kb H K, n * (c : Bar ↥H) = c * n := fun n hn =>
      mem_centralizer_iff.mp c.2 n hn
    obtain ⟨E, hEK, hEe, hEc⟩ :=
      exists_isElemAbelian_of_le_pRank Nat.prime_three (k := 2) (pRank_of_equiv e).ge
    have hcE : (c : Bar ↥H) ∉ E := by
      intro hcE
      have h1 := eq_one_of_mem_center_of_equiv e (hEK hcE) hcK
      rw [h1, orderOf_one] at hco
      omega
    have hcomm : ∀ y ∈ E, y * (c : Bar ↥H) = c * y := fun y hy => hcK y (hEK hy)
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hc3 hcE hcomm
    have : CFSG.IsElementaryAbelian 3 E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hEe
    have : CFSG.IsElementaryAbelian 3 (zpowers (c : Bar ↥H)) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hc3
    have hF : CFSG.IsElementaryAbelian 3 ↥(E ⊔ zpowers (c : Bar ↥H)) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer
        (zpowers_le.mpr (mem_centralizer_iff.mpr hcomm))
    have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar ↥H)) :=
      le_pRank_of_isElemAbelian Nat.prime_three le_top
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hF)
        (by rw [hcard, hEc]; norm_num)
    rw [pRank_top_bar hD] at h3'
    omega
  have hle : centralizer (kb H K : Set (Bar ↥H)) ≤ primeComplementCore (G := Bar ↥H) 3 :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno⟩
  rw [K2.primeComplementCore_bar] at hle
  exact le_bot_iff.mp hle

theorem card_qb (hD : Data278 M H x z Q K) : Nat.card (qb H Q) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := kb_normal hD.K_le hD.K_normal
  obtain ⟨e⟩ := nonempty_kb_equiv hD
  have hQH := hD.syl.le
  have hQp := hD.syl.isPGroup
  have hQ'p : IsPGroup 3 (Q.subgroupOf H) := hQp.comap_subtype
  have hcardQ : Nat.card (qb H Q) = Nat.card Q := by
    rw [K2.qs_card_map hQ'p le_rfl]
    exact Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv
  have hinj : Function.Injective
      (MulAut.conjNormal : Bar ↥H →* MulAut ↥(kb H K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ centralizer (kb H K : Set (Bar ↥H)) := by
      rw [mem_centralizer_iff]
      intro h hh
      have h1 : (MulAut.conjNormal g ⟨h, hh⟩ : ↥(kb H K)) = ⟨h, hh⟩ := by
        rw [hg]
        rfl
      have h2 := congrArg Subtype.val h1
      rw [MulAut.conjNormal_apply] at h2
      calc h * g = g * h * g⁻¹ * g := by rw [h2]
        _ = g * h := by group
    rw [centralizer_kb_eq_bot hD, mem_bot] at hc
    exact hc
  have hdvd : Nat.card Q ∣ 241920 := by
    rw [← hcardQ, ← card_mulAut_of_equiv e]
    exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_dvd_of_injective _ hinj)
  rw [hcardQ]
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have h27 := hD.card_ge
  rw [hn] at hdvd h27 ⊢
  have hn3 : 3 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using h27)
  have hn4 : n < 4 := by
    by_contra h4
    have h81 : 3 ^ 4 ∣ 241920 := (Nat.pow_dvd_pow 3 (not_lt.mp h4)).trans hdvd
    norm_num at h81
  rw [show n = 3 by omega]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG
