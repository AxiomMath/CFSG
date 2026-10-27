module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CStrongEmb
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeUC.Focal
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_pPrimeCore {M H : Subgroup G} {p d : ℕ} (hp : p.Prime)
    (hcore : relPPrimeCore p H ≤ M) (hd : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)) :
    ¬ d ∣ Nat.card (CFSG.pPrimeCore p ↥H) := by
  rw [← Subgroup.card_map_of_injective (K := CFSG.pPrimeCore p ↥H) H.subtype_injective,
    ← relPPrimeCore_eq_map hp H]
  exact fun hdvd => hd (hdvd.trans (Subgroup.card_dvd_of_le (le_inf (relPPrimeCore_le H) hcore)))

theorem card_barInf_dvd (p : ℕ) (M H : Subgroup G) :
    Nat.card (barInf p M H) ∣ Nat.card (H ⊓ M : Subgroup G) := by
  calc Nat.card (barInf p M H)
      = Nat.card (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
        rfl
    _ ∣ Nat.card ((H ⊓ M).subgroupOf H) :=
        Subgroup.card_map_dvd ((H ⊓ M).subgroupOf H) (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    _ = Nat.card (H ⊓ M : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem pRank_le_pRank_map_mk' {A : Type*} [Group A] [Finite A] {d : ℕ} (hd : d.Prime)
    (N : Subgroup A) [N.Normal] (hN : ¬ d ∣ Nat.card N) {P : Subgroup A} (hP : IsPGroup d P) :
    CFSG.pRank d ↥P ≤ CFSG.pRank d ↥(P.map (QuotientGroup.mk' N)) := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have hdisj : Disjoint P N := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [ha]
    exact ((hd.coprime_iff_not_dvd).mpr hN).pow_left a
  let f : ↥P →* A ⧸ N := (QuotientGroup.mk' N).comp P.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : A) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (x : A)).mp (by simpa [f] using hx)
    have hbot : (x : A) ∈ (⊥ : Subgroup A) := hdisj.le_bot ⟨x.2, hxN⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hrange : f.range = P.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hxP, rfl⟩
      exact ⟨⟨x, hxP⟩, rfl⟩
  have hEq : CFSG.pRank d ↥P = CFSG.pRank d ↥(P.map (QuotientGroup.mk' N)) := by
    calc CFSG.pRank d ↥P
        = CFSG.pRank d ↥f.range :=
          CFSG.pRank_congr_of_mulEquiv (MonoidHom.ofInjective hf) d
      _ = CFSG.pRank d ↥(P.map (QuotientGroup.mk' N)) :=
          CFSG.pRank_congr_of_mulEquiv (MulEquiv.subgroupCongr hrange) d
  exact hEq.le

theorem commutator_le_map_subtype_of_index_eq {H : Subgroup G} {N₀ : Subgroup ↥H} [N₀.Normal]
    {d : ℕ} (hd : d.Prime) (h : N₀.index = d) : ⁅H, H⁆ ≤ N₀.map H.subtype := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  haveI : Fact d.Prime := ⟨hd⟩
  let a : ↥H := ⟨x, hx⟩
  let b : ↥H := ⟨y, hy⟩
  let π : ↥H →* ↥H ⧸ N₀ := QuotientGroup.mk' N₀
  have hcab : ⁅a, b⁆ ∈ N₀ := by
    have hcard : Nat.card (↥H ⧸ N₀) = d := by
      rw [← Subgroup.index_eq_card, h]
    haveI : IsCyclic (↥H ⧸ N₀) := isCyclic_of_prime_card hcard
    have hcomm : ⁅π a, π b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      letI : CommGroup (↥H ⧸ N₀) := IsCyclic.commGroup
      exact mul_comm (π a) (π b)
    have h1 : π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, hcomm]
    exact (QuotientGroup.eq_one_iff (N := N₀) ⁅a, b⁆).mp h1
  exact ⟨⁅a, b⁆, hcab, by simp [map_commutatorElement, a, b]⟩

theorem relIndex_map_subtype {H : Subgroup G} (N₀ : Subgroup ↥H) :
    (N₀.map H.subtype).relIndex H = N₀.index := by
  show ((N₀.map H.subtype).comap H.subtype).index = N₀.index
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective N₀]

namespace NineSettingGen

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isKGroup_quotient (h : NineSettingGen G M p Q H E k) (q : ℕ) :
    CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore q ↥H) :=
  (h.setting.cstar.kProper.isKGroup H h.ne_top).quotient (CFSG.pPrimeCore q ↥H)

theorem pRank_quotient_le_three (h : NineSettingGen G M 3 Q H E k) (hH : IsTwoLocal H)
    (h3 : 3 ∉ sigmaM G M) :
    CFSG.pRank 3 ↥(⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have h3A : 3 ∉ rankThreeSigmaA G := fun hσ =>
    h3 ⟨hσ, (QSet.two_le_pRank_of_mem h.mem_Q).trans
      (pRank_mono 3 Nat.prime_three.one_lt (QSet.le_of_mem h.mem_Q))⟩
  calc CFSG.pRank 3 ↥(⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
      = CFSG.pRank 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
        CFSG.pRank_congr_of_mulEquiv Subgroup.topEquiv 3
    _ = CFSG.pRank 3 ↥H :=
        CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _ hN
    _ = CFSG.Open.pRank 3 H := CFSG.SectionRank.pRank_coe_eq_openPRank 3 H
    _ ≤ 3 := h.setting.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h3A hH

theorem not_mem_of_map_conj (h : NineSettingGen G M p Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) : g ∉ M := by
  intro hgM
  apply h.not_le
  rw [hg]
  rintro y ⟨x, hx, rfl⟩
  simpa [MulAut.conj_apply] using M.mul_mem (M.mul_mem hgM hx) (M.inv_mem hgM)

theorem not_dvd_card_inf (h : NineSettingGen G M p Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) {d : ℕ}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) :
    ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := by
  have hgM : g ∉ M := h.not_mem_of_map_conj hg
  rw [hg, inf_comm]
  exact hM.not_dvd_card_inf_conj hgM

theorem not_dvd_card_barInf (h : NineSettingGen G M p Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) {d : ℕ}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) :
    ¬ d ∣ Nat.card (barInf p M H) :=
  fun hdvd => h.not_dvd_card_inf hg hM (hdvd.trans (card_barInf_dvd p M H))

theorem no_normal_index (h : NineSettingGen G M p Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) {d : ℕ} (hd : d.Prime)
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) (hperf : commutator G = ⊤) :
    ∀ N : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H), N.Normal → N.index ≠ d := by
  haveI : Fact d.Prime := ⟨hd⟩
  intro N hN hNidx
  set N₀ : Subgroup ↥H := N.comap (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) with hN₀def
  have hN₀ : N₀.Normal := by
    rw [hN₀def]
    exact hN.comap (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
  have hidx : N₀.index = d := by
    rw [hN₀def, Subgroup.index_comap_of_surjective N
      (QuotientGroup.mk'_surjective (N := CFSG.pPrimeCore p ↥H))]
    exact hNidx
  haveI := hN₀
  have hNM : N₀.map H.subtype ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_subtype_le N₀
  have hcomm : ⁅M.map (MulAut.conj g).toMonoidHom, M.map (MulAut.conj g).toMonoidHom⁆ ≤
      N₀.map H.subtype := by
    rw [← hg]
    exact commutator_le_map_subtype_of_index_eq hd hidx
  have hnd := hM.map_not_dvd_relIndex_of_commutator_le hperf g hNM hcomm
  rw [← hg, relIndex_map_subtype] at hnd
  exact hnd (by rw [hidx])

theorem exists_sylow_image (h : NineSettingGen G M p Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) {d : ℕ} (hd : d ∈ sigmaM G M)
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) :
    ∃ W : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H), IsPGroup d W ∧ 3 ≤ CFSG.pRank d ↥W := by
  have hdp : d.Prime := sigmaA_prime d hd.1
  haveI : Fact d.Prime := ⟨hdp⟩
  obtain ⟨P, hP, hPM'⟩ := (hM.conj g).exists_isSylowOf_le
  have hPH : P ≤ H := hg.symm ▸ hPM'
  let S : Sylow d G := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have h3P : 3 ≤ CFSG.Open.pRank d P :=
    three_le_pRank_sylow_of_mem_sigmaA hd.1 S
  have h1 : 3 ≤ CFSG.pRank d ↥P := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank d P]
    exact h3P
  have hN : ¬ d ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    not_dvd_card_pPrimeCore h.prime h.relPPrimeCore_le (h.not_dvd_card_inf hg hM)
  let P' : Subgroup ↥H := P.subgroupOf H
  have hP' : IsPGroup d P' := hP.2.1.comap_subtype (K := H)
  refine ⟨P'.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)), hP'.map _, ?_⟩
  calc 3 ≤ CFSG.pRank d ↥P := h1
    _ = CFSG.pRank d ↥P' :=
        (CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPH) d).symm
    _ ≤ CFSG.pRank d ↥(P'.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
        pRank_le_pRank_map_mk' hdp (CFSG.pPrimeCore p ↥H) hN hP'

theorem dEmbConfig (h : NineSettingGen G M 3 Q H E k) {g : G}
    (hg : H = M.map (MulAut.conj g).toMonoidHom) {d : ℕ} (hd : d ∈ sigmaM G M)
    (h3 : 3 ∉ sigmaM G M) (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) :
    ∃ W : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H),
      DEmbConfig (↥H ⧸ CFSG.pPrimeCore 3 ↥H) (barInf 3 M H) d W := by
  have hdp : d.Prime := sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := sigmaA_odd d hd.1
  have hd3 : d ≠ 3 := fun hd3eq => h3 (hd3eq ▸ hd)
  have hd4 : d ≠ 4 := fun hd4eq => by rw [hd4eq] at hdp; norm_num at hdp
  have hd5 : 5 ≤ d := by
    have h2 : 2 ≤ d := hdp.two_le
    omega
  have hH2 : IsTwoLocal H :=
    hg.symm ▸ (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map
      h.setting.maxLocal (MulAut.conj g)).1
  obtain ⟨W, hWp, hW3⟩ := h.exists_sylow_image hg hd hM
  haveI : IsSimpleGroup G := h.setting.cstar.simple
  have hperf : commutator G = ⊤ := commutator_eq_top_of_standing h.setting.cstar.nonab
  refine ⟨W, ?_⟩
  exact ⟨hdp, hd5, h.isKGroup_quotient 3, CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three,
    h.pRank_quotient_le_three hH2 h3, h.not_dvd_card_barInf hg hM, hWp, hW3,
    h.no_normal_index hg hdp hM hperf⟩

private theorem zComponentData_mk {M Q H E : Subgroup G}
    (hex : ∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧
      ¬ L ≤ barInf 3 M H ∧ (IsL34Type ↥L ∨ IsA11Type ↥L))
    (h6 : {C : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H) |
        CFSG.IsComponent C ∧ ¬ C ≤ barInf 3 M H}.ncard ≤ 2 ∧
      ∀ C₁ C₂ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent C₁ →
        ¬ C₁ ≤ barInf 3 M H → CFSG.IsComponent C₂ → ¬ C₂ ≤ barInf 3 M H → C₁ ≠ C₂ →
          (IsL34Type ↥C₁ ∨ IsA6Type ↥C₁) ∧ (IsL34Type ↥C₂ ∨ IsA6Type ↥C₂))
    (h35 : (∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧
        ¬ L ≤ barInf 3 M H ∧ IsA11Type ↥L) → 5 ∣ Nat.card (barInf 3 M H)) :
    ZComponentData (↥H ⧸ CFSG.pPrimeCore 3 ↥H) (barInf 3 M H) :=
  ⟨hex, h6.1, h6.2, h35⟩

theorem zComponentDataGen (h7 : NineSevenTwoInputGen) (h6 : NineSixInputGen)
    (h35 : ThreeFiveA11InputGen) (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (h3 : 3 ∉ sigmaM G M) (hcore : pCoreOf 2 H ≠ pCoreOf 2 (H ⊓ M)) :
    ZComponentData (↥H ⧸ CFSG.pPrimeCore 3 ↥H) (barInf 3 M H) :=
  zComponentData_mk (Q := Q) (E := E) (h7 G M Q H E h hH2 h3 hcore.symm)
    (h6 G M Q H E h hH2 h3 (h7 G M Q H E h hH2 h3 hcore.symm))
    (h35 G M Q H E h hH2 h3)

end NineSettingGen

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isKGroup_quotient (h : NineSetting G M p Q H E k) (q : ℕ) :
    CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore q ↥H) :=
  (h.setting.standing.kProper.isKGroup H h.ne_top).quotient (CFSG.pPrimeCore q ↥H)

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
