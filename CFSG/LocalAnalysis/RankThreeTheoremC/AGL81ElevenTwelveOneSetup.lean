module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveB (M H Q : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) 3))
    (b : G) : Prop :=
  b ∈ H ⊓ M ∧ b ∈ d1PlusCore 3 H K ∧ orderOf b = 3 ∧
    ¬ Subgroup.centralizer ({b} : Set G) ≤ M ∧ Q ≤ Subgroup.centralizer ({b} : Set G)

variable (G) in
@[expose] def AGL81TwelveSetup : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → IsAltTwoP 3 K → 3 ≤ Open.pRank 3 H →
      ∃ b : G, TwelveB M H Q K b

theorem pRank_mulAut_le_two_of_isAltTwoP {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K) :
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨e⟩ := hK
  have e6 : K ≃* alternatingGroup (Fin 6) := e
  have hZ : Subgroup.center K = ⊥ := by
    have hcen : (Subgroup.center K).map e6.toMonoidHom =
        Subgroup.center (alternatingGroup (Fin 6)) := Subgroup.map_center_eq e6
    rw [alternatingGroup.center_eq_bot (by simp)] at hcen
    exact (Subgroup.map_eq_bot_iff_of_injective _ e6.injective).1 hcen
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer
    Nat.prime_three hZ).trans ?_
  have h1 : Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 2 fun hd => ?_
    have hcard : Nat.card K = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rw [hcard] at hd
    omega
  have h2 : Open.pRank 3
      (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) ≤ 0 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0 fun hd => ?_
    have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four 6 (by omega)
    rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e6).toEquiv] at h4
    have := hd.trans h4
    omega
  omega

theorem three_dvd_card_d1PlusCore {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} [K.Normal] (hA : IsAltTwoP 3 K)
    (h3 : 3 ≤ Open.pRank 3 H) : 3 ∣ Nat.card (d1PlusCore 3 H K) := by
  by_contra hX
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) H
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  let ψ : ↥(E.subgroupOf H) →* MulAut K :=
    (MulAut.conjNormal (H := K)).comp (π.comp (E.subgroupOf H).subtype)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hc : π (e : H) ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun φ : MulAut K => (φ ⟨k, hk⟩ : K).1) he
      simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply,
        MulAut.one_apply] at h1
      have h1' : π (e : H) * k * (π (e : H))⁻¹ = k := h1
      calc k * π (e : H) = (π (e : H) * k * (π (e : H))⁻¹) * π (e : H) := by rw [h1']
        _ = π (e : H) * k := by group
    have hXe : ((e : H) : G) ∈ d1PlusCore 3 H K := ⟨e, hc, rfl⟩
    have heE : ((e : H) : G) ∈ E := e.2
    have h3e : ((e : H) : G) ^ 3 = 1 := hE.2 _ heE
    have hdvd : orderOf ((e : H) : G) ∣ Nat.card (d1PlusCore 3 H K) :=
      Subgroup.orderOf_dvd_natCard _ hXe
    have hdvd3 : orderOf ((e : H) : G) ∣ 3 := orderOf_dvd_of_pow_eq_one h3e
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · have h1 : ((e : H) : G) = 1 := orderOf_eq_one_iff.mp h
      exact Subtype.ext (Subtype.ext h1)
    · rw [h] at hdvd
      exact absurd hdvd hX
  have hcomm : ∀ a b : ↥(E.subgroupOf H), a * b = b * a := by
    intro a b
    have := hE.1
    have h1 := congrArg Subtype.val (mul_comm' (⟨((a : H) : G), a.2⟩ : E) ⟨((b : H) : G), b.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have hpow : ∀ a : ↥(E.subgroupOf H), a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    simpa using hE.2 _ a.2
  have hcardE : Nat.card ↥(E.subgroupOf H) = 3 ^ Open.pRank 3 H := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hcard]
  have hle := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow hcardE ψ
    hinj (H := ⊤) le_top
  have := pRank_mulAut_le_two_of_isAltTwoP hA
  omega

theorem not_centralizer_le_of_mem_d1PlusCore {M H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hKX : ¬ K ≤ d1X0 3 M H) {b : G}
    (hb : b ∈ d1PlusCore 3 H K) (hb3 : orderOf b = 3) :
    ¬ Subgroup.centralizer ({b} : Set G) ≤ M := by
  intro hC
  apply hKX
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  set N := primeComplementCore (G := H) 3 with hN
  have hord : orderOf b₀ = 3 := by rwa [← Subgroup.orderOf_coe]
  have hp : IsPGroup 3 (Subgroup.zpowers b₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hcent := CFSG.LocalAnalysis.RankFourTheoremC.centralizer_singleton_map_mk N
    Nat.prime_three (primeComplementCore_coprime (G := H) 3) hp
  intro k hk
  have hkc : k ∈ Subgroup.centralizer ({QuotientGroup.mk' N b₀} : Set (H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hb₀) k hk
  rw [hcent] at hkc
  obtain ⟨h, hh, rfl⟩ := hkc
  refine ⟨h, ?_, rfl⟩
  show (h : G) ∈ H ⊓ M
  refine ⟨h.2, hC ?_⟩
  have hh' : h ∈ Subgroup.centralizer ({b₀} : Set H) := hh
  show (h : G) ∈ Subgroup.centralizer {(b₀ : G)}
  rw [Subgroup.mem_centralizer_singleton_iff] at hh' ⊢
  exact congrArg Subtype.val hh'

theorem agl81TwelveSetup_of (h9 : AGL81NineCompetitorQ G) : AGL81TwelveSetup G := by
  intro hS P M H Q K hd hA h3
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hK := hd.kbar
  subst hK
  have hn := (h9 (aglGlobal_of_setting hS) 3 P M H (muAt_of_escape hesc) hd.maxH hd.not_le
    (exists_component_of_d1KBar_ne_bot (d1KBar_ne_bot_of_isAltTwoP hA)) Q H hd.base hd.le_H
    hd.maxH hd.not_le hd.le_H (aglCovers_self H _)).1.nineThree
  haveI := hn.normal
  have hQX : Q ≤ Subgroup.normalizer (d1PlusCore 3 H (d1KBar 3 M H) : Set G) :=
    hd.le_H.trans (le_normalizer_d1PlusCore hn.normal)
  obtain ⟨b, hbX, hb3, hbQ⟩ := exists_centralizing_of_three_dvd hd.base.2.1 hQX
    (three_dvd_card_d1PlusCore hA h3)
  refine ⟨b, ⟨Subgroup.map_subtype_le _ hbX, hn.plusCore_le hbX⟩, hbX, hb3,
    not_centralizer_le_of_mem_d1PlusCore hd.not_le_X0 hbX hb3, fun a ha => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hbQ a ha

end CFSG.LocalAnalysis.RankThreeTheoremC
