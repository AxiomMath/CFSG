module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ICommon
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Inv
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Y
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Faith
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z b : G}
  {H S K : Subgroup G} {f : ↥K →* GL32}

omit [Finite G] in
theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {g : G}
    (h1 : g ∈ normalizer (H₁ : Set G)) (h2 : g ∈ normalizer (H₂ : Set G)) :
    g ∈ normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
  rw [map_commutator, h1, h2]

theorem inf_centralizer_le_core (hyp : Hyp P M x z H S) {U W : Subgroup G}
    (hOU : pCoreOf 2 H ≤ U) : W ⊓ centralizer (U : Set G) ≤ pCoreOf 2 H := by
  intro w hw
  have hwO : w ∈ centralizer (pCoreOf 2 H : Set G) := centralizer_le hOU (mem_inf.1 hw).2
  have hwH : w ∈ H :=
    hyp.optimal.eq_normalizer.ge (centralizer_le_normalizer _ hwO)
  exact charTwo_H hyp ⟨hwH, hwO⟩

theorem L32Data.campbell_hyp (h2813 : KFactLemma2813) (hOF : OmegaFalse G) (hCT : CoreTwo G)
    (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (h : L32Data M (zpowers x ⊔ zpowers z) H S K z b f) :
    ∃ R : Subgroup G, S ≤ R ∧ R ≤ K ⊔ pCoreOf 2 H ∧ IsPGroup 2 R ∧
      ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index ∧
      (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
        normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα := h618.alpha
  obtain ⟨t, htX, htS, htz, htb, n, htn⟩ := h.exists_t
  obtain ⟨hSR, hRX, hR2, hRi⟩ := h.sylow_of_t htX htS htz htn
  refine ⟨zpowers t ⊔ S, hSR, hRX, hR2, hRi, ?_⟩
  by_contra hfail
  obtain ⟨k1, k2, k3⟩ := h.k2813 h2813 hSR hRX hR2 hRi
  have htM : t ∈ M := normalizer_S_le_M hyp htS
  have htB : t ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
    rw [h.B_eq]
    refine CFSG.Goldschmidt.G310.le_normalizer_sup (A := zpowers t) (zpowers_le.2 ?_)
      (zpowers_le.2 ?_) (mem_zpowers t)
    · rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change zpowers (t * z * t⁻¹) = zpowers z
      rw [htz, zpowers_inv]
    · refine centralizer_le_normalizer _ ?_
      rw [centralizer_zpowers_eq]
      exact mem_centralizer_singleton_iff.2 htb
  obtain ⟨T, Y, hTsyl, hST, hBT, htT, hY3, hYM, hBY, hYT, hzc, hcen, hYr, hY27⟩ :=
    exists_T_Y hyp hα htM htB htS htn
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hz3 : z ^ 3 = 1 := z_pow_three hyp
  have hz1 : z ≠ 1 := z_ne_one hyp
  have hzY : z ∈ Y := hBY (mem_sup_right (mem_zpowers z))
  have hTV : omegaCenter T ≤ omegaCenter S :=
    omegaCenter_le_omegaCenter hST (fun w hw =>
      core_le_S hyp (inf_centralizer_le_core hyp (core_le_S hyp) hw))
  have hYT₁ : Y ≤ normalizer ((omegaCenter T : Subgroup G) : Set G) :=
    hYT.trans (normalizer_le_normalizer_omegaCenter T)
  have hcom : ∀ v ∈ omegaCenter T, z * v = v * z :=
    commutes_of_card_commutator_le hY3 hY27 hzY hz1 hz3 hzc hcen (isElemAbelian_omegaCenter T)
      hYT₁ hTV k1
  have hBT₁ : zpowers x ⊔ zpowers z ≤ normalizer ((omegaCenter T : Subgroup G) : Set G) :=
    hBT.trans (normalizer_le_normalizer_omegaCenter T)
  have hTne : T ≠ ⊥ := fun h0 => S_ne_bot hyp (le_bot_iff.1 (h0 ▸ hST))
  have hne : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter (zpowers t ⊔ S) : Subgroup G) : Set G) ≠
      (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) := fun he => hfail (he.le.trans inf_le_right)
  by_cases hXc : K ⊔ pCoreOf 2 H ≤
      centralizer ((omegaCenter (zpowers t ⊔ S) : Subgroup G) : Set G)
  swap
  ·
    have hVX := k2 hne hXc
    have hKT₁ : K ≤ normalizer ((omegaCenter T : Subgroup G) : Set G) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      intro k hk
      rw [mem_centralizer_iff]
      intro v hv
      exact hVX v (hTV hv) (hcom v hv).symm k (mem_sup_left hk)
    have hN : IsTwoLocal (normalizer ((omegaCenter T : Subgroup G) : Set G)) :=
      ⟨omegaCenter T, omegaCenter_ne_bot hT2 hTne, hT2.to_le (omegaCenter_le T), rfl⟩
    have hrank : 3 ≤ CFSG.Open.pRank 3 (normalizer ((omegaCenter T : Subgroup G) : Set G) ⊓ M) := by
      have := pRank_mono 3 Nat.prime_three.one_lt (le_inf hYT₁ hYM)
      omega
    have hNM := le_of_three_le_pRank_inf hyp.d1 hyp.situation.mem_sigmaA
      hyp.situation.isCoreMaxLocal hN hrank
    exact h618.comp.not_le (hKT₁.trans hNM)
  have k3' := k3 hXc
  suffices key : ∃ T₀ Q : Subgroup G, T₀ ≤ omegaCenter T ∧ T₀ ≠ ⊥ ∧
      K ≤ normalizer (T₀ : Set G) ∧ zpowers x ⊔ zpowers z ≤ normalizer (T₀ : Set G) ∧
      Q ≤ normalizer (T₀ : Set G) ∧ zpowers x ⊔ zpowers z ≤ Q ∧ Q ≤ Y ∧
      ∃ q ∈ Q, q ^ 3 = 1 ∧ q ∉ zpowers x ⊔ zpowers z by
    obtain ⟨T₀, Q, hT₀T, hT₀1, hKN, hBN, hQN, hBQ, hQY, q, hqQ, hq3, hqB⟩ := key
    have hT₀2 : IsPGroup 2 T₀ := hT2.to_le (hT₀T.trans (omegaCenter_le T))
    have hN : IsTwoLocal (normalizer (T₀ : Set G)) := ⟨T₀, hT₀1, hT₀2, rfl⟩
    have hNM : ¬ normalizer (T₀ : Set G) ≤ M := fun hle => h618.comp.not_le (hKN.trans hle)
    have hSN : S ≤ normalizer (T₀ : Set G) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      exact le_centralizer_iff.2 ((hT₀T.trans hTV).trans (omegaCenter_le_centralizer S))
    have hLP := localPair_of_le hyp hN hBN hNM hSN
    have hsit := sit_of_hyp hyp
    have hcore := hCT P M x z hsit hα _ S hLP
    exact hqB (hOF P M x z hsit _ S hLP hcore Q hQN (hY3.to_le hQY) hBQ q hqQ hq3)
  by_cases hBc : ∀ v ∈ omegaCenter T, ∀ y ∈ zpowers x ⊔ zpowers z, v * y = y * v
  ·
    set R := zpowers t ⊔ S
    have hRT : R ≤ normalizer (T : Set G) :=
      sup_le (zpowers_le.2 htT) (hST.trans le_normalizer)
    have hRT2 : IsPGroup 2 ↥(R ⊔ T) := IsPGroup.to_sup_of_normal_right' hR2 hT2 hRT
    have hRTne : R ⊔ T ≠ ⊥ := fun h0 => hTne (le_bot_iff.1 (h0 ▸ le_sup_right))
    have hOR : pCoreOf 2 H ≤ R := (core_le_S hyp).trans hSR
    have hOT : pCoreOf 2 H ≤ T := (core_le_S hyp).trans hST
    have hW : omegaCenter (R ⊔ T) ≤ omegaCenter T ⊓ omegaCenter R := le_inf
      (omegaCenter_le_omegaCenter le_sup_right (fun w hw =>
        hOT (inf_centralizer_le_core hyp hOT hw)))
      (omegaCenter_le_omegaCenter le_sup_left (fun w hw =>
        hOR (inf_centralizer_le_core hyp hOR hw)))
    have hBC : zpowers x ⊔ zpowers z ≤ centralizer ((omegaCenter T : Subgroup G) : Set G) :=
      fun y hy => mem_centralizer_iff.2 fun v hv => hBc v hv y hy
    have hYQ : Y ≤ normalizer ((Y ⊓ centralizer ((omegaCenter T : Subgroup G) : Set G) :
        Subgroup G) : Set G) :=
      CFSG.Goldschmidt.G310.le_normalizer_inf le_normalizer
        (hYT₁.trans (CFSG.Goldschmidt.G310.normalizer_le_normalizer_centralizer' _))
    have hBQ : zpowers x ⊔ zpowers z ≤ Y ⊓ centralizer ((omegaCenter T : Subgroup G) : Set G) :=
      le_inf hBY hBC
    have hCT₀ : centralizer ((omegaCenter T : Subgroup G) : Set G) ≤
        normalizer ((omegaCenter T ⊓ omegaCenter R : Subgroup G) : Set G) :=
      (centralizer_le (show ((omegaCenter T ⊓ omegaCenter R : Subgroup G) : Set G) ⊆
        (omegaCenter T : Set G) from fun a ha => ha.1)).trans (centralizer_le_normalizer _)
    refine ⟨omegaCenter T ⊓ omegaCenter R, Y ⊓ centralizer ((omegaCenter T : Subgroup G) : Set G),
      inf_le_left, fun h0 => omegaCenter_ne_bot hRT2 hRTne (le_bot_iff.1 (h0 ▸ hW)), ?_,
      hBC.trans hCT₀, inf_le_right.trans hCT₀, hBQ, inf_le_left,
      exists_three_of_le_normalizer hyp hα hYr hBQ hYQ⟩
    refine le_trans ?_ (centralizer_le_normalizer _)
    exact (le_sup_left.trans hXc).trans (centralizer_le (show
      ((omegaCenter T ⊓ omegaCenter R : Subgroup G) : Set G) ⊆ (omegaCenter R : Set G) from
        fun a ha => ha.2))
  ·
    push Not at hBc
    obtain ⟨v₀, hv₀, y₀, hy₀, hvy⟩ := hBc
    set T₀ : Subgroup G := ⁅omegaCenter T, zpowers x ⊔ zpowers z⁆
    have hT₀T : T₀ ≤ omegaCenter T := by
      refine commutator_le.2 fun v hv y hy => ?_
      have h1 : y * v⁻¹ * y⁻¹ ∈ omegaCenter T :=
        (mem_normalizer_iff.1 (hBT₁ hy) v⁻¹).1 (inv_mem hv)
      have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hv h1
    have hT₀1 : T₀ ≠ ⊥ := by
      intro h0
      have hmem : ⁅v₀, y₀⁆ ∈ T₀ := commutator_mem_commutator hv₀ hy₀
      rw [h0, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hvy hmem
    have hKC : K ≤ centralizer (T₀ : Set G) := by
      refine le_centralizer_iff.2 (commutator_le.2 fun v hv y hy => ?_)
      rw [mem_centralizer_iff]
      intro k hk
      have := k3' v (hTV hv) (hcom v hv).symm y hy k (mem_sup_left hk)
      rw [commutatorElement_def]
      exact this.symm
    have hQ : Y ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤
        normalizer (T₀ : Set G) := fun g hg =>
      mem_normalizer_commutator (hYT₁ hg.1) hg.2
    refine ⟨T₀, Y ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G), hT₀T, hT₀1,
      hKC.trans (centralizer_le_normalizer _),
      fun g hg => mem_normalizer_commutator (hBT₁ hg) (le_normalizer hg), hQ,
      le_inf hBY le_normalizer, inf_le_left, exists_three_normalizer hyp hα hY3 hYr hBY⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
