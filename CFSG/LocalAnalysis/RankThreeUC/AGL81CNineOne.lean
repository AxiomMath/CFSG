module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CReduction
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.CStarGenThree
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.LocalAnalysis.AGL81TheoremC CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup

variable {G : Type} [Group G] [Finite G]

structure CStarSettingGen (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop where
  cstar : CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen G
  maxLocal : rankThreeIsMaxTwoLocal M
  sigma_nonempty : (sigmaM G M).Nonempty

theorem CStarSetting.toGen {M : Subgroup G} (h : CStarSetting G M) : CStarSettingGen G M where
  cstar := CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.cStarGen_of_rankThreeUC h.standing h.uc
  maxLocal := h.maxLocal
  sigma_nonempty := by
    obtain ⟨p, hp, -⟩ := h.witness
    exact ⟨p, hp⟩

theorem CStarSettingGen.le_of_two_le_pRank {M : Subgroup G} (hC : CStarSettingGen G M) {p : ℕ}
    (hp : p ∈ sigmaM G M) {Q : Subgroup G} (hQM : Q ≤ M) (hQ : 2 ≤ CFSG.Open.pRank p Q)
    {H : Subgroup G} (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  haveI : Fact p.Prime := ⟨sigmaA_prime p hp.1⟩
  obtain ⟨E, hEQ, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) hQ
  exact hC.cstar.embed p hp.1 M hC.maxLocal E (hEQ.trans hQM) (elementary_isPGroup p E hE)
    (CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt le_rfl hE hEc) H hH
    (hEQ.trans hQH)

theorem CStarSettingGen.theoremE {M : Subgroup G} (hC : CStarSettingGen G M) {p : ℕ}
    (hp : p ∈ sigmaM G M) {H : Subgroup G} (hH : IsTwoLocal H)
    (h : 1 < CFSG.Open.pRank p (H ⊓ M)) : H ≤ M :=
  hC.le_of_two_le_pRank hp inf_le_right h hH inf_le_left

theorem three_le_pRank_sylow_of_mem_sigmaA {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (S : Sylow p G) : 3 ≤ CFSG.Open.pRank p (S : Subgroup G) := by
  obtain ⟨S₀, h⟩ := exists_sylow_rank_at_least_three p (sigmaA_prime p hp)
    (CFSG.LocalAnalysis.AGL81TheoremCD.three_le_pRank_top_of_mem_sigmaA hp)
  rwa [sylow_pRank_eq p (sigmaA_prime p hp) S₀ S] at h

theorem CStarSettingGen.normalizer_le_of_two_le_pRank {M : Subgroup G}
    (hC : CStarSettingGen G M) {p : ℕ} (hp : p ∈ sigmaM G M) {R : Subgroup G} (hRM : R ≤ M)
    (hR : 2 ≤ CFSG.Open.pRank p R) : normalizer (R : Set G) ≤ M :=
  normalizer_le_of_mem_uniqueSet hC.maxLocal
    (mem_uniqueSet_of_forall hC.maxLocal hRM fun H hH hRH =>
      (hH.2 M hC.maxLocal.1 (hC.le_of_two_le_pRank hp hRM hR hH.1 hRH)).symm)

namespace QSet

variable {M : Subgroup G} {p : ℕ} {Q : Subgroup G}

theorem prime_of_mem (hQ : Q ∈ QSet M p) : p.Prime :=
  (mem_QSet_iff.mp hQ).1

theorem ne_two_of_mem (hQ : Q ∈ QSet M p) : p ≠ 2 :=
  (mem_QSet_iff.mp hQ).2.1

theorem le_of_mem (hQ : Q ∈ QSet M p) : Q ≤ M :=
  (mem_QSet_iff.mp hQ).2.2.1

theorem isPGroup_of_mem (hQ : Q ∈ QSet M p) : IsPGroup p Q :=
  (mem_QSet_iff.mp hQ).2.2.2.1

theorem two_le_pRank_of_mem (hQ : Q ∈ QSet M p) : 2 ≤ CFSG.Open.pRank p Q := by
  rcases (mem_QSet_iff.mp hQ).2.2.2.2 with h | ⟨E, hEQ, hE, hEc, -⟩
  · exact h.2.le
  · exact CFSG.SectionRank.le_pRank (prime_of_mem hQ).one_lt hEQ hE hEc

theorem of_le (hQ : Q ∈ QSet M p) {R : Subgroup G} (hQR : Q ≤ R) (hRM : R ≤ M)
    (hR : IsPGroup p R) : R ∈ QSet M p := by
  obtain ⟨hp, hp2, -, -, h⟩ := mem_QSet_iff.mp hQ
  refine mem_QSet_iff.mpr ⟨hp, hp2, hRM, hR, ?_⟩
  rcases h with ⟨hσ, h3⟩ | ⟨E, hEQ, hE⟩
  · exact Or.inl ⟨hσ, h3.trans_le (pRank_mono p hp.one_lt hQR)⟩
  · exact Or.inr ⟨E, hEQ.trans hQR, hE⟩

theorem map_conj (hQ : Q ∈ QSet M p) {x : G} (hx : x ∈ M) :
    Q.map (MulAut.conj x).toMonoidHom ∈ QSet M p := by
  obtain ⟨hp, hp2, hQM, hQp, h⟩ := mem_QSet_iff.mp hQ
  have hconj : ∀ {Y : Subgroup G}, Y ≤ M → Y.map (MulAut.conj x).toMonoidHom ≤ M := by
    rintro Y hY _ ⟨y, hy, rfl⟩
    simpa using M.mul_mem (M.mul_mem hx (hY hy)) (M.inv_mem hx)
  refine mem_QSet_iff.mpr ⟨hp, hp2, hconj hQM, hQp.map _, ?_⟩
  rcases h with ⟨hσ, h3⟩ | ⟨E, hEQ, hE, hEc, hΓ⟩
  · refine Or.inl ⟨hσ, ?_⟩
    rwa [pRank_map_automorphism p hp.one_lt Q (MulAut.conj x)]
  · refine Or.inr ⟨E.map (MulAut.conj x).toMonoidHom, Subgroup.map_mono hEQ,
      CFSG.Open.IsElemAbelian.map hE _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hEc]
    · rw [← gamma_map_automorphism 1 p hp.one_lt E (MulAut.conj x)]
      exact hconj hΓ

end QSet

structure NineSettingGen (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (Q H E : Subgroup G) (k : ℕ) : Prop where
  setting : CStarSettingGen G M
  mem_Q : Q ∈ QSet M p
  mem_H : H ∈ HFam M Q
  stdE : IsStdE p k M Q E

structure NineSetting (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (Q H E : Subgroup G) (k : ℕ) : Prop where
  setting : CStarSetting G M
  mem_Q : Q ∈ QSet M p
  mem_H : H ∈ HFam M Q
  stdE : IsStdE p k M Q E

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem toGen (h : NineSetting G M p Q H E k) : NineSettingGen G M p Q H E k where
  setting := h.setting.toGen
  mem_Q := h.mem_Q
  mem_H := h.mem_H
  stdE := h.stdE

end NineSetting

theorem nineSetting_iff_gen {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ} :
    NineSetting G M p Q H E k ↔ CStarSetting G M ∧ NineSettingGen G M p Q H E k := by
  constructor
  · intro h
    exact ⟨h.setting, h.toGen⟩
  · rintro ⟨hS, h⟩
    exact ⟨hS, h.mem_Q, h.mem_H, h.stdE⟩

structure NineCore (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H E : Subgroup G)
    (k : ℕ) : Prop where
  standing : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G
  maxLocal : rankThreeIsMaxTwoLocal M
  prime : p.Prime
  ne_two : p ≠ 2
  Q_le_M : Q ≤ M
  isPGroup : IsPGroup p Q
  mem_H : H ∈ HFam M Q
  stdE : IsStdE p k M Q E

namespace NineSettingGen

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem toCore (h : NineSettingGen G M p Q H E k) : NineCore G M p Q H E k where
  standing := h.setting.cstar.toStandingGen
  maxLocal := h.setting.maxLocal
  prime := QSet.prime_of_mem h.mem_Q
  ne_two := QSet.ne_two_of_mem h.mem_Q
  Q_le_M := QSet.le_of_mem h.mem_Q
  isPGroup := QSet.isPGroup_of_mem h.mem_Q
  mem_H := h.mem_H
  stdE := h.stdE

end NineSettingGen

namespace NineCore

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem Q_le_H (h : NineCore G M p Q H E k) : Q ≤ H :=
  h.mem_H.2.1

theorem not_le (h : NineCore G M p Q H E k) : ¬ H ≤ M :=
  h.mem_H.2.2

theorem ne_top (h : NineCore G M p Q H E k) : H ≠ ⊤ :=
  h.mem_H.1

theorem k_two_le (h : NineCore G M p Q H E k) : 2 ≤ k := by
  rcases h.stdE.1 with rfl | rfl <;> omega

theorem relPPrimeCore_le (h : NineCore G M p Q H E k) : relPPrimeCore p H ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hk, hEQ, hE, hEc, hΓ⟩ := h.stdE
  have hcard : p ^ (k - 1 + 1) ≤ Nat.card E := by
    rcases hk with rfl | rfl <;> simp [hEc]
  exact relPPrimeCore_le_of_glbCore_le hE hcard (hEQ.trans h.Q_le_H) hΓ

end NineCore

namespace NineSettingGen

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem prime (h : NineSettingGen G M p Q H E k) : p.Prime :=
  h.toCore.prime

theorem ne_two (h : NineSettingGen G M p Q H E k) : p ≠ 2 :=
  h.toCore.ne_two

theorem Q_le_M (h : NineSettingGen G M p Q H E k) : Q ≤ M :=
  h.toCore.Q_le_M

theorem Q_le_H (h : NineSettingGen G M p Q H E k) : Q ≤ H :=
  h.toCore.Q_le_H

theorem not_le (h : NineSettingGen G M p Q H E k) : ¬ H ≤ M :=
  h.toCore.not_le

theorem ne_top (h : NineSettingGen G M p Q H E k) : H ≠ ⊤ :=
  h.toCore.ne_top

theorem relPPrimeCore_le (h : NineSettingGen G M p Q H E k) : relPPrimeCore p H ≤ M :=
  h.toCore.relPPrimeCore_le

private theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K U : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hU : IsPGroup p U) (hUK : U ≤ K) :
    ∃ x ∈ K, U.map (MulAut.conj x).toMonoidHom ≤ P := by
  classical
  obtain ⟨S, hSP⟩ := hP
  obtain ⟨S', hS'⟩ := (hU.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨((m⁻¹ : K) : G), (m⁻¹).2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h1 : (⟨t, hUK ht⟩ : K) ∈ (S' : Subgroup K) := hS' (Subgroup.mem_subgroupOf.mpr ht)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨y, hy, hyt⟩ := h1
  have hyt' : (m : G) * (y : G) * (m : G)⁻¹ = t := by
    have := congrArg Subtype.val hyt
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hyP : (y : G) ∈ P := by
    rw [← hSP]
    exact ⟨y, hy, rfl⟩
  have : (MulAut.conj ((m⁻¹ : K) : G)).toMonoidHom t = (y : G) := by
    rw [← hyt']
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hyP

theorem isSylowOf_of_isSylowOf_inf (h : NineSettingGen G M p Q H E k) (hp : p ∈ sigmaM G M)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf p P H ∧ P ∈ QSet M p := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨x, hx, hQx⟩ := exists_conj_le_of_isSylowOf hP (QSet.isPGroup_of_mem h.mem_Q)
    (le_inf h.Q_le_H h.Q_le_M)
  have hPQ : P ∈ QSet M p :=
    QSet.of_le (QSet.map_conj h.mem_Q hx.2) hQx (hP.le.trans inf_le_right) hP.isPGroup
  have hNorm : ∀ U : Subgroup G, P ≤ U → U ≤ M → IsPGroup p U →
      normalizer (U : Set G) ≤ M := fun U hPU hUM _ =>
    h.setting.normalizer_le_of_two_le_pRank hp hUM
      ((QSet.two_le_pRank_of_mem hPQ).trans (pRank_mono p h.prime.one_lt hPU))
  obtain ⟨T, hPT, hTH, hTM, hTp, hmax⟩ := exists_maxPSubgroup_of_normalizer_le
    (QSet.isPGroup_of_mem hPQ) (hP.le.trans inf_le_left) (QSet.le_of_mem hPQ) hNorm
  have hTP : T = P := hP.eq_of_le hPT (le_inf hTH hTM) hTp
  obtain ⟨S, hS⟩ := ((QSet.isPGroup_of_mem hPQ).comap_subtype (K := H)).exists_le_sylow
  have hSp : IsPGroup p (S.map H.subtype) := S.isPGroup'.map H.subtype
  have hPS : P ≤ (S : Subgroup H).map H.subtype := fun t ht =>
    ⟨⟨t, hP.le.trans inf_le_left ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hSeq : (S : Subgroup H).map H.subtype = T :=
    hmax _ (Subgroup.map_subtype_le _) hSp (hTP ▸ hPS)
  exact ⟨⟨S, hSeq.trans hTP⟩, hPQ⟩

end NineSettingGen

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem prime (h : NineSetting G M p Q H E k) : p.Prime :=
  QSet.prime_of_mem h.mem_Q

theorem ne_two (h : NineSetting G M p Q H E k) : p ≠ 2 :=
  QSet.ne_two_of_mem h.mem_Q

theorem Q_le_M (h : NineSetting G M p Q H E k) : Q ≤ M :=
  QSet.le_of_mem h.mem_Q

theorem Q_le_H (h : NineSetting G M p Q H E k) : Q ≤ H :=
  h.mem_H.2.1

theorem not_le (h : NineSetting G M p Q H E k) : ¬ H ≤ M :=
  h.mem_H.2.2

theorem ne_top (h : NineSetting G M p Q H E k) : H ≠ ⊤ :=
  h.mem_H.1

theorem k_two_le (h : NineSetting G M p Q H E k) : 2 ≤ k := by
  rcases h.stdE.1 with rfl | rfl <;> omega

theorem mem_muSet (h : NineSetting G M p Q H E k) : p ∈ muSet M := by
  refine ⟨h.prime, h.ne_two, ?_, Q, h.mem_Q, H, h.mem_H⟩
  obtain ⟨-, hEQ, -, hEc, -⟩ := h.stdE
  have h1 : Nat.card E ∣ Nat.card M := Subgroup.card_dvd_of_le (hEQ.trans h.Q_le_M)
  rw [hEc] at h1
  exact (dvd_pow_self p (by have := h.k_two_le; omega)).trans h1

theorem relPPrimeCore_le (h : NineSetting G M p Q H E k) : relPPrimeCore p H ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hk, hEQ, hE, hEc, hΓ⟩ := h.stdE
  have hcard : p ^ (k - 1 + 1) ≤ Nat.card E := by
    rcases hk with rfl | rfl <;> simp [hEc]
  exact relPPrimeCore_le_of_glbCore_le hE hcard (hEQ.trans h.Q_le_H) hΓ

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
