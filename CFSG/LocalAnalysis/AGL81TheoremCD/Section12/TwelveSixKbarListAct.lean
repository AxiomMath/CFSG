module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAut
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarE27Kit
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKInterSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace KbarList

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem conj_mem (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (k : ↥(kSub p M H)) : (y : G) * k * (y : G)⁻¹ ∈ kSub p M H :=
  (mem_normalizer_iff.mp ((normal_subgroupOf_iff_le_normalizer
    (Section14.kSub_le p M H)).mp hKH y.2) (k : G)).mp k.2

noncomputable def kbarAct (hKH : ((kSub p M H).subgroupOf H).Normal) :
    ↥H →* MulAut (kbarQuot p M H) :=
  (MulAut.mapQuotient (center (modTwoCore (kSub p M H)))).comp (kbarConj hKH)

theorem kbarAct_apply_mk (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (q : modTwoCore (kSub p M H)) :
    kbarAct hKH y (QuotientGroup.mk q) = QuotientGroup.mk (kbarConj hKH y q) :=
  MulAut.mapQuotient_mk _ _ _

theorem kbarAct_mk (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (k : ↥(kSub p M H)) :
    kbarAct hKH y (QuotientGroup.mk (QuotientGroup.mk k)) =
      QuotientGroup.mk (QuotientGroup.mk
        (⟨(y : G) * k * (y : G)⁻¹, conj_mem hKH y k⟩ : ↥(kSub p M H))) := by
  rw [kbarAct_apply_mk, kbarConj_mk]

theorem kbarAct_eq_conj (hKH : ((kSub p M H).subgroupOf H).Normal)
    (k : ↥(kSub p M H)) (hk : (k : G) ∈ H) :
    kbarAct hKH ⟨k, hk⟩ =
      MulAut.conj (QuotientGroup.mk (QuotientGroup.mk k : modTwoCore (kSub p M H)) :
        kbarQuot p M H) := by
  ext q
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
  rw [kbarAct_mk, MulAut.conj_apply]
  rfl

theorem ker_kbarAct_le (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    (kbarAct hKH).ker ≤ (xSub p M H).subgroupOf H := by
  intro y hy
  apply TwelveCtx.ker_kbarConj_le h hKH
  rw [MonoidHom.mem_ker]
  apply CFSG.RankThree.PartTwo.Sec15.F153L3C2.mulAut_eq_one_of_central hK.2.2.1
  intro q
  have h1 : kbarAct hKH y (QuotientGroup.mk q) = QuotientGroup.mk q := by
    rw [MonoidHom.mem_ker.1 hy]
    rfl
  rw [kbarAct_apply_mk] at h1
  have h2 := QuotientGroup.eq_iff_div_mem.1 h1
  rwa [div_eq_mul_inv] at h2

theorem conj_range_le_range (hKH : ((kSub p M H).subgroupOf H).Normal) :
    (MulAut.conj : kbarQuot p M H →* MulAut (kbarQuot p M H)).range ≤ (kbarAct hKH).range := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  exact ⟨⟨k, Section14.kSub_le p M H k.2⟩, kbarAct_eq_conj hKH k _⟩

variable {d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem pRank_three_range_le (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M)
    (hKH : ((kSub p M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    CFSG.Open.pRank 3 (kbarAct hKH).range ≤ 3 := by
  have : Finite (MulAut (kbarQuot p M H)) := MulEquiv.finite_left
  have hX3 := TwelveSixKCtx.not_three_dvd_card_xSub hc D hXM
  have hker : ¬ 3 ∣ Nat.card (kbarAct hKH).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro h3
    apply hX3
    have h1 : Nat.card (kbarAct hKH).ker ∣ Nat.card ((xSub p M H).subgroupOf H) :=
      Subgroup.card_dvd_of_le (ker_kbarAct_le hc.ctx hKH hK)
    rw [Nat.card_congr (subgroupOfEquivOfLe (xSub_le_H p M H)).toEquiv] at h1
    exact h3.trans h1
  have h := CFSG.pRank_map_eq_of_not_dvd_card_ker (kbarAct hKH).rangeRestrict
    (kbarAct hKH).rangeRestrict_surjective Nat.prime_three hker ⊤
  rw [Subgroup.map_top_of_surjective _ (kbarAct hKH).rangeRestrict_surjective,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
  rw [h]
  exact hc.pRank_three_le D

end KbarList

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKbarHyp.exists_cfg_inf (hyp : TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H) (hKH : ((kSub p M H).subgroupOf H).Normal) :
    ∃ (V W₁ W₂ W₃ : Subgroup ↥H) (t₁ t₂ t₃ : ↥H), IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃ ∧
      V ≤ (H ⊓ M).subgroupOf H ∧ t₁ ∈ (H ⊓ M).subgroupOf H ∧ t₂ ∈ (H ⊓ M).subgroupOf H ∧
      t₃ ∈ (H ⊓ M).subgroupOf H ∧ ∀ v ∈ V, KbarList.kbarAct hKH v = 1 → v = 1 := by
  obtain ⟨hc, ⟨D⟩, -, -, -, -, -⟩ := hyp
  have hkerX := KbarList.ker_kbarAct_le hc.ctx hKH hK
  have hVHM : D.V ≤ H ⊓ M := D.V_le.trans (D.sup_le hc.data)
  have hVH : D.V ≤ H := hVHM.trans inf_le_left
  have ht₁ := D.t₁_mem hc.data
  have ht₂ := D.t₂_mem hc.data
  have ht₃ := D.t₃_mem hc.data
  have hVX := hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
    (D.centralizer_le₃ hc) ht₁ ht₂ ht₃
  refine ⟨_, _, _, _, _, _, _, KbarE27.isE27InvConfig_subgroupOf D.cfg hVH ht₁.1 ht₂.1 ht₃.1,
    subgroupOf_mono H hVHM, mem_subgroupOf.mpr ht₁, mem_subgroupOf.mpr ht₂,
    mem_subgroupOf.mpr ht₃, ?_⟩
  intro v hv hv1
  have hvX := hkerX (MonoidHom.mem_ker.2 hv1)
  rw [mem_subgroupOf] at hv hvX
  have hvVX : (v : G) ∈ D.V ⊓ xSub p M H := ⟨hv, hvX⟩
  rw [hVX, mem_bot] at hvVX
  exact Subtype.ext hvVX

theorem TwelveSixKbarHyp.exists_kbarCfg (hyp : TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    ∃ (Y V W₁ W₂ W₃ : Subgroup (MulAut (kbarQuot p M H))) (t₁ t₂ t₃ : MulAut (kbarQuot p M H)),
      (MulAut.conj : kbarQuot p M H →* MulAut (kbarQuot p M H)).range ≤ Y ∧
      CFSG.Open.pRank 3 Y ≤ 3 ∧ IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃ ∧ V ≤ Y ∧
      t₁ ∈ Y ∧ t₂ ∈ Y ∧ t₃ ∈ Y := by
  have hKH := hyp.2.2.2.2.2.2
  obtain ⟨V, W₁, W₂, W₃, t₁, t₂, t₃, hcfg, -, -, -, -, hinj⟩ := hyp.exists_cfg_inf hK hKH
  obtain ⟨D⟩ := hyp.2.1
  exact ⟨_, _, _, _, _, _, _, _, KbarList.conj_range_le_range hKH,
    KbarList.pRank_three_range_le hyp.1 D hyp.2.2.2.2.1 hKH hK,
    KbarE27.isE27InvConfig_map hcfg _ hinj, map_le_range _ _, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
