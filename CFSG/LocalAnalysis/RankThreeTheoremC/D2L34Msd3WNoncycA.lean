module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNormal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Factor81

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf_of_mem_normalizers {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  exact ⟨fun hx => ⟨(hH x).1 hx.1, (hK x).1 hx.2⟩, fun hx => ⟨(hH x).2 hx.1, (hK x).2 hx.2⟩⟩

theorem exists_E27_of_commuting_E9 {D R₀ : Subgroup G} (hD : IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hR : IsElemAbelian 3 R₀) (hR9 : Nat.card R₀ = 9) (hne : D ≠ R₀)
    (hcomm : ∀ d ∈ D, ∀ r ∈ R₀, d * r = r * d) :
    ∃ F : Subgroup G, F ≤ D ⊔ R₀ ∧ IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      ∀ r ∈ R₀, ∀ f ∈ F, r * f = f * r := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR₀C : R₀ ≤ Subgroup.centralizer (D : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => hcomm d hd r hr
  have hR₀N : R₀ ≤ Subgroup.normalizer (D : Set G) :=
    hR₀C.trans (Subgroup.centralizer_le_normalizer _)
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hR₀N
  rw [hD9, hR9] at hcard
  have hinfd : Nat.card (D ⊓ R₀ : Subgroup G) ∣ 9 := hD9 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hinfne : Nat.card (D ⊓ R₀ : Subgroup G) ≠ 9 := by
    intro h9
    have hDR : D ⊓ R₀ = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hD9, h9])
    have hDR₀ : D ≤ R₀ := hDR.symm.le.trans inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hDR₀ (by rw [hD9, hR9]))
  have h27 : 27 ∣ Nat.card (D ⊔ R₀ : Subgroup G) := by
    have hjpos : 0 < Nat.card (D ⊓ R₀ : Subgroup G) := Nat.card_pos
    obtain ⟨c, hc⟩ := hinfd
    have hjle : Nat.card (D ⊓ R₀ : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) ⟨c, hc⟩
    generalize Nat.card (D ⊓ R₀ : Subgroup G) = j at hjpos hjle hc hinfne hcard
    interval_cases j <;> omega
  have hSel : IsElemAbelian 3 (D ⊔ R₀) := by
    have hUnion : D ⊔ R₀ = Subgroup.closure ((D : Set G) ∪ (R₀ : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hUnion]
    refine CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.isElemAbelian_closure (p := 3) ?_ ?_
    · rintro a (ha | ha) b (hb | hb)
      · exact congrArg Subtype.val (isMulCommutative_iff.mp hD.1 ⟨a, ha⟩ ⟨b, hb⟩)
      · exact hcomm a ha b hb
      · exact (hcomm b hb a ha).symm
      · exact congrArg Subtype.val (isMulCommutative_iff.mp hR.1 ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro a (ha | ha)
      · exact hD.2 a ha
      · exact hR.2 a ha
  obtain ⟨F, hFS, hF, hFc⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.exists_sub_ea_of_dvd
      (isEA3_of_isElemAbelian hSel) (n := 3) (by simpa using h27)
  exact ⟨F, hFS, isElemAbelian_of_isEA3 hF, by rw [hFc]; norm_num, fun r hr f hf =>
    congrArg Subtype.val (isMulCommutative_iff.mp hSel.1 ⟨r, Subgroup.mem_sup_right hr⟩
      ⟨f, hFS hf⟩)⟩

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem exists_sylow_le {M X : Subgroup G} (hXM : X ≤ M) (hXp : IsPGroup 3 X) :
    ∃ W : Subgroup G, W ≤ M ∧ IsPGroup 3 W ∧ ¬ 3 ∣ (W.subgroupOf M).index ∧ X ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXp' : IsPGroup 3 (X.subgroupOf M) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  obtain ⟨Q, hXQ⟩ := hXp'.exists_le_sylow
  set W : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hW
  have hWM : W ≤ M := Subgroup.map_subtype_le _
  have hWsub : W.subgroupOf M = Q :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨W, hWM, Q.isPGroup'.map _, ?_, fun x hx =>
    ⟨⟨x, hXM hx⟩, hXQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩⟩
  rw [hWsub]
  exact Q.not_dvd_index

theorem D2L34SideCtx3.exists_E27_le_sylow (h : D2L34SideCtx3 G d P M A H R Rbar K)
    {W : Subgroup G} (hWM : W ≤ M) (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) :
    ∃ F : Subgroup G, F ≤ W ∧ IsElemAbelian 3 F ∧ Nat.card F = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M :=
    hP3.ge.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hPM)
  obtain ⟨F, hFW, hFel, hFc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  exact ⟨F, hFW, hFel, by rw [hFc]; norm_num⟩

theorem D2L34SideCtx3.hasGoodE9_inf_normal (h : D2L34SideCtx3 G d P M A H R Rbar K)
    {C W : Subgroup G} (hCM : C ≤ M) (hCn : (C.subgroupOf M).Normal) (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index) (hWC : ¬ IsCyclic ↥(W ⊓ C)) :
    HasGoodE9 M (W ⊓ C) := by
  obtain ⟨F, hFW, hFel, hF27⟩ := h.exists_E27_le_sylow hWM hWp hWidx
  have hCN : M ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hCn
  exact h.hasGoodE9_of_noncyclic_normal hWM hWp inf_le_left
    (fun w hw => mem_normalizer_inf_of_mem_normalizers (Subgroup.le_normalizer hw)
      (hCN (hWM hw))) hWC hFW hFel hF27

theorem D2L34SideCtx3.card_le_nine_of_le_normal [D2Amb3 G]
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9) {N C X : Subgroup G}
    (hN : IsTwoLocal N) (hNM : ¬ N ≤ M) (hCM : C ≤ M) (hCN : C ≤ N)
    (hCn : (C.subgroupOf M).Normal) (hXC : X ≤ C) (hXp : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    Nat.card X ≤ 9 := by
  obtain ⟨W, hWM, hWp, hWidx, hXW⟩ := exists_sylow_le (hXC.trans hCM) hXp
  have hXWC : X ≤ W ⊓ C := le_inf hXW hXC
  have hWCc : ¬ IsCyclic ↥(W ⊓ C) := fun hcyc =>
    hXc (Subgroup.isCyclic_of_le (H' := W ⊓ C) hXWC)
  have hgood := h.hasGoodE9_inf_normal hCM hCn hWM hWp hWidx hWCc
  have h9 := D2L34BetaConf3.card_le_nine_of_good h.conf hR9 h.normRankTwo hN hNM
    (inf_le_right.trans hCN) (inf_le_right.trans hCM) (hWp.to_le inf_le_left) hWCc hgood
  exact (Subgroup.card_le_of_le hXWC).trans h9

theorem D2L34SideCtx3.pRank_inf_le_two [D2Amb3 G] (h : D2L34SideCtx3 G d P M A H R Rbar K)
    {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M) :
    CFSG.Open.pRank 3 (N ⊓ M) ≤ 2 := by
  by_contra hlt
  exact hNM (D2Amb3.d1 (G := G) P M h.conf.esc.maxTwoLocal_M
    ((weakCore_le_fullCore 3 (P : Subgroup G)).trans h.conf.esc.core_le) N hN (by omega))

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC
