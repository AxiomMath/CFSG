module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineApplyInputs
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCompNonempty
import CFSG.LocalAnalysis.RankThreeUC.AGL81CKStarComponent
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixPairFiveCatalogue
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.Holt.Induced

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

@[expose] def ThreeNineTuple (p d : ℕ) (K W : Type) [Group K] [Group W] : Prop :=
  (p = 3 ∧ d = 13 ∧ CFSG.Blueprint.ReeTitsModel K .Tits 2 1 ∧ IsPSLType 3 (ZMod 3) W) ∨
  (p = 5 ∧ d = 7 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic K .HS ∧
    CFSG.Open.StatedClassicalModel W .PSU 3 5 1) ∨
  (p = 5 ∧ d = 7 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic K .Fi22 ∧
    CFSG.Open.StatedClassicalModel W .POmegaPlus 4 2 1) ∨
  (p = 5 ∧ d = 31 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic K .Ly ∧
    CFSG.Blueprint.ChevalleyExceptionalModel W .G2 5 1) ∨
  (p = 7 ∧ d = 19 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic K .ONan ∧
    IsPSLType 3 (ZMod 7) W) ∨
  (p = 7 ∧ d = 17 ∧ CFSG.Blueprint.NativeSporadic.IsSporadic K .Fi24Prime ∧
    CFSG.Blueprint.NativeSporadic.IsSporadic W .He) ∨
  (d ∣ p + 1 ∧ IsPSLType 3 (ZMod p) K ∧ IsPSLType 2 (ZMod p) W)

theorem ThreeNineTuple.congr {p d : ℕ} {K K' W W' : Type} [Group K] [Group K'] [Group W]
    [Group W'] (eK : K ≃* K') (eW : W ≃* W') (h : ThreeNineTuple p d K W) :
    ThreeNineTuple p d K' W' := by
  rcases h with ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ |
    ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hp, hd, hK, hW⟩ | ⟨hdiv, hK, hW⟩
  · exact Or.inl ⟨hp, hd, CFSG.SectionRank.reeTitsModel_of_mulEquiv eK.symm hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩
  · exact Or.inr (Or.inl ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eW hW⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp, hd, Nonempty.map (fun e => eK.symm.trans e) hK,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eW hW⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hd,
      Nonempty.map (fun e => eK.symm.trans e) hK,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eW.symm hW⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hd,
      Nonempty.map (fun e => eK.symm.trans e) hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hd,
      Nonempty.map (fun e => eK.symm.trans e) hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hdiv,
      Nonempty.map (fun e => eK.symm.trans e) hK,
      Nonempty.map (fun e => eW.symm.trans e) hW⟩)))))

theorem normalizer_inf_subgroupOf_le {Y : Type} [Group Y] {N T X₁ : Subgroup Y}
    {F : Subgroup N}
    (h : Subgroup.normalizer ((F.map N.subtype : Subgroup Y) : Set Y) ⊓ T ≤ X₁) :
    Subgroup.normalizer (F : Set N) ⊓ T.subgroupOf N ≤ X₁.subgroupOf N :=
  fun _ hx => h ⟨Subgroup.le_normalizer_map (f := N.subtype) (H := F)
    (Subgroup.mem_map_of_mem N.subtype hx.1), hx.2⟩

theorem gammaOver_subgroupOf_le {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : 1 < q)
    {N R T X₁ : Subgroup Y}
    (h : ∀ F : Subgroup Y, F ≤ R → 1 ≤ CFSG.Open.pRank q F →
      Subgroup.normalizer (F : Set Y) ⊓ T ≤ X₁) :
    gammaOver 1 q (R.subgroupOf N) (T.subgroupOf N) ≤ X₁.subgroupOf N := by
  exact iSup₂_le fun F hF => iSup_le fun hk =>
    normalizer_inf_subgroupOf_le (h (F.map N.subtype)
      (by rintro _ ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.mp (hF hy))
      (hk.trans (CFSG.SectionRank.pRank_le_map hq N.subtype N.subtype_injective F)))

private theorem ne_bot_of_one_le_pRank {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : 1 < q)
    {F : Subgroup Y} (hF : 1 ≤ CFSG.Open.pRank q F) : F ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hE, -, hc⟩ := CFSG.SectionRank.exists_pRank hq (⊥ : Subgroup Y)
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hc
  exact (Nat.one_lt_pow (by omega) hq).ne' hc.symm

theorem threeNineConclusion_of_threeNineHyp (h39 : ThreeNine) {X : Type} [Group X] [Finite X]
    {K E D X₁ : Subgroup X} {p d : ℕ}
    (h : CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp K E D X₁ p d) :
    CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineConclusion K D X₁ p d :=
  h39 X K E D X₁ p d h.prime h.ne_two h.quasisimple h.core h.kgroup h.normal h.one_lt_rank
    h.rank_le h.elem h.card_E h.d_prime h.d_ne_two h.d_ne h.sylow h.D_ne_bot h.lt h.gammaE
    h.gammaD h.normQ

theorem starImg_le_normalizer_kStar (p : ℕ) (M H : Subgroup G) :
    starImg p H M ≤ Subgroup.normalizer (kStar p M H : Set (StarGroup p H)) := by
  have hnorm : M.subgroupOf H ≤
      Subgroup.normalizer (((kSub p M H).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa using conj_mem_kSub a.2 (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
  exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)

theorem exists_starImg_eq_of_isPGroup (hp : p.Prime) {E : Subgroup G} (hEH : E ≤ H)
    (hE : IsPGroup p E) {U : Subgroup (StarGroup p H)} (hU : IsPGroup p U)
    (hEU : starImg p H E ≤ U) :
    ∃ R : Subgroup G, R ≤ H ∧ IsPGroup p R ∧ E ≤ R ∧ starImg p H R = U := by
  have : Fact p.Prime := ⟨hp⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  obtain ⟨T, hET, -, hT, hTU⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le π hU
    (by rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]; exact le_top)
    (hE.comap_subtype (K := H)) le_top hEU
  refine ⟨T.map H.subtype, Subgroup.map_subtype_le T, hT.map _,
    fun x hx => ⟨⟨x, hEH hx⟩, hET hx, rfl⟩, ?_⟩
  simp only [starImg, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact hTU

theorem normalizer_le_starImg_of_isPGroup (hI : NineNineOneInput) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) {U : Subgroup (StarGroup p H)} (hU : IsPGroup p U)
    (hEU : starImg p H E ≤ U) :
    Subgroup.normalizer (U : Set (StarGroup p H)) ≤ starImg p H M := by
  obtain ⟨R, hRH, hRp, hER, rfl⟩ := exists_starImg_eq_of_isPGroup h.p_prime
    (hEQ.trans h.Q_le_H) hE.isPGroup hU hEU
  rw [Section15.starImg_normalizer_eq h.p_prime hRH hRp]
  exact starImg_mono (inf_le_left.trans
    (le_M_and_normalizer_le_of_le hI h hEQ hE hEc hΓ hRp hER).2)

theorem normalizer_le_starImg_of_le_starImg (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : IsPGroup d D) (hDHM : D ≤ H ⊓ M) {F : Subgroup (StarGroup p H)}
    (hFD : F ≤ starImg p H D) (hF1 : F ≠ ⊥) :
    Subgroup.normalizer (F : Set (StarGroup p H)) ≤ starImg p H M := by
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let D₀ : Subgroup G := (F.comap π ⊓ D.subgroupOf H).map H.subtype
  have hD₀sub : D₀.subgroupOf H = F.comap π ⊓ D.subgroupOf H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hstar : starImg p H D₀ = F := by
    rw [show starImg p H D₀ = (F.comap π ⊓ D.subgroupOf H).map π by
      rw [starImg, hD₀sub]]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro f hf
      obtain ⟨x, hx, hxf⟩ := Subgroup.mem_map.mp
        (show f ∈ (D.subgroupOf H).map π from hFD hf)
      exact Subgroup.mem_map.mpr
        ⟨x, ⟨Subgroup.mem_comap.mpr (hxf.symm ▸ hf), hx⟩, hxf⟩
  have hD₀D : D₀ ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hx.2
  have hD₀1 : D₀ ≠ ⊥ := by
    intro hbot
    apply hF1
    rw [← hstar, hbot]
    simp [starImg]
  rw [← hstar, starImg_normalizer_eq_of_not_dvd hdp
    (not_dvd_card_primeComplementCore_of_twelveCtx h hXM) (Subgroup.map_subtype_le _)
    (hD.to_le hD₀D)]
  exact starImg_mono (inf_le_left.trans
    (normalizer_le_M_of_mem_sigmaSet h hns hd (hD.to_le hD₀D)
      (hD₀D.trans (hDHM.trans inf_le_right)) hD₀1))

private theorem subgroupOf_lt {Y : Type} [Group Y] {N K D X₁ : Subgroup Y}
    (hKN : K ≤ N) (hDN : D ≤ N) (hX₁N : X₁ ≤ N) (hlt : X₁ < K ⊔ D) :
    X₁.subgroupOf N < K.subgroupOf N ⊔ D.subgroupOf N := by
  rw [← Subgroup.subgroupOf_sup hKN hDN]
  refine lt_of_le_of_ne (Subgroup.subgroupOf_mono N hlt.le) ?_
  intro heq
  have h := Subgroup.subgroupOf_inj.mp heq
  rw [inf_eq_left.mpr hX₁N, inf_eq_left.mpr (sup_le hKN hDN)] at h
  exact hlt.ne h

private theorem subgroupOf_ne_bot {Y : Type} [Group Y] {N D : Subgroup Y} (hDN : D ≤ N)
    (hD1 : D ≠ ⊥) : D.subgroupOf N ≠ ⊥ := by
  intro hbot
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hDN] at hbot
  exact hD1 hbot

private theorem gammaOver_subgroupOf_le_of {Y : Type} [Group Y] [Finite Y]
    {N E K D X₁ : Subgroup Y} {p : ℕ} (hKN : K ≤ N) (hDN : D ≤ N) (hp : 1 < p)
    (hΓ : ∀ F : Subgroup Y, F ≤ E → 1 ≤ CFSG.Open.pRank p F →
      Subgroup.normalizer (F : Set Y) ⊓ (K ⊔ D) ≤ X₁) :
    gammaOver 1 p (E.subgroupOf N) (K.subgroupOf N ⊔ D.subgroupOf N) ≤ X₁.subgroupOf N := by
  rw [← Subgroup.subgroupOf_sup hKN hDN]
  exact gammaOver_subgroupOf_le (N := N) (R := E) (T := K ⊔ D) (X₁ := X₁) hp hΓ

private theorem gammaIn_subgroupOf_le {Y : Type} [Group Y] [Finite Y]
    {N K D X₁ : Subgroup Y} {d : ℕ} (hKN : K ≤ N) (hDN : D ≤ N) (hd : 1 < d)
    (hΓ : ∀ F : Subgroup Y, F ≤ D → 1 ≤ CFSG.Open.pRank d F →
      Subgroup.normalizer (F : Set Y) ⊓ (K ⊔ D) ≤ X₁) :
    gammaIn 1 d (D.subgroupOf N) (K.subgroupOf N ⊔ D.subgroupOf N) ≤ X₁.subgroupOf N := by
  rw [← Subgroup.subgroupOf_sup hKN hDN]
  exact (CFSG.LocalAnalysis.AGL81I.Section3.gammaIn_le_gammaOver hd
    (D.subgroupOf N) ((K ⊔ D).subgroupOf N)).trans
    (gammaOver_subgroupOf_le (N := N) (R := D) (T := K ⊔ D) (X₁ := X₁) hd hΓ)

private theorem normalizer_subgroupOf_le {Y : Type} [Group Y] {N K E D X₁ : Subgroup Y}
    {p : ℕ} (hKN : K ≤ N) (hDN : D ≤ N) (hEN : E ≤ N)
    (h : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set Y) ⊓ (K ⊔ D) ≤ X₁) :
    ∀ Q : Subgroup ↥N, IsPGroup p Q → E.subgroupOf N ≤ Q →
      Subgroup.normalizer (Q : Set ↥N) ⊓ (K.subgroupOf N ⊔ D.subgroupOf N) ≤
        X₁.subgroupOf N := by
  intro Q hQp hEQ
  rw [← Subgroup.subgroupOf_sup hKN hDN]
  exact normalizer_inf_subgroupOf_le (N := N) (T := K ⊔ D) (X₁ := X₁)
    (h (Q.map N.subtype) (Subgroup.map_subtype_le Q) (hQp.map N.subtype)
      ((Subgroup.map_subgroupOf_eq_of_le hEN).symm.le.trans (Subgroup.map_mono hEQ)))

theorem threeNineHyp_subgroupOf {Y : Type} [Group Y] [Finite Y] {N K E D X₁ : Subgroup Y}
    {p d : ℕ} (hKN : K ≤ N) (hEN : E ≤ N) (hDN : D ≤ N) (hp : p.Prime) (hp2 : p ≠ 2)
    (hKq : CFSG.IsQuasisimple ↥K) (hKO : CFSG.pPrimeCore p ↥K = ⊥)
    (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : N ≤ Subgroup.normalizer (K : Set Y))
    (h1 : 1 < CFSG.Open.pRank p N) (h3 : CFSG.Open.pRank p N ≤ 3)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p)
    (hD : CFSG.ABGLocalTools.IsSylowOf d D N) (hD1 : D ≠ ⊥) (hlt : X₁ < K ⊔ D)
    (hΓE : ∀ F : Subgroup Y, F ≤ E → 1 ≤ CFSG.Open.pRank p F →
      Subgroup.normalizer (F : Set Y) ⊓ (K ⊔ D) ≤ X₁)
    (hΓD : ∀ F : Subgroup Y, F ≤ D → 1 ≤ CFSG.Open.pRank d F →
      Subgroup.normalizer (F : Set Y) ⊓ (K ⊔ D) ≤ X₁)
    (hQ : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup p Q → E ≤ Q →
      Subgroup.normalizer (Q : Set Y) ⊓ (K ⊔ D) ≤ X₁) :
    CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp (K.subgroupOf N) (E.subgroupOf N)
      (D.subgroupOf N) (X₁.subgroupOf N) p d := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact d.Prime := ⟨hd⟩
  have hX₁N : X₁ ≤ N := hlt.le.trans (sup_le hKN hDN)
  refine
    { prime := hp
      ne_two := hp2
      quasisimple := CFSG.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKN) hKq
      core := CFSG.pPrimeCore_eq_bot_of_mulEquiv p
        (Subgroup.subgroupOfEquivOfLe hKN).symm hKO
      kgroup := hKcat.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKN)
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hKn
      one_lt_rank := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
        exact h1
      rank_le := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
        exact h3
      elem := hE.subgroupOf N
      card_E := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv).trans hEc
      d_prime := hd
      d_ne_two := hd2
      d_ne := hdp
      sylow := by
        rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N,
          Subgroup.map_subgroupOf_eq_of_le hDN, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
        exact hD
      D_ne_bot := subgroupOf_ne_bot hDN hD1
      lt := subgroupOf_lt hKN hDN hX₁N hlt
      gammaE := gammaOver_subgroupOf_le_of hKN hDN hp.one_lt hΓE
      gammaD := gammaIn_subgroupOf_le hKN hDN hd.one_lt hΓD
      normQ := normalizer_subgroupOf_le hKN hDN hEN hQ }

theorem threeNineConclusion_subgroupOf {Y : Type} [Group Y] [Finite Y] {N K D X₁ : Subgroup Y}
    {p d : ℕ} (hKN : K ≤ N) (hDN : D ≤ N) (hX₁N : X₁ ≤ N)
    (h : CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineConclusion (K.subgroupOf N)
      (D.subgroupOf N) (X₁.subgroupOf N) p d) :
    IsCyclic ↥D ∧ D ≤ K ∧ ThreeNineTuple p d ↥K (oPrimeModPrimeComplement d X₁) := by
  rcases h with ⟨hcyc, hDK, htuple⟩
  have hcycD : IsCyclic ↥D :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hDN)).mp hcyc
  have hDKD : D ≤ K := by
    intro x hx
    have hxN : x ∈ N := hDN hx
    have hxD' : (⟨x, hxN⟩ : N) ∈ D.subgroupOf N := by
      rwa [Subgroup.mem_subgroupOf]
    have hxK' : (⟨x, hxN⟩ : N) ∈ K.subgroupOf N := hDK hxD'
    rwa [Subgroup.mem_subgroupOf] at hxK'
  refine ⟨hcycD, hDKD, ?_⟩
  obtain ⟨eW⟩ :=
    CFSG.LocalAnalysis.AGL81I.Section3.oPrimeModPrimeComplement_congr d
      (Subgroup.subgroupOfEquivOfLe hX₁N)
  exact ThreeNineTuple.congr (Subgroup.subgroupOfEquivOfLe hKN) eW htuple

private theorem gammaOver_starImg_E_le_of_twelveCtx {E : Subgroup G}
    (hS : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen G M p Q H E 2)
    {C D : Subgroup (StarGroup p H)} :
    ∀ F : Subgroup (StarGroup p H), F ≤ starImg p H E → 1 ≤ CFSG.Open.pRank p F →
      Subgroup.normalizer (F : Set (StarGroup p H)) ⊓ (C ⊔ D) ≤
        starImg p H M ⊓ (C ⊔ D) := fun _ hF hk =>
  inf_le_inf_right _ ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hF hk).trans
    hS.rankThreeGamma_starImg_E_le_gen)

private theorem gammaIn_starImg_D_le_of_twelveCtx (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : IsPGroup d D) (hDHM : D ≤ H ⊓ M) {C : Subgroup (StarGroup p H)} :
    ∀ F : Subgroup (StarGroup p H), F ≤ starImg p H D → 1 ≤ CFSG.Open.pRank d F →
      Subgroup.normalizer (F : Set (StarGroup p H)) ⊓ (C ⊔ starImg p H D) ≤
        starImg p H M ⊓ (C ⊔ starImg p H D) := fun _ hF hk =>
  inf_le_inf_right _ (normalizer_le_starImg_of_le_starImg h hns hd hXM hD hDHM hF
    (ne_bot_of_one_le_pRank
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1).one_lt hk))

private theorem normalizer_starImg_le_of_twelveCtx (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΓ : rankThreeGamma 1 p E ≤ M)
    {N C D : Subgroup (StarGroup p H)} :
    ∀ U : Subgroup (StarGroup p H), U ≤ N → IsPGroup p U → starImg p H E ≤ U →
      Subgroup.normalizer (U : Set (StarGroup p H)) ⊓ (C ⊔ D) ≤
        starImg p H M ⊓ (C ⊔ D) := fun _ _ hU hEU =>
  inf_le_inf_right _ (normalizer_le_starImg_of_isPGroup hI h hEQ hE hEc hΓ hU hEU)

theorem threeNineHyp_of_twelveCtx (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M) :
    ∃ E : Subgroup (StarGroup p H),
      CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
        (C.subgroupOf (Subgroup.normalizer (C : Set (StarGroup p H))))
        (E.subgroupOf (Subgroup.normalizer (C : Set (StarGroup p H))))
        ((starImg p H D).subgroupOf (Subgroup.normalizer (C : Set (StarGroup p H))))
        ((starImg p H M ⊓ (C ⊔ starImg p H D)).subgroupOf
          (Subgroup.normalizer (C : Set (StarGroup p H)))) p d := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have hdne : d ≠ p := fun e => h.p_not_mem_sigma (e ▸ hd)
  have : Fact d.Prime := ⟨hdp⟩
  obtain ⟨E₀, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hS : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen G M p Q H E₀ 2 :=
    nineSettingGen h hEQ hE hEc hΓ
  let N : Subgroup (StarGroup p H) := Subgroup.normalizer (C : Set (StarGroup p H))
  have hO := not_dvd_card_primeComplementCore_of_twelveCtx h hXM
  have hEN : starImg p H E₀ ≤ N := hS.starImg_E_le_normalizer_gen hC hCM
  have hDN : starImg p H D ≤ N :=
    starImg_le_normalizer_of_isComponent h hdp hd2 hD.isPGroup hD.le hC hCM
  have h1 : 1 < CFSG.Open.pRank p N := by
    have h2 := CFSG.SectionRank.le_pRank (p := p) h.p_prime.one_lt hEN
      hS.isElemAbelian_starImg_E_gen (k := 2) hS.card_starImg_E_gen
    omega
  have h3 : CFSG.Open.pRank p N ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.p_prime.one_lt (le_top : N ≤ ⊤)).trans
      (hS.pRank_star_le_three h.H_mem_H2Star.1 h.p_not_mem_sigma)
  have hKcat : CFSG.SectionRank.IsKGroupCat ↥C :=
    (isKGroupCat_of_starGroup hbridge h ⊤ (C.subgroupOf ⊤)).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe le_top).symm
  have hCore : CFSG.pPrimeCore p ↥C = ⊥ :=
    pPrimeCore_eq_bot_of_isComponent_of_prime h.p_prime
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) h.p_prime) hC
  have hsyl : CFSG.ABGLocalTools.IsSylowOf d (starImg p H D) N :=
    (isSylowOf_starImg_top_of_prime hdp
      (isSylowOf_H_of_isSylowOf_inf h hns hd hD hD1)).of_le hDN le_top
  have hD1' : starImg p H D ≠ ⊥ :=
    starImg_ne_bot_of_not_dvd hdp hO (hD.le.trans inf_le_left) hD.isPGroup hD1
  have hlt : starImg p H M ⊓ (C ⊔ starImg p H D) < C ⊔ starImg p H D :=
    inf_lt_right.mpr fun hle => hCM (le_sup_left.trans hle)
  have hΓE := gammaOver_starImg_E_le_of_twelveCtx (C := C) (D := starImg p H D) hS
  have hΓD := gammaIn_starImg_D_le_of_twelveCtx (C := C) h hns hd hXM hD.isPGroup hD.le
  have hQ := normalizer_starImg_le_of_twelveCtx (N := N) (C := C) (D := starImg p H D)
    hI h hEQ hE hEc hΓ
  refine ⟨starImg p H E₀, threeNineHyp_subgroupOf (N := N) (K := C) (E := starImg p H E₀)
    (D := starImg p H D) (X₁ := starImg p H M ⊓ (C ⊔ starImg p H D))
    Subgroup.le_normalizer hEN hDN h.p_prime h.p_odd hC.1 hCore hKcat le_rfl h1 h3
    hS.isElemAbelian_starImg_E_gen hS.card_starImg_E_gen hdp hd2 hdne hsyl hD1' hlt
    hΓE hΓD hQ⟩

theorem threeNine_of_twelveCtx (h39 : ThreeNine) (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ starImg p H M) :
    IsCyclic ↥(starImg p H D) ∧ starImg p H D ≤ C ∧
      ThreeNineTuple p d ↥C
        (oPrimeModPrimeComplement d (starImg p H M ⊓ (C ⊔ starImg p H D))) := by
  obtain ⟨E, hH⟩ := threeNineHyp_of_twelveCtx hI hbridge h hns hd hXM hD hD1 hC hCM
  have hDN : starImg p H D ≤ Subgroup.normalizer (C : Set (StarGroup p H)) :=
    starImg_le_normalizer_of_isComponent h
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1)
      hD.isPGroup hD.le hC hCM
  exact threeNineConclusion_subgroupOf (N := Subgroup.normalizer (C : Set (StarGroup p H)))
    (K := C) (D := starImg p H D) (X₁ := starImg p H M ⊓ (C ⊔ starImg p H D))
    Subgroup.le_normalizer hDN
    (inf_le_right.trans (sup_le Subgroup.le_normalizer hDN))
    (threeNineConclusion_of_threeNineHyp h39 hH)

private theorem eq_of_isComponent_of_not_le {C₀ : Subgroup (StarGroup p H)}
    (hC₀ : CFSG.IsComponent C₀) (hC₀M : ¬ C₀ ≤ starImg p H M)
    {D : Subgroup (StarGroup p H)}
    (hDS : ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → ¬ C ≤ starImg p H M → D ≤ C)
    (hND : Subgroup.normalizer (D : Set (StarGroup p H)) ≤ starImg p H M) :
    ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → ¬ C ≤ starImg p H M → C = C₀ := by
  intro C hC hCM
  rcases CFSG.LocalCores.distinct_components_commute hC hC₀ with heq | hcomm
  · exact heq
  · exfalso
    apply hCM
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hDS C₀ hC₀ hC₀M))).trans
        ((Subgroup.centralizer_le_normalizer _).trans hND))

theorem kStar_isQuasisimple_of_twelveCtx (h39 : ThreeNine) (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G))
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M) :
    CFSG.IsQuasisimple ↥(kStar p M H) ∧ ¬ kStar p M H ≤ starImg p H M := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd2 : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  obtain ⟨E₀, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hS : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen G M p Q H E₀ 2 :=
    nineSettingGen h hEQ hE hEc hΓ
  have hO := not_dvd_card_primeComplementCore_of_twelveCtx h hXM
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
  have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
    hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hD.card_eq] at hcard
    exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcard
  have hD1' : starImg p H D ≠ ⊥ :=
    starImg_ne_bot_of_not_dvd hdp hO (hD.le.trans inf_le_left) hD.isPGroup hD1
  have hDS : ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → ¬ C ≤ starImg p H M →
      starImg p H D ≤ C := fun C hC hCM =>
    (threeNine_of_twelveCtx h39 hI hbridge h hns hd hXM hD hD1 hC hCM).2.1
  have hND : Subgroup.normalizer (starImg p H D : Set (StarGroup p H)) ≤ starImg p H M :=
    normalizer_le_starImg_of_le_starImg h hns hd hXM hD.isPGroup hD.le le_rfl hD1'
  obtain ⟨J, hJ, hJM⟩ := exists_pComponentIn_not_le_of_not_pLayerIn_le hA
  let C₀ : Subgroup (StarGroup p H) := starImg p H J
  have hC₀ : CFSG.IsComponent C₀ := isComponent_starImg hJ
  have hC₀M : ¬ C₀ ≤ starImg p H M := fun hle =>
    hJM ((hS.le_iff_starImg_le hJ.1).mpr hle)
  have huniq := eq_of_isComponent_of_not_le hC₀ hC₀M hDS hND
  have hK : kStar p M H = C₀ := by
    rw [hS.kStar_eq_sSup_of_not_le hA]
    refine le_antisymm (sSup_le fun C hC => (huniq C hC.1 hC.2).le) (le_sSup ⟨hC₀, hC₀M⟩)
  rw [hK]
  exact ⟨hC₀.1, hC₀M⟩

theorem threeNine_kStar_of_twelveCtx (h39 : ThreeNine) (hI : NineNineOneInput)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hXM : ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G)) (hA : ¬ pLayerIn p H ≤ M)
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) (hD1 : D ≠ ⊥) :
    IsCyclic ↥(starImg p H D) ∧ starImg p H D ≤ kStar p M H ∧
      ThreeNineTuple p d ↥(kStar p M H)
        (oPrimeModPrimeComplement d (starImg p H M ⊓ (kStar p M H ⊔ starImg p H D))) := by
  have : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hdH : d ∣ Nat.card (H ⊓ M : Subgroup G) := by
    obtain ⟨n, hn⟩ := hD.isPGroup.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hD1 (Subgroup.card_eq_one.mp hn)
    have hdD : d ∣ Nat.card D := by
      rw [hn]
      exact dvd_pow_self d hn0
    exact hdD.trans (Subgroup.card_dvd_of_le hD.le)
  obtain ⟨hq, -⟩ := kStar_isQuasisimple_of_twelveCtx h39 hI hbridge h hns hd hXM hdH hA
  obtain ⟨E₀, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  have hK := (nineSettingGen h hEQ hE hEc hΓ).isComponent_kStar_of_isQuasisimple hA hq
  exact threeNine_of_twelveCtx h39 hI hbridge h hns hd hXM hD hD1 hK.1 hK.2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
