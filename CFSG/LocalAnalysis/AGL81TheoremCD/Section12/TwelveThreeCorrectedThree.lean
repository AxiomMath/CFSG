module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase5
public import Certificates.Certificate1322001
import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Main
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenAtStarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.GroupTheory.BaerSuzuki.Helpers
import CFSG.LocalAnalysis.SectionRank.QTK.OddLinear
public import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
public import CFSG.LocalAnalysis.AGL81I.Section3.PSL2BorelMaximal
public import CFSG.LocalAnalysis.AGL81I.Section3.SL3Parabolic
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL2Y
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem oPPrimeHull_eq_self_of_closure_orderOf {X : Type} [Group X] {p : ℕ}
    {N : Subgroup X} (hN : N = Subgroup.closure {x : X | orderOf x = p}) :
    oPPrimeHull p N = N := by
  refine le_antisymm ((Subgroup.closure_le N).mpr fun x hx => hx.1) ?_
  nth_rewrite 1 [hN]
  refine (Subgroup.closure_le (oPPrimeHull p N)).mpr fun x hx => Subgroup.subset_closure ?_
  exact ⟨hN.symm ▸ Subgroup.subset_closure hx, 1, by simpa using hx⟩

private theorem branchCThree_starImg_le_sup (h10 : NineTenGen) (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) (hp3 : p = 3)
    (hSp : Nat.card ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G} (hD : IsPGroup d D) :
    starImg p H D ≤ kStar p M H ⊔ CFSG.pCore 3 (StarGroup p H) := by
  subst hp3
  have hle : pLayerIn 3 H ≤ M := by rw [hbot]; exact bot_le
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  obtain ⟨-, hcard⟩ := nineTen_branchC_of_twelveCtx h10 h hEQ hE hEc hΓ hbot
  have hset := nineSettingGen h hEQ hE hEc hΓ
  have hC : Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H)) ≤
      CFSG.pCore 3 (StarGroup 3 H) :=
    centralizer_pCore_le_of_layer_eq_bot Nat.prime_three H
      ((pLayerIn_eq_bot_iff Nat.prime_three H).mp hbot)
  have hQ : CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)) ≤ 3 :=
    NineSettingGen.pRank_pCore_star_le_three hset h.mem_H4Star.1.1
      (by simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using
        h.p_not_mem_sigma)
  have hNn : (kStar 3 M H).Normal := kStar_normal_of_le hle
  have hN : oPPrimeHull 3 (kStar 3 M H) = kStar 3 M H := by
    rw [kStar_eq_closure_of_le (p := 3) (M := M) (H := H) Nat.prime_three hle]
    exact oPPrimeHull_eq_self_of_closure_orderOf rfl
  have hN1 : ¬ kStar 3 M H ≤ CFSG.pCore 3 (StarGroup 3 H) := by
    intro hNle
    have hNp : IsPGroup 3 (kStar 3 M H) :=
      (CFSG.pCore_isPGroup (p := 3) (G := StarGroup 3 H)).to_le hNle
    have htopP : IsPGroup 3 (⊤ : Subgroup ↥(kStar 3 M H)) :=
      hNp.of_equiv (Subgroup.topEquiv (G := ↥(kStar 3 M H))).symm
    have htop : CFSG.pCore 3 ↥(kStar 3 M H) = ⊤ :=
      le_antisymm le_top (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
        Subgroup.normal_top htopP)
    have hcard1 : Nat.card (KStarQuot 3 M H) = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨?_, inferInstance⟩
      change Subsingleton (↥(kStar 3 M H) ⧸ CFSG.pCore 3 ↥(kStar 3 M H))
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact hcard hcard1
  obtain ⟨hdp, hd2, hd3⟩ := mem_sigma_prime_odd_ne_p h hd
  have hd5 : 5 ≤ d := hdp.five_le_of_ne_two_of_ne_three hd2 hd3
  exact le_sup_pCore_three_of_isPGroup hC hQ hSp hNn hN hN1 hdp hd5
    (show IsPGroup d (starImg 3 H D) from
      (hD.comap_subtype (K := H)).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)))

private theorem branchCThree_oneImg_le (h10 : NineTenGen) (h : TwelveCtx G M p Q H)
    (hbot : pLayerIn p H = ⊥) (hp3 : p = 3)
    (hSp : Nat.card ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840)
    {d : ℕ} (hd : d ∈ sigmaSet G M) {D : Subgroup G}
    (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    oneImg p H D ≤ oneImg p H (kSub p M H) := by
  subst hp3
  have hsup := branchCThree_starImg_le_sup h10 h hbot rfl hSp (D := D) hd hD.isPGroup
  have hone : (starImg 3 H D).map
      (QuotientGroup.mk' (CFSG.pCore 3 (StarGroup 3 H))) = oneImg 3 H D := by
    rw [starImg, oneImg, oneMap, Subgroup.map_map]
  have hkeq : (kStar 3 M H).map
      (QuotientGroup.mk' (CFSG.pCore 3 (StarGroup 3 H))) =
      oneImg 3 H (kSub 3 M H) := by
    rw [kStar, oneImg, oneMap, Subgroup.map_map]
  have hmap := Subgroup.map_mono
    (f := QuotientGroup.mk' (CFSG.pCore 3 (StarGroup 3 H))) hsup
  rw [hone, Subgroup.map_sup, hkeq,
    show (CFSG.pCore 3 (StarGroup 3 H)).map
      (QuotientGroup.mk' (CFSG.pCore 3 (StarGroup 3 H))) = ⊥ from by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']] at hmap
  rw [sup_bot_eq] at hmap
  exact hmap

private theorem false_of_sixThreeOneList_three {X : Type} [Group X] [Finite X] {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hcard : Nat.card X ≠ 1) (hlist : SixThreeOneList 3 X)
    (hSL : (IsSLType 2 (ZMod 3) X ∨ IsPSLType 2 (ZMod 3) X ∨ IsSLType 3 (ZMod 3) X) →
      d ∣ 3 + 1)
    (hSL5 : IsSLType 2 (ZMod 5) X → d ∣ 3 + 1)
    (hA5 : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X → d ∣ 3 + 1)
    (h13 : IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) X → False)
    (hSp4 : (∃ W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)),
      oPPrimeHull 3 W = W ∧ Nonempty (X ≃* ↥W ⧸ CFSG.pCore 3 ↥W)) → False) : False := by
  unfold SixThreeOneList at hlist
  have hfour : ∀ h : d ∣ 3 + 1, False := fun h =>
    CFSG.SectionRank.QTK.not_dvd_four_of_odd_prime hd hd2 (by simpa using h)
  rcases hlist with h | ⟨hp7, -⟩ | ⟨hp5, -⟩ | ⟨-, h⟩
  · rcases h with h | h | h | h
    · exact hfour (hSL (Or.inl h))
    · exact hfour (hSL (Or.inr (Or.inr h)))
    · exact hfour (hSL (Or.inr (Or.inl h)))
    · exact hcard h
  · omega
  · omega
  · rcases h with h | h | h | h
    · exact hfour (hSL5 h)
    · exact hfour (hA5 h)
    · exact h13 h
    · exact hSp4 h

@[expose] def TwelveThreeCorrectedThreeFacts : Prop :=
  CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase5Sp4 ∧
    Nat.card ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840

theorem twelveThreeCorrectedThreeFacts_holds :
    TwelveThreeCorrectedThreeFacts :=
  ⟨CFSG.LocalAnalysis.AGL81I.Section3.threeTenCase5Sp4_holds,
    Certificates.certificate1322001.1⟩

theorem false_of_branchC_three (h10 : NineTenGen) (h310 : ThreeTen) (hI : NineNineOneInput)
    (hC3 : TwelveThreeCorrectedThreeFacts) (h : TwelveCtx G M p Q H)
    (hns : ¬ Group.IsSolvable ↥M) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hdH : d ∣ Nat.card (H ⊓ M : Subgroup G)) (hbot : pLayerIn p H = ⊥) (hp3 : p = 3) : False := by
  subst hp3
  have hle : pLayerIn 3 H ≤ M := by rw [hbot]; exact bot_le
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  obtain ⟨hlist, hcard⟩ := nineTen_branchC_of_twelveCtx h10 h hEQ hE hEc hΓ hbot
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf d (H ⊓ M)
  have hk0 : 0 < (Nat.card (H ⊓ M : Subgroup G)).factorization d :=
    hdp.factorization_pos_of_dvd Nat.card_pos.ne' hdH
  have hD1 : D ≠ ⊥ := by
    intro hbotD
    have hcardD : Nat.card D = 1 := by rw [hbotD, Subgroup.card_bot]
    rw [hD.card_eq] at hcardD
    exact (Nat.one_lt_pow hk0.ne' hdp.one_lt).ne' hcardD
  let B := oneAmb 3 M H D
  let I := (oneImg 3 H (kSub 3 M H)).subgroupOf B
  let Dsub := (oneImg 3 H D).subgroupOf B
  let Y := (oneImg 3 H M ⊓ B).subgroupOf B
  obtain ⟨P, hp, hp2, hdp', hd2, hdne, hIeq, hDsyl, hDne, hPsyl, hYlt, hγ, hN⟩ :=
    exists_threeTenHyp_oneAmb hI h hns hd hle hD hD1
  have hDI : Dsub ≤ I :=
    Subgroup.subgroupOf_mono B (branchCThree_oneImg_le h10 h hbot rfl hC3.2 hd hD)
  obtain ⟨e₁⟩ := nonempty_oneImg_kSub_mulEquiv (p := 3) h hle
  let e : ↥I ≃* KStarQuot 3 M H :=
    (Subgroup.subgroupOfEquivOfLe (show oneImg 3 H (kSub 3 M H) ≤ B from le_sup_left)).trans e₁
  have hlistI : SixThreeOneList 3 ↥I := SixThreeOneList.of_mulEquiv e.symm hlist
  have hcardI : Nat.card ↥I ≠ 1 :=
    fun h1 => hcard ((Nat.card_congr e.toEquiv).symm.trans h1)
  have hhyp : CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenHyp I Dsub P Y 3 d :=
    ⟨hp, hp2, hdp', hd2, hdne, hIeq, hDsyl, hDne, hPsyl, hYlt, hγ, hN⟩
  have hconclOf := h310 (↥B) I Dsub P Y 3 d hp hp2 hdp' hd2 hdne hIeq hDsyl hDne hPsyl
    hYlt hγ hN
  have hSL : (IsSLType 2 (ZMod 3) ↥I ∨ IsPSLType 2 (ZMod 3) ↥I ∨
      IsSLType 3 (ZMod 3) ↥I) → d ∣ 3 + 1 :=
    fun hcase => (hconclOf (Or.inl hcase)).2.2.2.1
  have hSL5 : IsSLType 2 (ZMod 5) ↥I → d ∣ 3 + 1 :=
    fun hcase => (hconclOf (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hcase⟩)))).2.2.2.1
  have hA5 : IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) ↥I → d ∣ 3 + 1 :=
    fun hcase => (hconclOf (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr hcase⟩)))).2.2.2.1
  have h13 : IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) ↥I →
      False :=
    fun hext => CFSG.LocalAnalysis.AGL81I.Section3.threeTenCase5Thirteen_holds B I Dsub P Y d
      hhyp hext
  have hSp4 : (∃ W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)),
      oPPrimeHull 3 W = W ∧ Nonempty (↥I ≃* ↥W ⧸ CFSG.pCore 3 ↥W)) → False :=
    fun ⟨W, hW, ⟨eW⟩⟩ => hC3.1 (↥B) I Dsub P Y d hhyp hDI
      ⟨W, ⊥, inferInstance, hW, ⟨eW.trans
        (QuotientGroup.quotientBot (G := ↥W ⧸ CFSG.pCore 3 ↥W)).symm⟩⟩
  exact false_of_sixThreeOneList_three hdp hd2 hcardI hlistI hSL hSL5 hA5 h13 hSp4

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
