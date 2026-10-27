module

public import CFSG.CGT.PushingUpLit.SolKNA.Config
public import CFSG.CGT.PushingUpLit.SolKNA.CaseData
public import CFSG.CGT.PushingUpLit.SolKR2.Top
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.RankThree.GF2n (inf_conjSubgroup_eq_bot_of_isTI conjSubgroup_eq_self_iff)
open CFSG.RankThree.PartTwo (omegaOneSub)
open CFSG.RankThree.GF2n.Tim78 (omegaTwoSub mem_omegaTwoSub_iff)
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly (pCoreOf)

variable {G : Type} [Group G]

theorem exists_sylow_sylowImg_eq {H : Subgroup G} (h2 : IsPGroup 2 H) :
    ∃ R : Sylow 2 H, sylowImg R = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTop : IsPGroup 2 (⊤ : Subgroup ↥H) := h2.of_equiv Subgroup.topEquiv.symm
  obtain ⟨R, hR⟩ := hTop.exists_le_sylow
  refine ⟨R, ?_⟩
  have hRtop : (R : Subgroup ↥H) = ⊤ := top_le_iff.mp hR
  show (R : Subgroup ↥H).map H.subtype = H
  rw [hRtop, Subgroup.map_top, Subgroup.range_subtype]

variable [Finite G]

theorem normalizer_eq_of_normal {K H : Subgroup G} (S : STSetting G K) (hH2 : IsPGroup 2 H)
    (hH1 : H ≠ ⊥)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    Subgroup.normalizer (H : Set G) = Subgroup.normalizer (K : Set G) := by
  by_contra hne
  exact S.max.2 _ (lt_of_le_of_ne hHM (Ne.symm hne)) ⟨H, hH1, hH2, rfl⟩

omit [Finite G] in
theorem le_pCoreOf_of_normal {K H : Subgroup G} (hHK : H ≤ K) (hH2 : IsPGroup 2 H)
    (hKH : K ≤ Subgroup.normalizer (H : Set G)) : H ≤ pCoreOf 2 K := by
  rw [pCoreOf_eq_inSubgroup_pCore]
  exact CFSG.RankThree.GF2n.Tim78.le_inSubgroup_pCore hHK hKH hH2

theorem STSetting.of_normal {K H : Subgroup G} (S : STSetting G K) (hH2 : IsPGroup 2 H)
    (hH1 : H ≠ ⊥) (hHK : H ≤ pCoreOf 2 K)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    STSetting G H := by
  have hN := normalizer_eq_of_normal S hH2 hH1 hHM
  have hTI : IsTI H := isTI_of_normal_le_pCoreOf S.tight hHK hHM
  refine ⟨S.simple, S.nonab, ⟨?_, fun g hg => ?_⟩, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hH1 (Subgroup.card_eq_one.mp (by rw [hk]; rfl))
    rw [hk]
    exact Nat.even_pow.mpr ⟨even_two, hk0⟩
  · have hne : conjSubgroup g⁻¹ H ≠ H := fun h' => hg (by
      have := conjSubgroup_eq_self_iff.mp h'
      simpa using (Subgroup.normalizer (H : Set G)).inv_mem this)
    have hbot : H ⊓ conjSubgroup g⁻¹ H = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hne
    show Odd (Nat.card ↥(H ⊓ conjSubgroup g⁻¹ H))
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  · rw [hN]
    exact S.max
  · rw [hN]
    exact S.fstar

section C0


theorem abelian_TI_false {H : Subgroup G} (S : STSetting G H) (hHc : IsCommSubgroup H)
    (hH2 : IsPGroup 2 H) (hel : ¬ IsElemAbelian 2 H) (hcyc : ¬ IsCyclic H) : False := by
  classical
  have := S.simple
  obtain ⟨R, hR⟩ := exists_sylow_sylowImg_eq hH2
  have hc : IsCommSubgroup (sylowImg R) := by rw [hR]; exact hHc
  have hne : ¬ IsElemAbelian 2 (sylowImg R) := by rw [hR]; exact hel
  have h2 : IsPGroup 2 (sylowImg R) := isPGroup_sylowImg R
  have hH1 : sylowImg R ≠ ⊥ := by
    intro hbot
    have hbot' : H = ⊥ := hR.symm.trans hbot
    apply hcyc
    rw [hbot']
    infer_instance
  rcases omegaOne_card_cases hc h2 hH1 with hc2 | hc4 | hc8
  · exact hcyc (by rw [← hR]; exact isCyclic_of_card_omegaOne_two hc h2 hc2)
  · obtain ⟨e⟩ := S.nonempty_omegaTwoSub_equiv_of_card_omegaOne_four R hc hne hc4
    have hR2 : SolKR2.R2 (Subgroup.normalizer (H : Set G)) (sylowImg R) :=
      SolKR2.R2.of_rankTwo S R hc hne hc4 ⟨omegaTwoSub (sylowImg R),
        fun x => mem_omegaTwoSub_iff hc, ⟨e⟩⟩
    exact SolKR2.R2.false_of_facts S.nonab SolKR2.r2First_holds hR2
      (SolKR2.R2Facts.of_lemmas SolKR2.r2Weak_holds SolKR2.r2First_holds hR2)
  · exact hne (S.isElemAbelian_sylowImg_of_eight_le R hc hc8)

theorem caseI_normal_false {K R T : Subgroup G} {g : G} (cfg : NAConfig G K R T g)
    (hI : CaseI K R T)
    (hNM : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G)) :
    False := by
  have hNR : R ⊓ Subgroup.normalizer (T : Set G) ≤ R := inf_le_left
  have hNK : R ⊓ Subgroup.normalizer (T : Set G) ≤ K := hNR.trans cfg.R_le_K
  have hN2 : IsPGroup 2 ↥(R ⊓ Subgroup.normalizer (T : Set G)) := cfg.sylowR.isPGroup.to_le hNR
  obtain ⟨e⟩ := hI.iso
  have hcard : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T :=
    Nat.card_congr e.toEquiv
  have hN1 : R ⊓ Subgroup.normalizer (T : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact cfg.T_ne (Subgroup.eq_bot_of_card_eq _ hcard.symm)
  have hKN : K ≤ Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
      Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hI.normal
  have S : STSetting G (R ⊓ Subgroup.normalizer (T : Set G)) :=
    STSetting.of_normal cfg.stSetting hN2 hN1 (le_pCoreOf_of_normal hNK hN2 hKN) hNM
  refine abelian_TI_false S hI.comm hN2 (fun hel => ?_) hI.not_cyclic
  obtain ⟨n, hn, hn2⟩ := hI.exists_sq_ne
  apply hn2
  rw [← sq]
  exact hel.2 n hn

end C0

end CFSG.CGT.PushingUpLit.SolKNA
