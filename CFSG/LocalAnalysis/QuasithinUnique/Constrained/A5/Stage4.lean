module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4M1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs314
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem O2_cent_le_TC (C : StdCfg T M H S L) (hQ : blockQ L = blockU L) {t : G}
    (hSyl : IsSylowTwoOf S (Subgroup.centralizer ({t} : Set G)))
    (hHC : H ≤ Subgroup.centralizer ({t} : Set G))
    (hU : ¬ blockU L ≤ pCoreOf 2 (Subgroup.centralizer ({t} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ blockTC T S L := by
  set Cc : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCc
  set W : Subgroup G := pCoreOf 2 Cc with hW
  have hZ : blockZ L = ⊥ := blockZ_eq_bot C.hcs C.F C.hj (blockU_le_S C.hcs C.hj)
  have hWS : W ≤ S := pCoreOf_two_le_of_sylowIn hSyl.1 hSyl.2.1 hSyl.2.2
  have hLH : L ≤ H := C56.le_H C.hcs
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    (hLH.trans hHC).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Cc)
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs =>
    C56.H_le_normalizer C.hcs C.hj (C.hcs.sylow.le hs)
  have hWU : blockU L ⊓ W = ⊥ := by
    have hLN : L ≤ Subgroup.normalizer ((blockU L ⊓ W : Subgroup G) : Set G) := by
      intro l hl
      have h1 : l ∈ Subgroup.normalizer (blockU L : Set G) :=
        C1.mem_normalizer_blockU (C56.H_le_normalizer C.hcs C.hj (hLH hl))
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, hLW hl⟩
    have := (C56.isShort C.hcs).2.2.2.2.2 (blockU L ⊓ W) (by rw [hZ]; exact bot_le) inf_le_left hLN
    rcases this with h | h
    · rw [h, hZ]
    · exfalso
      apply hU
      intro u hu
      have : u ∈ blockU L ⊓ W := by rw [h]; exact hu
      exact this.2
  have hcomm : ∀ w ∈ W, ∀ l ∈ L, w * l = l * w := by
    intro w hw l hl
    have hc1 : w * (l * w⁻¹ * l⁻¹) ∈ W :=
      mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hLW hl) w⁻¹).mp (inv_mem hw))
    have hc2 : (w * l * w⁻¹) * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hSL (hWS hw)) l).mp hl) (inv_mem hl)
    have hcW : (w * l * w⁻¹) * l⁻¹ ∈ W := by
      have : (w * l * w⁻¹) * l⁻¹ = w * (l * w⁻¹ * l⁻¹) := by group
      rw [this]
      exact hc1
    have hWL : W ⊓ L ≤ pCoreOf 2 L := by
      refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (W ⊓ L) L
        inf_le_right ?_ ?_
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
        intro l' hl'
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLW hl', Subgroup.le_normalizer hl'⟩
      · exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Cc).to_le inf_le_left
    have hcU : (w * l * w⁻¹) * l⁻¹ ∈ blockU L := by
      rw [← hQ]
      exact hWL ⟨hcW, hc2⟩
    have hc : (w * l * w⁻¹) * l⁻¹ ∈ blockU L ⊓ W := ⟨hcU, hcW⟩
    rw [hWU, Subgroup.mem_bot] at hc
    calc w * l = (w * l * w⁻¹ * l⁻¹) * (l * w) := by group
      _ = l * w := by rw [hc, one_mul]
  intro w hw
  have hwT : w ∈ T := C.hcs.le_T (hWS hw)
  show w ∈ T ⊓ Subgroup.centralizer (conjJoin S L : Set G)
  rw [C.hj]
  exact Subgroup.mem_inf.mpr ⟨hwT, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    (hcomm w hw l hl).symm⟩

theorem TC_eq_bot (h314 : A314A5Excluded) (C : StdCfg T M H S L) (h5 : IsAltType L 5)
    (hQ : blockQ L = blockU L) : blockTC T S L = ⊥ := by
  by_contra hne
  obtain ⟨t, ht, ht1, hsmall, hxt⟩ := C.TC_structure hne
  set Cc : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCc
  have hcomm : ∀ c ∈ Cc, c * t = t * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hc t (Set.mem_singleton t)).symm
  have hHC : H ≤ Cc := by
    intro h hh
    rw [hCc, Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact C.TC_comm_H ht hh
  have hTCC : blockTC T S L ≤ Cc := by
    intro a ha
    rw [hCc, Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact C.TC_comm_TC ht ha
  have hTCle : blockTC T S L ≤ pCoreOf 2 Cc := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (blockTC T S L) Cc
      hTCC ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTCC]
      refine C5.le_normalizer_of_commute ?_
      intro c hc a ha
      rcases hsmall a ha with rfl | rfl
      · simp
      · exact hcomm c hc
    · exact C.hcs.setting.isPGroup.to_le inf_le_left
  have hCbot : pCoreOf 2 Cc ≠ ⊥ := by
    intro h
    apply ht1
    have : t ∈ pCoreOf 2 Cc := hTCle ht
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hΓ : IsGamma M Cc := by
    obtain ⟨-, U, HU, hp, hle⟩ := C.hcs.gamma0.isGamma
    exact ⟨hCbot, U, HU, hp, hle.trans hHC⟩
  have hSyl : IsSylowTwoOf S Cc :=
    (C.hcs.gamma0.overgroup_of_le C.hcs.setting C.hcs.sylow_inf hΓ hHC).2.1
  have hSQTK : CFSG.SectionRank.IsSQTKCat ↥Cc := C.hcs.setting.qtke.1 Cc hCbot
  have hU := C.U_not_le_O2_cent hne ht hxt
  have hO2 := C.O2_cent_le_TC hQ hSyl hHC hU
  have hZ : blockZ L = ⊥ := blockZ_eq_bot C.hcs C.F C.hj (blockU_le_S C.hcs C.hj)
  have hLH : L ≤ H := C56.le_H C.hcs
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs =>
    C56.H_le_normalizer C.hcs C.hj (C.hcs.sylow.le hs)
  refine h314 G Cc S L hSQTK hSyl hCbot ?_ (hLH.trans hHC) (C56.isShort C.hcs) h5 hQ hZ hSL
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  rcases hsmall w (hO2 hw) with rfl | rfl
  · simp
  · exact hcomm c hc

end StdCfg

theorem a5_TC_eq_bot
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) : blockTC T S L = ⊥ := by
  have hcs := cfg.cs
  have hj := cfg.single
  have F := h247_facts h247 hcs cfg.alt5 hj
  have hQ := blockQ_eq_blockU h245_4 hcs hj
  obtain ⟨D, hsurj, hker, hRE, hRE', hHeq⟩ := exists_stdData hcs hj cfg.alt5 F hQ hC54
  exact StdCfg.TC_eq_bot h314 ⟨hcs, hj, F, D, hsurj, hker, hRE, hRE', hHeq⟩ cfg.alt5 hQ

theorem lemma2_4_29_4
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_4 := by
  intro G _ _ T M H S L cfg _
  exact a5_TC_eq_bot h247 h245_4 hC54 h314 cfg

end CFSG.QuasithinUnique.A5
