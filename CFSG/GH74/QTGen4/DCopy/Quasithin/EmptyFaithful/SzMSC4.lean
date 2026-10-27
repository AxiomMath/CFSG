module

public import CFSG.Quasithin.EmptyFaithful.SzMSC4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151ZH
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
  CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA CFSG.LieType.BorelTits
open scoped Pointwise

theorem input15122ThreeDHSRu_of_local_corr_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hMS : MS93.AS_C_1_34_corr_F4) (h1416 : StageLemma1416)
    (hloc : Input15122HSRuLocalCorr) : Input15122ThreeDHSRu_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D hx18 hHR
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow

  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (hsru_not_a38Types hHR)
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := (hc.h20.three hcomp).1

  have hLnot : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
    intro hle
    apply hc.hL.not_le
    have h1 : L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) = L := inf_eq_left.mpr hle
    have h2 : mZ1516 Mc Z₁ ⊓ L = L := h3D.2.trans h1
    exact h2 ▸ inf_le_left
  obtain ⟨K, hKL, hKS, hKcomp, hKsyl, hKchar, ⟨α, hα⟩, hKnot, hnoC⟩ :=
    hloc G L S hcomp.2.2 hZ hHR hS2 hSN hsyl hLnot
  have hKG : K ≤ g1_1516 Z₁ := hKL.trans hLG
  have hKSG : K ⊔ S ≤ g1_1516 Z₁ := sup_le hKG (s1516_le_g1 T Z₁)

  have hpc : pCoreOf 2 (K ⊔ S) ≠ ⊥ := by
    have h1 : pCoreOf 2 (g1_1516 Z₁) ≤ S := hc.h18.four.pCoreOf_le
    have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ pCoreOf 2 (K ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hKSG.trans (le_normalizer_pCoreOf 2 (g1_1516 Z₁)))
        (pCoreOf_isPGroup 2 (g1_1516 Z₁))
    exact ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) h2
  have hSQ : IsSQTKIn (K ⊔ S) :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc,
      kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc⟩
  have hchar : CharTwo (K ⊔ S) := zb_charTwo_sup hKS hS2 hKchar
  have hset : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K S hKS
  have hLie := SBd7.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) hc.h18.four.pCoreOf_le
  have hKperf : ⁅K, K⁆ = K := hKcomp.2.1
  by_cases hno : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ (K ⊔ S ≤ Subgroup.normalizer (C : Set G))
  ·
    have hMSp : IsMSPair (K ⊔ S) S :=
      S151S9.isMSPair_of_noChar hSQ hchar hKcomp hset hLie hKsyl hS0 hno
    obtain ⟨i, hi⟩ := hMS G (K ⊔ S) S K hMSp hKcomp hset
      ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
    exact hnoC i hi
  ·
    push Not at hno
    obtain ⟨C, hCS, hC0, hCchar, hKSC⟩ := hno
    have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
      S151S9.le_normalizer_of_char hCS hCchar hx18.s_normal
    have hC2 : IsPGroup 2 ↥C := hS2.to_le hCS
    have hCN : C ≤ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer
    have hCpc : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 hCN le_rfl hC2
    have hInH : InH T (Subgroup.normalizer (C : Set G)) :=
      ⟨hTC, ne_bot_of_le_ne_bot hC0 hCpc⟩
    obtain ⟨hperf1, hMc⟩ := (h1416 G T Mc hq).2.2.2 _ hInH
    have hKN : K ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hKSC
    have hKinf : K ≤ perfectCore (Subgroup.normalizer (C : Set G)) :=
      le_perfectCore_of_perfect hKN hKperf
    have hKMZ : K ≤ mZ1516 Mc Z₁ ⊓ L := fun x hx =>
      ⟨⟨hKG hx, hMc (hperf1 (hKinf hx))⟩, hKL hx⟩
    rw [h3D.2] at hKMZ
    exact hKnot fun x hx => (hKMZ hx).2

end CFSG.Quasithin
