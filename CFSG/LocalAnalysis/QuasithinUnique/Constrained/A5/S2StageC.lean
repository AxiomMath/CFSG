module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2B3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25C

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC

namespace S2.Ctx

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {t : G}
  (c : S2.Ctx T M H S L t)
include c

theorem local_of_star {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block) (hP2 : NoProperA5Block)
    (X S₁ : Subgroup G) (hXc : CharTwo X) (hLX : L ⊔ s2SI S L ≤ X)
    (hXφ : X ≤ Subgroup.normalizer (s2Phi S L : Set G)) (hS₁ : IsSylowTwoOf S₁ X)
    (hS₁S : s2SI S L ≤ S₁) : quasithinIsLocal S₁ L := by
  have hYX : L ⊔ S₁ ≤ X := sup_le (le_sup_left.trans hLX) hS₁.1
  have hS₁Y : IsSylowTwoOf S₁ (L ⊔ S₁) := S2.isSylow_of_le_of_le hS₁ le_sup_right hYX
  have hOX : pCoreOf 2 X ≤ S₁ := pCoreOf_two_le_of_sylowIn hS₁.1 hS₁.2.1 hS₁.2.2
  have hYc : CharTwo (L ⊔ S₁) :=
    charTwo_of_pCore_centralizer_le hXc hYX fun y hy => (le_sup_right : S₁ ≤ L ⊔ S₁) (hOX hy.1)
  have hLSI : L ⊔ s2SI S L ≤ L ⊔ S₁ := sup_le le_sup_left (hS₁S.trans le_sup_right)
  have hstar := c.star hE hI h37 h39 hP1 hP2 (L ⊔ S₁) hYc hLSI (hYX.trans hXφ)
    ⟨S₁, hS₁Y, hS₁S, rfl⟩
  have hφY : s2Phi S L ≤ L ⊔ S₁ :=
    phi_le_I.trans (s2I_le_baum.trans (c.R_le_SI.trans (hS₁S.trans le_sup_right)))
  have hpY : pCoreOf 2 (L ⊔ S₁) ≠ ⊥ := by
    intro hbot
    apply c.phi_ne hE hI
    have : s2Phi S L ≤ pCoreOf 2 (L ⊔ S₁) :=
      le_pCoreOf_of_normalizes hφY (hYX.trans hXφ) c.phi_isPGroup
    rw [hbot] at this
    exact le_bot_iff.1 this
  exact ⟨hS₁.2.1, hstar, hS₁Y.2.2, hpY⟩

end S2.Ctx

theorem lemma2_4_25_C (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block)
    (hP2 : NoProperA5Block) (hK : Comp25Component) (hList : Comp25List) : Lemma2_4_25_C := by
  intro G _ _ T M H S L cfg x hxT hxN hxU hB
  obtain ⟨t, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  obtain ⟨P₂, hE, hI⟩ := c.exists_P₂
  obtain ⟨K, hKc, hLK, hKn⟩ := hK G T M H S L cfg x hxT hxN hxU hB
  obtain ⟨hKl, hKz⟩ := hList G T M H S L cfg x hxT hxN hxU hB K hKc hLK
  refine ⟨K, { hB with
    K_comp := hKc
    L_le := hLK
    K_list := hKl
    K_center := hKz
    local_all := fun T_I hTI hSIT => ⟨?_, fun X S₁ hXc hLX hXK hS₁ hS₁S => ?_⟩ }⟩
  · exact hTI.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKc.1).1 hKn)
  · have hKN : K ≤ Subgroup.normalizer (s2Phi S L : Set G) := hKc.1
    have hXφ : X ≤ Subgroup.normalizer (s2Phi S L : Set G) :=
      hXK.trans (sup_le hKN hTI.1)
    exact c.local_of_star hE hI h37 h39 hP1 hP2 X S₁ hXc hLX hXφ hS₁ hS₁S

end CFSG.QuasithinUnique.A5
