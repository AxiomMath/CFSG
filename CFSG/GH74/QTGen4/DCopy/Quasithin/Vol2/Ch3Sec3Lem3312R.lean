module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312F
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312H

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Step3_3_12R_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D Y : Subgroup G), Hyp331 G T M L D →
    Y ∈ lFamilyOf L T → pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ → L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) →
    ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧
      (D ≤ Subgroup.normalizer (Y : Set G) ∨
        (IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          InducesInnerOn T Y))

theorem step3_3_12R_of_F4
    (h14 : Stmt3_3_14_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h36 : Vol2Native.A36ForSQTKCat) (h128 : Lemma128One)
    (hF : L3312.Facts3312) : Step3_3_12R_F4 := by
  intro G _ _ T M L D Y h hY hO htype
  have H : L3312.Hyp3312 G T M L D Y := ⟨h, hY, hO⟩
  have : IsSimpleGroup G := h.simple
  set X := Y ⊔ T ⊔ D with hX
  obtain ⟨K, hK, hYK⟩ := H.exists_cComp h37 h39
  have hHK := H.sup_le_normalizer_K_F4 h14 h37 h38 h128 hK hYK
  refine ⟨K, hK, hYK, hHK, ?_⟩
  have hKX : K ≤ X := le_of_mem_cComp hK
  have hlist := lemma_1_2_4_list h.qtke h.simple h.nonabelian h312 hO H.isSylowTwoOf_H
    (le_sup_left.trans le_sup_left) (mem_lFamily_of_isLocal H.isLocal) hK hYK
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36K := Vol2Native.lemma_1_2_1_four_strong hKc h36 hO hK
  obtain ⟨e⟩ := L3312.Hyp3312.modO2_equiv (T := T) (D := D) (Y := Y)
  have htype' : L3312.Type3312R (ModO2 (modO2Image X Y)) := L3312.Type3312R.of_equiv e htype
  have hYK' : modO2Image X Y ≤ modO2Image X K := Subgroup.map_mono fun y hy => hYK hy
  rcases L3312.oddNorm_or_j1 hF hYK' htype' h36K hlist with hc | hON
  · exact Or.inr (H.j1_case_F4 h14 h37 h128 hF.j1 hK hYK hHK hc htype)
  · exact Or.inl (H.le_normalizer_D_of_oddNorm_F4 h14 h37 h128 hKX hYK hHK hON)

end CFSG.Quasithin.H13
