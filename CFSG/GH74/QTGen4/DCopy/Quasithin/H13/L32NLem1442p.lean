module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Case1442FromConcl9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)), L1442.Ctx_F4 G T L V V₂ g a D →
      G112Concl9 (D.img (l32nH T V)) → Case1442Five T V V₂ g D

@[expose] def Case1442FromConcl13S_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)), L1442.Ctx_F4 G T L V V₂ g a D →
      G11.SzG11S.G112Concl13S (D.img (l32nH T V)) → Case1442Six T V V₂ g D

theorem lemma1442Big_of_inputs_F4
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12813 : Lemma12_8_13_F4) (h14312 : Lemma14312One_F4) (hFixS : G11.SzG11S.TheoremG112FixS)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h9 : Case1442FromConcl9_F4) (h13 : Case1442FromConcl13S_F4) : Lemma1442Big_F4 := by
  intro G _ _ T L V h hext hU32 V₂ g hV₂ hgP hgH D
  obtain ⟨a, C⟩ := L1442.exists_ctx_F4 h1332 h1334 h1222 h12213 h12813 h14312 hFixS h37 h38 h39 h
    hext hU32 hV₂ hgP hgH D
  rcases C.fixS with (c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13) | c8s |
    c6u
  · exact (C.false_of_concl1_F4 c1).elim
  · exact (C.false_of_concl2_F4 c2).elim
  · exact (C.false_of_concl3_F4 c3).elim
  · exact (L1442.Ctx.false_of_concl4_F4 C c4).elim
  · exact (C.false_of_concl5_F4 c5).elim
  · exact (C.false_of_concl6_F4 h12213 c6).elim
  · exact Or.inl (C.case3_of_concl7_F4 h12213 c7)
  · exact Or.inr (Or.inl (C.case4_of_concl8_F4 h12213 c8))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h9 G T L V V₂ g a D C c9))))
  · exact (C.false_of_concl10_F4 c10).elim
  · exact (C.false_of_concl11_F4 h12813 c11).elim
  · exact (C.false_of_concl12_F4 c12).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h13 G T L V V₂ g a D C c13))))
  · exact (C.false_of_concl8S8_F4 c8s).elim
  · exact (C.false_of_concl6U33_F4 c6u).elim

end CFSG.Quasithin.H13
