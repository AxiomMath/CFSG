module

public import CFSG.Quasithin.Vol2.Ch4Sec3Core
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3Thm432

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem exists_setting432K_F4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∃ (K : Subgroup G) (t : G), Setting432K G T M L n I H K t := by
  obtain ⟨K, hK, hKq, hLK, h1, hKM, hMK, hdesc⟩ := s.exists_K_F4 hR hC hC48 hInsp h36 h37 h38 h39
  obtain ⟨t, htT, htN, htS, ht2, htR⟩ := s.exists_t h37 h38 h39
  exact ⟨K, t, s, hK, hKq, hLK, h1, hKM, hMK, hdesc, htT, htN, htS, ht2, htR⟩

end Setting432

@[expose] def Lemma43End_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      C41Case3 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ → False

theorem core432_of_F4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h436 : Lemma436Comp) (hSp4 : Lemma437Sp4)
    (hA7 : Lemma437A7) (hSL3 : Lemma437SL3) (h439 : Lemma439) (h4310 : Lemma4310)
    (hEnd : Lemma43End_F4) : Core432_F4 := by
  intro G _ _ T M L n I H s
  obtain ⟨K, t, sk⟩ := s.exists_setting432K_F4 hR hC hC48 hInsp h36 h37 h38 h39
  rcases sk.desc with ⟨hcomp, h31⟩ | ⟨-, hchar, -, -, h41⟩
  · exact h436 G T M L n I H K t sk hcomp h31
  · have h438 := concl438_of sk hchar h41 hSp4 hA7 hSL3
    have hCS := h439 G T M L n I H K t sk hchar h41 h438
    have hcase3 := h4310 G T M L n I H K t sk hchar h41 h438 hCS
    exact hEnd G T M L n I H K t sk hchar h41 h438.1 hcase3 hCS

end CFSG.Quasithin.H13.Ch4
