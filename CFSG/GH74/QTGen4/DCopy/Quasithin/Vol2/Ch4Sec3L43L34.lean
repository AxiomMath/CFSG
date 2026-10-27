module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3Core

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def Lemma43Upto_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      C41Case3 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ →
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ZS K₂ R₂ X KZ Γ A B : Subgroup G)
        (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
        (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
        Config43L34 G T M L n I H K t F ZS K₂ R₂ X KZ Γ A B α P

theorem lemma43End_of_F4 (hUpto : Lemma43Upto_F4) (hB414 : LemmaB414Corrected)
    (hgap : Gap432L34Twisted) : Lemma43End_F4 := by
  intro G _ _ T M L n I H K t sk hchar h41 h3 h134 hcent
  obtain ⟨F, _, _, ZS, K₂, R₂, X, KZ, Γ, A, B, α, P, c⟩ :=
    hUpto G T M L n I H K t sk hchar h41 h3 h134 hcent
  exact false_of_config43L34 hB414 hgap c

end CFSG.Quasithin.H13.Ch4
