module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Stmt5_3_2At_F4 (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T t m f → IsSec53Param t m f →
      ∃ (Y : Type) (_ : Group Y), LieModel Y t m 2 f ∧
        IsExtensionOfLieAmalgam Y (sec53M1 L) (sec53M2 H)

variable {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}

theorem stmt5_3_2_of_at_F4 (hL3 : Stmt5_3_2At_F4 .PSL 3) (hSp : Stmt5_3_2At_F4 .PSp 2)
    (hG2 : Stmt5_3_2At_F4 .G2 0) (h3D4 : Stmt5_3_2At_F4 .trialityD4 0)
    (h2F4 : Stmt5_3_2At_F4 .twistedF4 0) (hU4 : Stmt5_3_2At_F4 .PSU 4) (hU5 : Stmt5_3_2At_F4 .PSU 5) :
    Stmt5_3_2_F4 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases hpar.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl, -⟩
  · exact hL3 G T M L V H B D L₂ n f hyp hty hpar
  · exact hSp G T M L V H B D L₂ n f hyp hty hpar
  · exact hG2 G T M L V H B D L₂ n f hyp hty hpar
  · exact h3D4 G T M L V H B D L₂ n f hyp hty hpar
  · exact h2F4 G T M L V H B D L₂ n f hyp hty hpar
  · exact hU4 G T M L V H B D L₂ n f hyp hty hpar
  · exact hU5 G T M L V H B D L₂ n f hyp hty hpar

end CFSG.Quasithin.H13
