module

public import CFSG.Quasithin.H13.L32NLem1442e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtL128Quad

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L1442.Ctx_F4

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem exists_quad_F4 (h12213 : Stmt12_2_13_F4) :
    ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
      (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
      ∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v := by
  have hfr : frattiniOf (centerOf (fsuU T V)) = ⊥ := by
    rw [C.base.zU]
    exact L14312.frattiniOf_eq_bot_of_card_two C.card_V1
  exact (lemma12_8_8_two_of_F4 C.base.h1222 h12213 G T L V 3 (fsuV1 T V) V₂ C.base.s1282
    D).2.2.2 hfr

theorem false_of_concl6_F4 (h12213 : Stmt12_2_13_F4) (h6 : G112Concl6 (D.img (l32nH T V))) : False := by
  obtain ⟨q, -, hq, hΓ⟩ := C.exists_quad_F4 h12213
  have hle : D.img (l32nH T V) ≤ G11.orthSub q := fun γ hγ v => hΓ γ hγ v
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h6.2] at hdvd
  rcases card_orthSub_six ⟨C.g111.alt, C.g111.nondegenerate⟩ hq h6.1 with h | h
  · rw [h] at hdvd
    exact absurd hdvd (by decide)
  · rw [h] at hdvd
    exact absurd hdvd (by decide)

end Ctx_F4

end L1442

end CFSG.Quasithin.H13
