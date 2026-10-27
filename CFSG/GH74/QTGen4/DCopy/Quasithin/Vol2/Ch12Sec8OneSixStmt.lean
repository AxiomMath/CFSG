module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def Lemma12_8_13_six_hat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → 4 ≤ n → ∀ D : HatModelU (u128 V V₁),
      ¬ G112Concl4 (D.img (Subgroup.normalizer (V₁ : Set G)))

end CFSG.Quasithin.H13
