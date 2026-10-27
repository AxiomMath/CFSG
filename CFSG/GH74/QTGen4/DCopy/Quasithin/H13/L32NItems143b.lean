module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32NItems143b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Lemma14312One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
          2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) →
        Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) =
            2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) ∧
          2 * Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) = Module.finrank (ZMod 2) D.V ∧
          (centerOf (fsuU T V) = fsuV1 T V ∧ CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) ∧
            l32nCHat T V = pCoreOf 2 (l32nH T V)) ∧
          ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
            (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
            (∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v) ∧
            ∀ e ∈ D.hat (l32nE T V V₂ g), q e = 0

@[expose] def Lemma14323Rest_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Module.finrank (ZMod 2) D.V = 4 →
      (D.hat V = D.hat (l32nE T V V₂ g) ∧ Nat.card ↥(D.hat V) = 4) ∧
      (Case14323i T L V g D ∨ Case14323ii T V g D ∨ Case14323iii T V g D ∨
        Case14323iv T L V D) ∧
      ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
          (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ∧
        ∀ x ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g), ∀ v ∈ D.hat V, x v = v) ∧
      (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) ⊔ l32nCHat T V < l32nH T V

@[expose] def Lemma14324One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      G112Concl6 (D.img (l32nH T V)) ∨
        (Module.finrank (ZMod 2) D.V = 4 ∧
          (Case14323i T L V g D ∨ Case14323ii T V g D ∨ Case14323iii T V g D))

@[expose] def Lemma14325One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    centerOf (L ⊔ T) ⊓ fsuU T V = ⊥

@[expose] def Lemma14331One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → centerOf (i128 T L V (fsuV1 T V)) = ⊥

end CFSG.Quasithin.H13
