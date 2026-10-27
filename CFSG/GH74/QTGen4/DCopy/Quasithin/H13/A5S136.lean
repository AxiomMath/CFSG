module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3

@[expose] def End136_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    (∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      (∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
        V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G)) ∧ ⁅V, conjSub g⁻¹ V⁆ = ⊥) →
    rParam V = 3 → 1 < wParam T V →
    (∀ H : Subgroup G, InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) → 1 < E1.nParam H) →
    (∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H → H ≤ Subgroup.normalizer (L : Set G)) →
      False

theorem input136_of_F4 (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hend : End136_F4) : Input136_F4 := by
  intro G _ _ T L V S hab
  have hr := S.rParam_eq_three_F4 h137 h1336 hab
  exact hend G T L V S hab
    (fun g hg hne => ⟨S.lemma_13_6_24_one_F4 h137 h1326 hab hg hne,
      S.lemma_13_6_24_two_F4 h137 h1326 hab hg hne⟩)
    hr (S.one_lt_wParam_F4 h137 h1326 hab hr)
    (fun H hH hHM => S.one_lt_nParam_F4 h137 h1326 h1336 hab hH hHM)
    (fun H hH hs => S.le_M_of_solvable_F4 h137 h1326 h1336 hab hH hs)

end CFSG.Quasithin.H13.A5
