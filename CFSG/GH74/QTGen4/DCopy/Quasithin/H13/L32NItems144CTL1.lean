module

public import CFSG.Quasithin.H13.L32NItems144CTL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem normalizer_le_M_F4 (h13322 : Stmt13_3_2_two_F4) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, huniq⟩ := h13322 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  exact normalizer_le_of_unique huniq hP1 hP2 hLT

theorem false_of_H_le_F4 (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4) (hV : StmtL32NModule_F4)
    (hD : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hH : l32nH T V ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    False :=
  lemma12_8_3_four_F4 h12213 (S.hyp.hyp1281One_F4 h13322 hV) (S.hyp.isTSub_fsuV1_F4 hV)
    (hH.trans (normalizer_le_M_F4 S h13322 hD (isPGroup_D S) (LT_le_normalizer S)))

theorem H_le_of_K_le_F4 (hV : StmtL32NModule_F4)
    (hK : oTwoUpper (l32nH T V) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    l32nH T V ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow (S.hyp.isSylowTwoOf_l32nH_F4 hV)]
  exact sup_le hK (T_le_normalizer S)

theorem false_of_normalizes_F4 (h12213 : Stmt12_2_13_F4) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (hD : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {x : G}
    (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
    (hx₁ : x ∈ Subgroup.normalizer (Q₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (Q₂ : Set G)) :
    False :=
  false_of_H_le_F4 S h12213 h13322 hV hD (H_le_of_K_le_F4 S hV fun _ hk =>
    mem_normalizer_of_inv S hxW hk (S.inv_of_normalizes hxW hxQ hx₁ hx₂ hk))

end Setup

end L1444CTL

end CFSG.Quasithin.H13
