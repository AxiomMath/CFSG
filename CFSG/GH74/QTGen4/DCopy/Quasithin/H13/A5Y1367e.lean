module

public import CFSG.Quasithin.H13.A5Y1367e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem list_of_inYz_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h56 : AsB56) (hH : S.Hyp1367) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.IsQuasisimple ↥(S.plus K) ∧ B56QuasisimpleList ↥(S.plus K) := by
  have hF := hH.hF
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hK hT
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hWT := (S.WK_le_Tv_F4 h1222 h517 hF hK.1 hT).1
  have hSQ := S.sqtkGroup_HK_F4 h1222 h517 hF hK.1 hT
  have hKJ := S.plus_le_jStar_F4 h1222 h517 hF hK hT
  have hJne : autOn (thompsonJ S.Tv) (S.WK K) ≠ ⊥ := by
    intro h
    have h1 := S.plus_eq_commutator_F4 h1222 h517 hF hK hT
    rw [h, Subgroup.commutator_bot_right] at h1
    exact (qs_perfect_ne_bot hq).2 h1.symm
  have hcases := b56Cases_jStar h56 hWT (S.Tv_le_HK K) hR hSQ hJne
  have hNn : ∀ x ∈ jStar (S.HK K) S.Tv (S.WK K), ∀ n ∈ S.plus K, x * n * x⁻¹ ∈ S.plus K :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp
      (S.HK_le_normalizer_plus_F4 h1222 h517 hF hK hT (jStar_le (S.Tv_le_HK K) hx)) n).mp hn
  exact ⟨hq, b56List_of_qs_normal hKJ hNn hq hcases⟩

end Setting

theorem list1367_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h56 : AsB56) : List1367_F4 := by
  intro G _ _ T L V S hH K hK hT
  exact S.list_of_inYz_F4 h1222 h517 h56 hH hK hT

end CFSG.Quasithin.H13.A5
