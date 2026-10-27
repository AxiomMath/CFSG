module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem515

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem isUniqueM_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) : IsUniqueM (L ⊔ T) M := by
  obtain ⟨⟨-, -, huniq⟩, -⟩ :=
    (h331 G T h.simple h.nonabelian h.qtke h.sylow).2 L h.maximal h.isQuasisimple
  rw [h.conjClosure_eq] at huniq
  have hM : M = Subgroup.normalizer (L : Set G) := huniq M h.maxTwoLocal h.sup_le_M
  refine ⟨⟨h.maxTwoLocal, h.sup_le_M⟩, fun M' hM' => ?_⟩
  rw [huniq M' hM'.1 hM'.2, hM]

theorem not_le_of_isHStar_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) {H : Subgroup G}
    (hH : IsHStar T M H) : ¬ L ≤ H := by
  intro hLH
  have h1 := pCoreOf_sup_eq_bot_of_isUniqueM (h.isUniqueM_F4 h331) hH.2.1
  have h2 : (L ⊔ T) ⊔ H = H := sup_eq_right.mpr (sup_le hLH hH.1.1)
  rw [h2] at h1
  exact hH.1.2 h1

theorem inf_le_borel_of_isHStar_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) : H ⊓ L ≤ borelL T L := by
  have hRA := h.rankOneAt hR
  have hne : H ⊓ L ≠ L := fun heq =>
    h.not_le_of_isHStar_F4 h331 hH (heq.symm.le.trans inf_le_left)
  exact le_inf inf_le_right
    (hRA.unique_max (H ⊓ L) (inf_le_inf_right L hH.1.1) inf_le_right hne)

theorem pCoreOf_inf_eq_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    {H : Subgroup G} (hH : IsHStar T M H) : pCoreOf 2 (H ⊓ L) = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  have hTHL : T ⊓ L ≤ H ⊓ L := inf_le_inf_right L hH.1.1
  have hSHL : IsSylowTwoOf (T ⊓ L) (H ⊓ L) := A4.isSylowTwoOf_mono hSL hTHL inf_le_right
  apply le_antisymm (F7.isSylowTwoOf_pCoreOf_le hSHL)
  exact le_pCoreOf_of_le_normalizer 2 hTHL
    ((h.inf_le_borel_of_isHStar_F4 h331 hR hH).trans inf_le_right) hSL.2.1

theorem inf_le_normalizer_inf_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) :
    H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have h1 : H ⊓ M ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans h.normal)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have h2 := h1.trans (normalizer_le_normalizer_pCoreOf 2 (H ⊓ L))
  rwa [h.pCoreOf_inf_eq_F4 h331 hR hH] at h2

theorem inf_le_normalizer_borel_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) {H : Subgroup G} (hH : IsHStar T M H) :
    H ⊓ M ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  have h1 : H ⊓ M ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans h.normal
  have h2 : H ⊓ M ≤ Subgroup.normalizer
      ((Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    (h.inf_le_normalizer_inf_F4 h331 hR hH).trans Subgroup.le_normalizer
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem lemma_5_1_5_one_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    {H D : Subgroup G} (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    H ⊓ M ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (D ⊔ T) : Set G) := by
  refine ⟨h.inf_le_normalizer_inf_F4 h331 hR hH, ?_⟩
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  have hSB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono hSL (inf_le_borel T L) inf_le_left
  have hB : D ⊔ (T ⊓ L) = borelL T L := sup_eq_of_isHall_isSylow hD hSB
  have hDT : D ⊔ T = borelL T L ⊔ T := by
    apply le_antisymm (sup_le_sup_right hD.1 T)
    rw [← hB]
    exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
  rw [hDT, oTwoUpper_sup_eq_of_isPGroup h.sylow.1 h.T_le_normalizer_borel]
  exact (h.inf_le_normalizer_borel_F4 h331 hR hH).trans (normalizer_le_normalizer_oTwoUpper _)

end Hyp5_0_1

end CFSG.Quasithin.H13
