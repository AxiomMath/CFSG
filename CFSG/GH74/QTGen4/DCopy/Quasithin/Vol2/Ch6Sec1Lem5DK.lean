module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DJ
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5DE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5DF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_normalizer_oTwoUpper_ch615_F4 (h432 : Stmt4_3_2_F4) (hDSB : DSBLoc_F4)
    (hR1 : L2RankOneSylowFact) (c : Cx615C G T M L V H n)
    (hK : borelL T L ≤ Subgroup.normalizer (oTwoUpper H : Set G)) : False := by
  obtain ⟨-, -, -, -, hcase⟩ := c.coords_ch615
  obtain ⟨S, P₁, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : ∃ S P₁ : Subgroup G, S ≤ T ∧
      T ⊓ L ≤ S ∧ S ≤ Subgroup.normalizer (P₁ : Set G) ∧
      borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (S ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) ∧ CharTwo (L ⊔ S) ∧
      CharTwo (P₁ ⊔ S ⊔ borelL T L) := by
    rcases hcase with ⟨ψ₁, hψ₁, hr₁⟩ | ⟨ψ, hψ, hr, t, htT, ht₁, -⟩
    · exact c.exists_s3_one_ch615 hR1 hK hψ₁ hr₁
    · exact c.exists_s3_two_ch615 hR1 hK hψ hr htT ht₁
  exact c.toCx615B.false_of_s3_ch615_F4 h432 hDSB h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem false_of_le_ch615_F4 (h432 : Stmt4_3_2_F4) (hDSB : DSBLoc_F4) (hR1 : L2RankOneSylowFact)
    (c : Cx615C G T M L V H n) (hCM : cXU615 T L H ≤ M)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) : False :=
  c.false_of_normalizer_oTwoUpper_ch615_F4 h432 hDSB hR1
    (c.borelL_le_normalizer_oTwoUpper_ch615_F4 h432 hCM hN)

end Cx615C

end CFSG.Quasithin.H13
