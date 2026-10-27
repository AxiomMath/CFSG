module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5EFF
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FA

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

theorem res615EFF_of_cases_F4 (hB56 : AsB56)
    (hcases : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      (B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) ∨ B56Case3 (ffJ (autI hU (borelL T L ⊔ H))) ∨
        B56Case4 (ffJ (autI hU (borelL T L ⊔ H))) ∨
        B56Case5 (ffJ (autI hU (borelL T L ⊔ H)))) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF_F4 := by
  intro G _ _ T M L V H n c hN
  obtain ⟨-, hU, -⟩ := c.U_red_ch615
  have hne : ffJ (autI hU (borelL T L ⊔ H)) ≠ ⊥ := by
    intro hb
    have hK := (c.le_ffJ_ch615 hU).2
    rw [hb] at hK
    exact c.autI_oTwoUpper_ne_bot_ch615 hU (le_bot_iff.mp hK)
  rcases hB56 (IntMod (UX615 T L H) hU) IntMod.sq_eq_one _ hne (c.b53Hyp_ch615 hU) with
    h1 | h2 | h3 | h4 | h5
  · exact hcases G T M L V H n c hU hN (Or.inl h1)
  · exact absurd h2 (c.not_b56Case2_ch615 hU hN)
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inl h3))
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inr (Or.inl h4)))
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inr (Or.inr h5)))

end CFSG.Quasithin.H13
