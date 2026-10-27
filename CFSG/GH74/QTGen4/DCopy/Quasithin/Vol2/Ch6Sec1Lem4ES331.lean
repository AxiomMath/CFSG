module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Hyp611.normalizer_thompsonJ_le_ch614_F4 (h331 : Stmt3_3_1_F4) {T M L V : Subgroup G} {n : ℕ}
    (h : Hyp611 G T M L V n) (hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, -, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  have hJ : thompsonJ T ≠ ⊥ := by
    intro hJ
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀b : A₀ = ⊥ := le_bot_iff.mp (hJ ▸ B6.le_thompsonJ hA₀)
    have hV := hA₀.2.2 V h.le_T h.isElemAbelian
    rw [hA₀b, Subgroup.card_bot] at hV
    exact h.ne_bot (Subgroup.eq_bot_of_card_le V hV)
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := h.sylow.1.to_le (B6.thompsonJ_le T)
  have hO : pCoreOf 2 (Subgroup.normalizer (thompsonJ T : Set G)) ≠ ⊥ := fun h0 =>
    hJ (le_bot_iff.mp (h0 ▸ CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hJ2))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hM'eq := huniq M' hM'.1 (hJN.trans hM'.2)
  rw [hMeq, ← hM'eq]
  exact hM'.2

end CFSG.Quasithin.H13
