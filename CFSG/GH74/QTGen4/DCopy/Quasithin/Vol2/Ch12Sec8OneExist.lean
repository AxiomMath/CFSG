module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneExist
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Hyp1223.le_and_normalizes_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G}
    (h : Hyp1223 G T L V) : V ≤ T ∧ T ≤ normalizer (V : Set G) := by
  rcases h1222 G T h.simple h.nonabelian h.qtke h.sylow with hAlt | h3
  · exact absurd hAlt h.notAlt
  obtain ⟨-, -, hall⟩ := h3 L h.maximal h.faithful h.quasisimple
  exact ⟨(hall V h.irrPlus).1.1, (hall V h.irrPlus).1.2.1⟩

theorem exists_v1_of_hyp1281One_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : ∃ V₁ : Subgroup G, IsTSub T V V₁ 1 := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  exact exists_tsub h.hyp.sylow.1 hsq hab hTV hcard 1 hn

theorem exists_v2_of_hyp1281One_F4 (h1222 : Stmt12_2_2_F4) {T L V V₁ : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hV₁ : IsTSub T V V₁ 1) :
    ∃ V₂ : Subgroup G, IsTSub T V V₂ 2 ∧ V₁ ≤ V₂ := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hn : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  exact exists_tsub_two_of_one h.hyp.sylow.1 hsq hab hTV hcard hn hV₁

@[expose] def Exist1282g_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G)

end CFSG.Quasithin.H13
