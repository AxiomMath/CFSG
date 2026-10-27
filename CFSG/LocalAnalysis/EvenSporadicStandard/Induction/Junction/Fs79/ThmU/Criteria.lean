module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Swap

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem universalF_of_good_mem_center [Finite G] (hLB : LayerBalanceAt G)
    (hglaub : GlaubermanSimplePerfect) {B : Subgroup G} (hB : MaximalF B) {x : G}
    (hx : GoodInv B x) (hxB : x ∈ B) (hxz : ∀ b ∈ B, x * b = b * x) : UniversalF B := by
  intro y hy
  have hxy : x * y = y * x := Subgroup.mem_centralizer_singleton_iff.1 (hy.2.1 hxB)
  obtain ⟨M, hS, -, -⟩ := exists_swapConfig hLB hglaub hB hx hy hxy
  refine hS.ne (cj_eq_of_commute ?_)
  intro n hn
  obtain ⟨m, hm, hxm⟩ := (hS.mem_iff x).1 hxB
  have hz : ∀ n ∈ M, diag x m * diag x n = diag x n * diag x m := by
    intro n hn
    have h := hxz (diag x n) ((hS.mem_iff (diag x n)).2 ⟨n, hn, rfl⟩)
    rw [← hxm]
    exact h
  have hcent := (centralizes_of_central_diag hS.x_mul_self hS.diagComm
    (IsCompIn.perfect hS.isCompIn) hm hz).1
  rw [hxm]
  exact hcent n hn

theorem goodInv_of_fourGroup [Finite G] (hLB : LayerBalanceAt G)
    (hglaub : GlaubermanSimplePerfect) {B : Subgroup G} (hB : MaximalF B) {u₁ u₂ : G}
    (h₁ : GoodInv B u₁) (h₂ : GoodInv B u₂) (h₃ : GoodInv B (u₁ * u₂)) (h12 : u₁ * u₂ = u₂ * u₁)
    {b : G} (hb : orderOf b = 2) (hbB : B ≤ centralizer ({b} : Set G))
    (hb₁ : u₁ * b = b * u₁) (hb₂ : u₂ * b = b * u₂) : GoodInv B b := by
  refine goodInv_of_not_badInv hb hbB ?_
  intro hbad
  obtain ⟨M, hS, -, -⟩ := exists_swapConfig hLB hglaub hB h₁ hbad hb₁
  have hsupp : cj u₂ M = M ∨ cj u₂ M = cj u₁ M :=
    hS.cj_mem_support hb₂ fun c hc =>
      (Subgroup.mem_centralizer_singleton_iff.1 (h₂.le_centralizer hc)).symm
  rcases hsupp with hcase | hcase
  · obtain ⟨M₂, hS₂, -, -⟩ := exists_swapConfig hLB hglaub hB h₂ hbad hb₂
    exact cj_ne_of_not_centralizes (h := hS₂) hS.isCompIn hS.not_centralizes_left hcase
  · have hxy3 : (u₁ * u₂) * b = b * (u₁ * u₂) := by
      calc (u₁ * u₂) * b = u₁ * (u₂ * b) := by group
        _ = u₁ * (b * u₂) := by rw [hb₂]
        _ = (u₁ * b) * u₂ := by group
        _ = (b * u₁) * u₂ := by rw [hb₁]
        _ = b * (u₁ * u₂) := by group
    obtain ⟨M₃, hS₃, -, -⟩ := exists_swapConfig hLB hglaub hB h₃ hbad hxy3
    have hcjcj : cj (u₁ * u₂) M = M := by
      have h1sq : u₁ * u₁ = 1 := mul_self_eq_one_of_orderOf h₁.1
      calc cj (u₁ * u₂) M = cj u₁ (cj u₂ M) := (map_conj_map_conj M u₂ u₁).symm
        _ = cj u₁ (cj u₁ M) := by rw [hcase]
        _ = M := cj_cj_of_mul_self h1sq M
    exact cj_ne_of_not_centralizes (h := hS₃) hS.isCompIn hS.not_centralizes_left hcjcj

end CFSG.EvenSporadicStandard.Induction.ThmU
