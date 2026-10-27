module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Local

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem mem_ptPerp_of_le_sup_lines (hP : IsGeneralizedPolygon Γ 4) (hι : IsProjGQ c ι A)
    {y z L₁ L₂ : V} (hy : c y = 0) (hL : L₁ ≠ L₂) (hy₁ : Γ.Adj y L₁)
    (hy₂ : Γ.Adj y L₂) (hz : c z = 0) (hzle : ι z ≤ ι L₁ ⊔ ι L₂) :
    z ∈ ptPerp Γ c {y} := by
  classical
  have hL₁ : c L₁ = 1 := color_eq_one_of_adj_of_color_eq_zero hy hy₁
  have hL₂ : c L₂ = 1 := color_eq_one_of_adj_of_color_eq_zero hy hy₂
  have hyL₁ : ι y ≤ ι L₁ := (hι.adj_iff y L₁ hy hL₁).1 hy₁
  have hyL₂ : ι y ≤ ι L₂ := (hι.adj_iff y L₂ hy hL₂).1 hy₂
  have hL₁2 : finrank K (ι L₁) = 2 := hι.finrank_line L₁ hL₁
  have hL₂2 : finrank K (ι L₂) = 2 := hι.finrank_line L₂ hL₂
  have hy1 : finrank K (ι y) = 1 := hι.finrank_point y hy
  haveI : FiniteDimensional K (ι L₁) :=
    Module.finite_of_finrank_pos (by rw [hL₁2]; norm_num)
  haveI : FiniteDimensional K (ι L₂) :=
    Module.finite_of_finrank_pos (by rw [hL₂2]; norm_num)
  let π : Submodule K W := ι L₁ ⊔ ι L₂
  haveI : FiniteDimensional K π := by
    dsimp [π]
    exact Submodule.finiteDimensional_sup (ι L₁) (ι L₂)
  haveI : FiniteDimensional K ↥(ι L₁ ⊓ ι L₂) :=
    Submodule.finiteDimensional_of_le (inf_le_left : ι L₁ ⊓ ι L₂ ≤ ι L₁)
  have hinf_ge : 1 ≤ finrank K ↥(ι L₁ ⊓ ι L₂) := by
    have hle : ι y ≤ ι L₁ ⊓ ι L₂ := le_inf hyL₁ hyL₂
    have hmono : finrank K ↥(ι y) ≤ finrank K ↥(ι L₁ ⊓ ι L₂) := Submodule.finrank_mono hle
    omega
  have hdimπ : finrank K π ≤ 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ι L₁) (ι L₂)
    rw [hL₁2, hL₂2] at h
    dsimp [π]
    omega
  have hzy_le : Γ.dist z y ≤ 2 := by
    by_contra hle
    have hzy_gt : 2 < Γ.dist z y := not_le.mp hle
    have hzy_ne : z ≠ y := by
      intro h
      rw [h, SimpleGraph.dist_self] at hzy_gt
      omega
    have hzy4 : Γ.dist z y = 4 := by
      rcases dist_eq_two_or_four_of_color_zero hP hz hy hzy_ne with h | h
      · omega
      · exact h
    have hzL₁ : ¬ Γ.Adj z L₁ := by
      intro h
      have h2 : Γ.dist z y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP h hy₁.symm hzy_ne
      omega
    obtain ⟨w, ⟨hL₁w, hzw2⟩, -⟩ := existsUnique_proj_of_not_adj hP hz hL₁ hzL₁
    have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hL₁ hL₁w
    have hwy : w ≠ y := by
      intro h
      rw [h] at hzw2
      omega
    have hzw_ne : z ≠ w := by
      intro h
      rw [h, SimpleGraph.dist_self] at hzw2
      omega
    let M : V := commonNeighbor hP hzw2
    have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzw2
    have hwM : Γ.Adj w M := commonNeighbor_adj_right hP hzw2
    have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz hzM
    have hM2 : finrank K (ι M) = 2 := hι.finrank_line M hM1
    have hlineM : ι M = ι z ⊔ ι w :=
      line_eq_sup_of_two_adjacent_points hι hz hw0 hzw_ne hzM hwM
    have hwπ : ι w ≤ π := by
      have hwL₁ : ι w ≤ ι L₁ := (hι.adj_iff w L₁ hw0 hL₁).1 hL₁w.symm
      exact hwL₁.trans le_sup_left
    have hMπ : ι M ≤ π := by
      rw [hlineM]
      exact sup_le hzle hwπ
    have hlt : finrank K π < finrank K (ι M) + finrank K (ι L₂) := by
      rw [hM2, hL₂2]
      omega
    obtain ⟨P, hP1, hPle⟩ :=
      exists_finrank_eq_one_le_inf hMπ (le_sup_right : ι L₂ ≤ π) hlt
    have hne : ι M ⊓ ι L₂ ≠ ⊥ := by
      intro hbot
      rw [hbot] at hPle
      have hPbot : P = ⊥ := le_antisymm hPle bot_le
      rw [hPbot, finrank_bot] at hP1
      omega
    obtain ⟨x, hxM, hxL₂⟩ := exists_adj_le_of_line_inf_ne_bot hι hM1 hne
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hM1 hxM
    have hxL₂' : Γ.Adj x L₂ := (hι.adj_iff x L₂ hx0 hL₂).2 hxL₂
    have hxy : x ≠ y := by
      intro h
      have hzx : z ≠ x := by
        intro hzx
        exact hzy_ne (hzx.trans h)
      have h2 : Γ.dist z x = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hzM hxM hzx
      rw [← h] at hzy4
      omega
    have hxw : x ≠ w := by
      intro h
      have hwL₂ : Γ.Adj w L₂ := h ▸ hxL₂'
      exact hL (eq_of_two_common_points hP hwy hL₁w hy₁.symm hwL₂.symm hy₂.symm)
    have hxw2 : Γ.dist x w = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxM.symm hwM.symm hxw
    have hxy2 : Γ.dist x y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxL₂' hy₂.symm hxy
    have hwy2 : Γ.dist w y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL₁w.symm hy₁.symm hwy
    obtain ⟨u, hu, -⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP hxw2 hxy2 hwy2
    have huL₁ : u = L₁ :=
      eq_of_two_common_points hP hwy hu.2.1.symm hu.2.2.symm hL₁w hy₁.symm
    have huL₂ : u = L₂ :=
      eq_of_two_common_points hP hxy hu.1.symm hu.2.2.symm hxL₂'.symm hy₂.symm
    exact hL (huL₁.symm.trans huL₂)
  refine ⟨hz, ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact hzy_le

end CFSG.Geometry.GeneralizedQuadrangles

end
