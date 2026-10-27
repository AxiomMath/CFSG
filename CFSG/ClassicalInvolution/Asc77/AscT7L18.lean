module

public import CFSG.ClassicalInvolution.Asc77.AscT7L11
public import CFSG.ClassicalInvolution.Asc77.AscT7L16
public import CFSG.ClassicalInvolution.Asc77.AscT7L17

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

namespace T7L

section Matrix

variable {F : Type} [Field F]

theorem exists_conj_x0_u0 [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R')
    {x x' : SL(4, F)} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F))
    {a b : SL(4, F)} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ c : SL(4, F), x = c * x0 F * c⁻¹ ∧ a * b = c * u0 F * c⁻¹ := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hRg' : R = (R0 F).map (MulAut.conj g).toMonoidHom := hRg
  have hR'g' : R' = (R0' F).map (MulAut.conj g).toMonoidHom := hR'g
  have hx'neg := twin_neg h2 hxg hR'g' hx'R' hx'2 hx2 hc
  have hzc : ∀ y : SL(4, F), y * zneg F = zneg F * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  rw [hRg'] at ha
  rw [hR'g'] at hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at haa hbb ⊢
  have hxg' : x = g * x0 F * g⁻¹ := hxg
  have ha₀2 : a₀ * a₀ = x0 F := by
    have : g * (a₀ * a₀) * g⁻¹ = g * x0 F * g⁻¹ := by rw [← hxg', ← haa]; group
    exact mul_left_cancel (mul_right_cancel this)
  have hb₀2 : b₀ * b₀ = zneg F * x0 F := by
    have : g * (b₀ * b₀) * g⁻¹ = g * (zneg F * x0 F) * g⁻¹ := by
      calc g * (b₀ * b₀) * g⁻¹ = g * b₀ * g⁻¹ * (g * b₀ * g⁻¹) := by group
        _ = x' := hbb
        _ = zneg F * x := hx'neg
        _ = zneg F * (g * x0 F * g⁻¹) := by rw [hxg']
        _ = g * (zneg F * x0 F) * g⁻¹ := by
          calc zneg F * (g * x0 F * g⁻¹) = (zneg F * g) * x0 F * g⁻¹ := by group
            _ = (g * zneg F) * x0 F * g⁻¹ := by rw [← hzc g]
            _ = g * (zneg F * x0 F) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hcomm : b₀ * a₀ = a₀ * b₀ := (R0_comm_R0' ha₀ hb₀).symm
  have hw : a₀ * b₀ ∈ R0 F ⊔ R0' F :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₀) (Subgroup.mem_sup_right hb₀)
  have hzx : x0 F * zneg F = zneg F * x0 F := hzc _
  have hw2 : (a₀ * b₀) * (a₀ * b₀) = zneg F := by
    calc (a₀ * b₀) * (a₀ * b₀) = a₀ * (b₀ * a₀) * b₀ := by group
      _ = (a₀ * a₀) * (b₀ * b₀) := by rw [hcomm]; group
      _ = x0 F * (zneg F * x0 F) := by rw [ha₀2, hb₀2]
      _ = (x0 F * zneg F) * x0 F := by group
      _ = zneg F * (x0 F * x0 F) := by rw [hzx]; group
      _ = zneg F := by rw [x0_mul_self, mul_one]
  have hz1 := zneg_ne_one h2
  have hzz := zneg_mul_self (F := F)
  rcases classify_w h2 hw (hw2 ▸ zneg_mem_center) with h | h | h | h | ⟨h, hh, hwh⟩
  · exfalso
    rw [h, mul_one] at hw2
    exact hz1 hw2.symm
  · exfalso
    rw [h, x0_mul_self] at hw2
    exact hz1 hw2.symm
  · exfalso
    have : (zneg F * x0 F) * (zneg F * x0 F) = 1 := by
      calc (zneg F * x0 F) * (zneg F * x0 F)
          = zneg F * (x0 F * zneg F) * x0 F := by group
        _ = zneg F * (zneg F * x0 F) * x0 F := by rw [hzx]
        _ = (zneg F * zneg F) * (x0 F * x0 F) := by group
        _ = 1 := by rw [hzz, x0_mul_self, mul_one]
    rw [h, this] at hw2
    exact hz1 hw2.symm
  · exfalso
    rw [h, hzz] at hw2
    exact hz1 hw2.symm
  · have hxh : h * x0 F = x0 F * h := by
      have := sup_le R0_le_centralizer R0'_le_centralizer hh
      exact (Subgroup.mem_centralizer_iff.mp this (x0 F) rfl).symm
    refine ⟨g * h, ?_, ?_⟩
    · calc x = g * x0 F * g⁻¹ := hxg'
        _ = g * (h * x0 F * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 F * (g * h)⁻¹ := by group
    · calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (h * u0 F * h⁻¹) * g⁻¹ := by rw [hwh]
        _ = g * h * u0 F * (g * h)⁻¹ := by group

end Matrix

section Row

variable (p : ℕ) [Fact p.Prime]

theorem e4GenSL : E4GenSL p := by
  intro e hadm hp2 hq h3
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRl := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField p e) (by norm_num) hR
  have hRl' := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField p e) (by norm_num) hR'
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, GaloisField p e) := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, ← hcomm x hx x' hx']
    exact hxx'
  obtain ⟨c, hxc, habc⟩ := exists_conj_x0_u0 h2 hRl hRl' hne hx hx2 hx1 hx' hx'2 hx'1 hc ha haa
    hb hbb
  exact e4_goal_of_top_le _ _ _
    (top_le_sup_of_conj c hxc habc (top_le_centralizer_x0_sup_u0 h4))

end Row

end T7L

end CFSG.ClassicalInvolution.Asc77
