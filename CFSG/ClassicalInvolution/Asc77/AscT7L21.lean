module

public import CFSG.ClassicalInvolution.Asc77.AscT7L10
public import CFSG.ClassicalInvolution.Asc77.AscT7L17
public import CFSG.ClassicalInvolution.Asc77.AscT7L20
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

namespace T7L

section Matrix

variable {F : Type} [Field F]

theorem zneg_ne_one_sp (h2 : (2 : F) ≠ 0) : zneg F ≠ 1 := by
  intro h
  have h1 := congrArg (mat 2 F) h
  rw [mat_zneg, map_one] at h1
  have := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
  simp at this
  apply h2
  linear_combination -this

theorem R0_le_cent_sp : R0 F ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  show longBlock F 2 0 A * longBlock F 2 0 (-1) = longBlock F 2 0 (-1) * longBlock F 2 0 A
  rw [← map_mul, ← map_mul, neg_one_comm]

theorem R0'_le_cent_sp : R0' F ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (longBlock_comm (-1) B).symm

theorem eq_conj_longInv (h2 : (2 : F) ≠ 0) {g x : StatedSp 2 F} {k : Fin 2}
    (hx : x ∈ (longBlock F 2 k).range.map (MulAut.conj g).toMonoidHom) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : x = g * longInv F 2 k * g⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx2 hx1 ⊢
  have hyy : y * y = 1 := by
    have : g * (y * y) * g⁻¹ = g * 1 * g⁻¹ := by
      rw [mul_one, mul_inv_cancel]
      calc g * (y * y) * g⁻¹ = g * y * g⁻¹ * (g * y * g⁻¹) := by group
        _ = 1 := hx2
    exact mul_left_cancel (mul_right_cancel this)
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h]; group)
  rw [(isLongRootSp2_standard (K := F) (n := 2) k).eq_of_orderOf_eq_two h2 hy
    (orderOf_eq_prime (by rwa [pow_two]) hy1)]

theorem exists_conj_x0_u0_sp [Finite F] (h2 : (2 : F) ≠ 0) {g : StatedSp 2 F}
    {R R' : Subgroup (StatedSp 2 F)} (hRg : R = (R0 F).map (MulAut.conj g).toMonoidHom)
    (hR'g : R' = (R0' F).map (MulAut.conj g).toMonoidHom) {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    {a b : StatedSp 2 F} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ c : StatedSp 2 F, x = c * x0 F * c⁻¹ ∧ a * b = c * u0 F * c⁻¹ := by
  have hxg' : x = g * x0 F * g⁻¹ := eq_conj_longInv h2 (k := 0) (hRg ▸ hxR) hx2 hx1
  have hx'g : x' = g * (zneg F * x0 F) * g⁻¹ := by
    rw [zneg_mul_x0_eq_longInv]
    exact eq_conj_longInv h2 (k := 1) (hR'g ▸ hx'R') hx'2 hx'1
  have hzc : ∀ y : StatedSp 2 F, y * zneg F = zneg F * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  rw [hRg] at ha
  rw [hR'g] at hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at haa hbb ⊢
  have ha₀2 : a₀ * a₀ = x0 F := by
    have : g * (a₀ * a₀) * g⁻¹ = g * x0 F * g⁻¹ := by rw [← hxg', ← haa]; group
    exact mul_left_cancel (mul_right_cancel this)
  have hb₀2 : b₀ * b₀ = zneg F * x0 F := by
    have : g * (b₀ * b₀) * g⁻¹ = g * (zneg F * x0 F) * g⁻¹ := by
      calc g * (b₀ * b₀) * g⁻¹ = g * b₀ * g⁻¹ * (g * b₀ * g⁻¹) := by group
        _ = x' := hbb
        _ = g * (zneg F * x0 F) * g⁻¹ := hx'g
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
  have hz1 := zneg_ne_one_sp h2
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
      have := sup_le R0_le_cent_sp R0'_le_cent_sp hh
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    refine ⟨g * h, ?_, ?_⟩
    · calc x = g * x0 F * g⁻¹ := hxg'
        _ = g * (h * x0 F * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 F * (g * h)⁻¹ := by group
    · calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (h * u0 F * h⁻¹) * g⁻¹ := by rw [hwh]
        _ = g * h * u0 F * (g * h)⁻¹ := by group

theorem top_le_x0_sup_u0 [Finite F] (h2 : (2 : F) ≠ 0) :
    (⊤ : Subgroup (StatedSp 2 F)) ≤ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({u0 F} : Set (StatedSp 2 F)) := by
  obtain ⟨g', hg't, hg'x⟩ := exists_conj_t0 h2
  have hx : x0 F = g'⁻¹ * x0 F * g'⁻¹⁻¹ := by
    rw [inv_inv]
    calc x0 F = g'⁻¹ * (g' * x0 F * g'⁻¹) * g' := by group
      _ = g'⁻¹ * x0 F * g' := by rw [hg'x]
  have hu : u0 F = g'⁻¹ * t0 F * g'⁻¹⁻¹ := by
    rw [inv_inv]
    calc u0 F = g'⁻¹ * (g' * u0 F * g'⁻¹) * g' := by group
      _ = g'⁻¹ * t0 F * g' := by rw [hg't]
  exact top_le_sup_of_conj g'⁻¹ hx hu (top_le_x0_sup_t0 h2)

theorem top_le_sup_sp [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    {a b : StatedSp 2 F} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x')
    (hab : a * b = b * a) :
    (⊤ : Subgroup (StatedSp 2 F)) ≤ Subgroup.centralizer ({x} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({a * b} : Set (StatedSp 2 F)) := by
  obtain ⟨g, k, hRg, hR'g⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hR
    hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  fin_cases k
  · obtain ⟨c, hxc, habc⟩ := exists_conj_x0_u0_sp h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 ha haa
      hb hbb
    exact top_le_sup_of_conj c hxc habc (top_le_x0_sup_u0 h2)
  · obtain ⟨c, hxc, habc⟩ := exists_conj_x0_u0_sp h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hb hbb
      ha haa
    have h1 := top_le_sup_of_conj c hxc habc (top_le_x0_sup_u0 h2)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hxz : x = x' * (x' * x⁻¹) := by rw [hxinv, ← mul_assoc, hx'2, one_mul]
    have hle : Subgroup.centralizer ({x'} : Set (StatedSp 2 F)) ≤
        Subgroup.centralizer ({x} : Set (StatedSp 2 F)) := by
      rw [hxz]
      exact centralizer_le_of_mul_central hc
    rw [hab] at *
    exact h1.trans (sup_le_sup_right hle _)

end Matrix

section Row

variable (p : ℕ) [Fact p.Prime]

theorem e4GenSp : E4GenSp p := by
  intro e hadm hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).1 hR
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').1 hR'
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField p e)) := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, ← hcomm x hx x' hx']
    exact hxx'
  exact e4_goal_of_top_le _ _ _ (top_le_sup_sp h2 hRl hRl' hne hx hx2 hx1 hx' hx'2 hx'1 hc ha haa
    hb hbb (hcomm a ha b hb))

end Row

end T7L

end CFSG.ClassicalInvolution.Asc77
