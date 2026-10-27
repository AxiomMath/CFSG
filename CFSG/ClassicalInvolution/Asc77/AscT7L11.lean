module

public import CFSG.ClassicalInvolution.Asc77.AscT7L10
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Model

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

theorem zneg_mul_self : zneg F * zneg F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_zneg, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem zneg_ne_one (h2 : (2 : F) ≠ 0) : zneg F ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) h) 0) 0
  simp [coe_zneg] at this
  apply h2
  linear_combination -this

noncomputable def gSL (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) : SL(4, F) :=
  ⟨Gm i * Matrix.diagonal ![(4 : F)⁻¹, 1, 1, 1], by
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    rw [Matrix.det_mul, det_Gm hi, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [h4]⟩

theorem gSL_mul (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    gSL h2 hi * (scal4 i (four_pow_of_sq hi) * x0 F) = u0 F * gSL h2 hi := by
  apply Subtype.ext
  have hG := Gm_mul_zx hi
  have hD : Matrix.diagonal ![(4 : F)⁻¹, 1, 1, 1] *
      ((scal4 i (four_pow_of_sq hi) * x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((scal4 i (four_pow_of_sq hi) * x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
        Matrix.diagonal ![(4 : F)⁻¹, 1, 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_scal4, coe_x0]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  show (Gm i * Matrix.diagonal ![(4 : F)⁻¹, 1, 1, 1]) *
      ((scal4 i (four_pow_of_sq hi) * x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (Gm i * Matrix.diagonal ![(4 : F)⁻¹, 1, 1, 1])
  rw [mul_assoc, hD, ← mul_assoc, hG, mul_assoc]

theorem exists_longRoot_comm_ab [Finite F] (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    {R R' : Subgroup SL(4, F)} (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R')
    {x x' : SL(4, F)} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F))
    {a b : SL(4, F)} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x') :
    ∃ R'' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num),
      ∀ r ∈ R'', (a * b) * r = r * (a * b) := by
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
      calc (zneg F * x0 F) * (zneg F * x0 F) = zneg F * (x0 F * zneg F) * x0 F := by group
        _ = zneg F * (zneg F * x0 F) * x0 F := by rw [hzx]
        _ = (zneg F * zneg F) * (x0 F * x0 F) := by group
        _ = 1 := by rw [hzz, x0_mul_self, mul_one]
    rw [h, this] at hw2
    exact hz1 hw2.symm
  · exfalso
    rw [h, hzz] at hw2
    exact hz1 hw2.symm
  · have hsc : scal4 i (four_pow_of_sq hi) ∈ Subgroup.center SL(4, F) :=
      scal4_mem_center i (four_pow_of_sq hi)
    set s : SL(4, F) := scal4 i (four_pow_of_sq hi) * x0 F with hs
    have hu0 : u0 F = gSL h2 hi * s * (gSL h2 hi)⁻¹ := eq_mul_inv_of_mul_eq (gSL_mul h2 hi).symm
    set c : SL(4, F) := g * h * gSL h2 hi with hc'
    refine ⟨(R0 F).map (MulAut.conj c).toMonoidHom,
      (mem_longRootSet_iff (show 2 ≤ 4 by norm_num)).mpr ⟨c, rfl⟩, ?_⟩
    have hab : g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = c * s * c⁻¹ := by
      calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (h * u0 F * h⁻¹) * g⁻¹ := by rw [hwh]
        _ = c * s * c⁻¹ := by rw [hu0, hc']; group
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hrs : r * s = s * r := by
      have h1 : r * x0 F = x0 F * r :=
        Subgroup.mem_centralizer_singleton_iff.mp (R0_le_centralizer hr)
      have h2' : r * scal4 i (four_pow_of_sq hi) = scal4 i (four_pow_of_sq hi) * r :=
        Subgroup.mem_center_iff.mp hsc r
      calc r * s = (r * scal4 i (four_pow_of_sq hi)) * x0 F := by rw [hs]; group
        _ = scal4 i (four_pow_of_sq hi) * (r * x0 F) := by rw [h2']; group
        _ = scal4 i (four_pow_of_sq hi) * (x0 F * r) := by rw [h1]
        _ = s * r := by rw [hs]; group
    rw [hab]
    calc c * s * c⁻¹ * (c * r * c⁻¹) = c * (s * r) * c⁻¹ := by group
      _ = c * (r * s) * c⁻¹ := by rw [hrs]
      _ = c * r * c⁻¹ * (c * s * c⁻¹) := by group

end Matrix

section Row

variable (p : ℕ) [Fact p.Prime]

theorem twinCentralSL : TwinCentralSL p := by
  intro e hadm hp2 hq h4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  obtain ⟨i, hi⟩ : ∃ i : GaloisField p e, i * i = -1 := by
    have : Fintype (GaloisField p e) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField p e) = p ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p e he
    have : IsSquare (-1 : GaloisField p e) := by
      rw [FiniteField.isSquare_neg_one_iff, hc]
      omega
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi.symm⟩
  intro R hR R' hR' hne hcomm x hx hx2 hx1 x' hx' hx'2 hx'1 hxx' a ha haa b hb hbb
  have hRl := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField p e) (by norm_num) hR
  have hRl' := fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField p e) (by norm_num) hR'
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, GaloisField p e) := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, ← hcomm x hx x' hx']
    exact hxx'
  obtain ⟨R'', hR'', hcomm''⟩ := exists_longRoot_comm_ab h2 hi hRl hRl' hne hx hx2 hx1 hx' hx'2
    hx'1 hc ha haa hb hbb
  exact ⟨R'', longRootSet_subset_fundamentalSubgroups_psl (m := 3) (by norm_num) hR'', hcomm''⟩

end Row

end T7L

end CFSG.ClassicalInvolution.Asc77
