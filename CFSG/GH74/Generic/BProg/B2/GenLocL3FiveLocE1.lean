module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3FiveMat
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
public import CFSG.GH74.Generic.BProg.B2.GenLocL3FiveR3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial Matrix GenLocL3Pair GenLocL3Good GenLocL3Nine
  GenLocL3NineR3
open scoped MatrixGroups

namespace GenLocL3Five

@[expose] def InV (y : MulAut (LinearFlag.projectiveSL 3 K5)) : Prop :=
  y ≠ 1 ∧ ∃ (m : Fin 3) (u : Fin 3 → K5ˣ), y = LinearFlag.conjAut 3 K5 (diag3 u) ∧
    (u (crd m 0) : K5) = u (crd m 1) ∧ (u m : K5) = -(u (crd m 0) : K5)

@[expose] def InW (y : MulAut (LinearFlag.projectiveSL 3 K5)) : Prop :=
  ∃ u : Fin 3 → K5ˣ, y = LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5 ∧
    ∀ m : Fin 3, IsSquare ((u (crd m 0) : K5) * u (crd m 1))

theorem card_K5 : Nat.card K5 = 5 := by simp

theorem pow_eight_of_matrix {g : SL(3, K5)} (h : (g : Matrix (Fin 3) (Fin 3) K5) ^ 8 = 1) :
    LinearFlag.proj 3 K5 g ^ 8 = 1 := by
  rw [← map_pow]
  have : (g ^ 8 : SL(3, K5)) = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, h]; rfl)
  rw [this, map_one]

theorem fixed_VW {y e : MulAut (LinearFlag.projectiveSL 3 K5)} (hy : InV y) (he : InW e)
    {x : LinearFlag.projectiveSL 3 K5} (hxy : y x = x) (hxe : e x = x) : x ^ 8 = 1 := by
  obtain ⟨-, m, u, rfl, h1, h2⟩ := hy
  obtain ⟨u', rfl, hsq⟩ := he
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K5 x
  have hc := (conjAut_fixed_iff (diag3 u) g).1 hxy
  have hd := (conjAut_dual_fixed_iff (diag3 u') g).1 hxe
  rw [coe_diag3] at hc hd
  have hsq' : (u' (crd m 0) : K5) * u' (crd m 1) = 1 ∨ (u' (crd m 0) : K5) * u' (crd m 1) = 4 :=
    sq_cases _ (mul_ne_zero (u' (crd m 0)).ne_zero (u' (crd m 1)).ne_zero) (hsq m)
  exact pow_eight_of_matrix (block_pow8 m (u (crd m 0) : K5) (u (crd m 0)).ne_zero (fun i => (u i : K5))
    (fun i => (u' i : K5)) rfl h1.symm h2 (fun i => (u' i).ne_zero) hsq' _ hc hd)

theorem sq_of_InV_data (m : Fin 3) (u : Fin 3 → K5ˣ) (h1 : (u (crd m 0) : K5) = u (crd m 1))
    (h2 : (u m : K5) = -(u (crd m 0) : K5)) : ∀ i i', (u i : K5) * u i = u i' * u i' := by
  have key : ∀ i, (u i : K5) * u i = (u (crd m 0) : K5) * u (crd m 0) := by
    intro i
    have hcov : ∀ m i : Fin 3, i = crd m 0 ∨ i = crd m 1 ∨ i = m := by decide
    rcases hcov m i with h | h | h
    · rw [h]
    · rw [h, ← h1]
    · rw [h, h2]; ring
  intro i i'
  rw [key i, key i']

theorem InV_eq_of_same_block {y1 y2 : MulAut (LinearFlag.projectiveSL 3 K5)} (h1 : InV y1) (h2 : InV y2)
    {m m' : Fin 3} {u u' : Fin 3 → K5ˣ} (hy1 : y1 = LinearFlag.conjAut 3 K5 (diag3 u))
    (hy2 : y2 = LinearFlag.conjAut 3 K5 (diag3 u')) (hj : (u (crd m 0) : K5) = u (crd m 1))
    (hm : (u m : K5) = -(u (crd m 0) : K5)) (hj' : (u' (crd m' 0) : K5) = u' (crd m' 1))
    (hm' : (u' m' : K5) = -(u' (crd m' 0) : K5)) (hmm : m = m') : y1 = y2 := by
  subst hmm
  rw [hy1, hy2]
  refine eq_of_trivial_block m (sq_of_InV_data m u hj hm) (sq_of_InV_data m u' hj' hm')
    (Units.ext hj) (Units.ext hj') ?_ ?_
  · rw [← hy1]; exact h1.1
  · rw [← hy2]; exact h2.1

theorem fixed_VV {y1 y2 : MulAut (LinearFlag.projectiveSL 3 K5)} (h1 : InV y1) (h2 : InV y2)
    (hne : y1 ≠ y2) {x : LinearFlag.projectiveSL 3 K5} (hx1 : y1 x = x) (hx2 : y2 x = x) :
    x ^ 8 = 1 := by
  obtain ⟨hy1, m, u, hu, hj, hm⟩ := h1
  obtain ⟨hy2, m', u', hu', hj', hm'⟩ := h2
  have hmm : m ≠ m' := fun h =>
    hne (InV_eq_of_same_block ⟨hy1, m, u, hu, hj, hm⟩ ⟨hy2, m', u', hu', hj', hm'⟩ hu hu' hj hm hj' hm' h)
  subst hu hu'
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K5 x
  have hc := (conjAut_fixed_iff (diag3 u) g).1 hx1
  have hc' := (conjAut_fixed_iff (diag3 u') g).1 hx2
  rw [coe_diag3] at hc hc'
  have hdet : (g : Matrix (Fin 3) (Fin 3) K5).det ≠ 0 := by
    rw [g.2]; exact one_ne_zero
  exact pow_eight_of_matrix (diag_pow8 m m' hmm (u (crd m 0) : K5) (u' (crd m' 0) : K5)
    (u (crd m 0)).ne_zero (u' (crd m' 0)).ne_zero (fun i => (u i : K5)) (fun i => (u' i : K5)) rfl hj.symm hm
    rfl hj'.symm hm' _ hdet hc hc')

theorem outer_mul_outer (u v : Fin 3 → K5ˣ) :
    (LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5) *
        (LinearFlag.conjAut 3 K5 (diag3 v) * LinearFlag.dualAut 3 K5) =
      LinearFlag.conjAut 3 K5 (diag3 (fun i => u i * (v i)⁻¹)) := by
  have hδδ : LinearFlag.dualAut 3 K5 * LinearFlag.dualAut 3 K5 = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K5) (n := 3)).2.2.2.1
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K5) (diag3 v)
  have hit : GeneralLinearGroup.inverseTranspose (diag3 v) = diag3 (fun i => (v i)⁻¹) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose, coe_diag3_inv, Matrix.diagonal_transpose, coe_diag3]
  have hmul : diag3 u * diag3 (fun i => (v i)⁻¹) = diag3 (fun i => u i * (v i)⁻¹) := by
    apply Units.ext
    rw [Units.val_mul, coe_diag3, coe_diag3, coe_diag3, Matrix.diagonal_mul_diagonal]
    rfl
  calc (LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5) *
        (LinearFlag.conjAut 3 K5 (diag3 v) * LinearFlag.dualAut 3 K5)
      = LinearFlag.conjAut 3 K5 (diag3 u) * (LinearFlag.dualAut 3 K5 *
          LinearFlag.conjAut 3 K5 (diag3 v)) * LinearFlag.dualAut 3 K5 := by simp only [mul_assoc]
    _ = LinearFlag.conjAut 3 K5 (diag3 u) * (LinearFlag.conjAut 3 K5 (diag3 (fun i => (v i)⁻¹)) *
          LinearFlag.dualAut 3 K5) * LinearFlag.dualAut 3 K5 := by rw [s2, hit]
    _ = LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.conjAut 3 K5 (diag3 (fun i => (v i)⁻¹)) *
          (LinearFlag.dualAut 3 K5 * LinearFlag.dualAut 3 K5) := by simp only [mul_assoc]
    _ = _ := by rw [hδδ, mul_one, ← map_mul, hmul]

theorem isSquare_mul_of_sq_eq (tj tk vj vk : K5) (h : tj * tj = tk * tk) (hv : IsSquare (vj * vk)) :
    IsSquare ((tj * vj) * (tk * vk)) := by
  have h1 : (tk - tj) * (tk + tj) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · have : tk = tj := by linear_combination h2
    subst this
    have h3 : (tk * vj) * (tk * vk) = (tk * tk) * (vj * vk) := by ring
    rw [h3]
    exact (IsSquare.mul_self tk).mul hv
  · have : tk = -tj := by linear_combination h2
    subst this
    have h5 : (5 : K5) = 0 := by decide
    have h3 : (tj * vj) * (-tj * vk) = ((2 * tj) * (2 * tj)) * (vj * vk) := by
      linear_combination (-(tj * tj * vj * vk)) * h5
    rw [h3]
    exact (IsSquare.mul_self (2 * tj)).mul hv

theorem D_cases (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5)
    (y : D) :
    (∃ u : Fin 3 → K5ˣ, (y : MulAut (LinearFlag.projectiveSL 3 K5)) = LinearFlag.conjAut 3 K5 (diag3 u)) ∨
      (∃ u : Fin 3 → K5ˣ, (y : MulAut (LinearFlag.projectiveSL 3 K5)) =
        LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5) := by
  obtain ⟨u, σ, ε, hε, h⟩ := exists_data (hfs y.2)
  rw [sigma_eq_one card_K5 σ, map_one, mul_one] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · left; exact ⟨u, by rw [h, pow_zero, mul_one]⟩
  · right; exact ⟨u, by rw [h, pow_one]⟩

theorem inV_of_diag (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5)))
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (y : D) (u : Fin 3 → K5ˣ)
    (hy : (y : MulAut (LinearFlag.projectiveSL 3 K5)) = LinearFlag.conjAut 3 K5 (diag3 u)) (hy1 : y ≠ 1) :
    InV (y : MulAut (LinearFlag.projectiveSL 3 K5)) := by
  have h1 : LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.conjAut 3 K5 (diag3 u) = 1 := by
    rw [← hy]
    exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD y)
  have hsq := sq_equal_of_conjAut_sq u h1
  obtain ⟨m, hm⟩ := exists_block_eq hsq
  have hne : (y : MulAut (LinearFlag.projectiveSL 3 K5)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine ⟨hne, m, u, hy, congrArg Units.val hm, ?_⟩
  have h2 : ((u m : K5) - u (crd m 0)) * ((u m : K5) + u (crd m 0)) = 0 := by
    linear_combination hsq m (crd m 0)
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    apply hne
    have hcov : ∀ m i : Fin 3, i = crd m 0 ∨ i = crd m 1 ∨ i = m := by decide
    have hconst : ∀ i, u i = u (crd m 0) := by
      intro i
      rcases hcov m i with h | h | h
      · rw [h]
      · rw [h]; exact hm.symm
      · rw [h]; exact Units.ext (by linear_combination h3)
    have hu : u = fun i => u (crd m 0) * (fun _ => (1 : K5ˣ)) i := by
      funext i; simp [hconst i]
    have h1' : diag3 (fun _ : Fin 3 => (1 : K5ˣ)) = (1 : GL (Fin 3) K5) := by
      apply Units.ext
      rw [coe_diag3]
      simp
    rw [hy, hu, conjAut_diag3_smul, h1', map_one]
  · linear_combination h3

theorem inW_of_outer (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5)))
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hS : ShapeE5 D) (y : D) (u : Fin 3 → K5ˣ)
    (hy : (y : MulAut (LinearFlag.projectiveSL 3 K5)) =
      LinearFlag.conjAut 3 K5 (diag3 u) * LinearFlag.dualAut 3 K5) :
    InW (y : MulAut (LinearFlag.projectiveSL 3 K5)) := by
  obtain ⟨r, v, hr, hv⟩ := hS
  refine ⟨u, hy, fun m => ?_⟩
  have hyr : ((y * r : D) : MulAut (LinearFlag.projectiveSL 3 K5)) =
      LinearFlag.conjAut 3 K5 (diag3 (fun i => u i * (v i)⁻¹)) := by
    rw [Subgroup.coe_mul, hy, hr, outer_mul_outer]
  have h1 : LinearFlag.conjAut 3 K5 (diag3 (fun i => u i * (v i)⁻¹)) *
      LinearFlag.conjAut 3 K5 (diag3 (fun i => u i * (v i)⁻¹)) = 1 := by
    rw [← hyr]
    exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD (y * r))
  have hsq := sq_equal_of_conjAut_sq _ h1
  have e : ∀ i, (u i : K5) = ((u i * (v i)⁻¹ : K5ˣ) : K5) * (v i : K5) := by
    intro i
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hj := isSquare_mul_of_sq_eq ((u (crd m 0) * (v (crd m 0))⁻¹ : K5ˣ) : K5)
    ((u (crd m 1) * (v (crd m 1))⁻¹ : K5ˣ) : K5) (v (crd m 0) : K5) (v (crd m 1) : K5)
    (hsq (crd m 0) (crd m 1)) (hv m)
  rw [e (crd m 0), e (crd m 1)]
  exact hj

theorem pair_pow8 (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hS : ShapeE5 D) (a b : D) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    {x : LinearFlag.projectiveSL 3 K5} (hxa : (a : MulAut (LinearFlag.projectiveSL 3 K5)) x = x)
    (hxb : (b : MulAut (LinearFlag.projectiveSL 3 K5)) x = x) : x ^ 8 = 1 := by
  rcases D_cases D hfs a with ⟨ua, hua⟩ | ⟨ua, hua⟩ <;> rcases D_cases D hfs b with ⟨ub, hub⟩ | ⟨ub, hub⟩
  · exact fixed_VV (inV_of_diag D hD a ua hua ha) (inV_of_diag D hD b ub hub hb)
      (fun h => hab (Subtype.ext h)) hxa hxb
  · exact fixed_VW (inV_of_diag D hD a ua hua ha) (inW_of_outer D hD hS b ub hub) hxa hxb
  · exact fixed_VW (inV_of_diag D hD b ub hub hb) (inW_of_outer D hD hS a ua hua) hxb hxa
  · have hyab : ((a * b : D) : MulAut (LinearFlag.projectiveSL 3 K5)) =
        LinearFlag.conjAut 3 K5 (diag3 (fun i => ua i * (ub i)⁻¹)) := by
      rw [Subgroup.coe_mul, hua, hub, outer_mul_outer]
    have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD b
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      calc a = a * (b * b) := by rw [hbb, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [h, one_mul]
    have hx_ab : ((a * b : D) : MulAut (LinearFlag.projectiveSL 3 K5)) x = x := by
      rw [Subgroup.coe_mul, MulAut.mul_apply, hxb, hxa]
    exact fixed_VW (inV_of_diag D hD (a * b) _ hyab hab1) (inW_of_outer D hD hS a ua hua) hx_ab hxa

theorem locE1_of_shapeE5 (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K5))) (hfs : D ≤ frameStab 3 K5)
    (hA : IsRank23 ↥D) (h8 : Nat.card ↥D = 8) (hS : ShapeE5 D) : LocE1 D.subtype := by
  intro E hE
  refine noOddNormal_of_isPGroup ?_
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hrk : pRank 2 ↥D = 3 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hA.1
    have h2 : 2 ^ pRank 2 ↥D = 2 ^ 3 := by rw [← h1, h8]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hEA := GenLocBasic.isEA_subgroup hA.1 E
  have hEcard := GenLocBasic.card_eq_two_pow_pRank_type hEA
  have h4 : 2 < Nat.card ↥E := by
    rw [hEcard]
    have h2 : 2 ≤ pRank 2 ↥E := by omega
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨t, ht, s, hs, ht1, hs1, hts⟩ := GenLocBasic.exists_two_ne_one h4
  have hpow : ∀ x ∈ fixedIn (LinearFlag.projectiveSL 3 K5) (E.map D.subtype), x ^ 8 = 1 := by
    intro x hx
    rw [mem_fixedIn] at hx
    exact pair_pow8 D hfs hA.1 hS t s ht1 hs1 hts (hx _ ⟨t, ht, rfl⟩) (hx _ ⟨s, hs, rfl⟩)
  intro x
  exact ⟨3, Subtype.ext (by simpa using hpow x x.2)⟩

end GenLocL3Five

end CFSG.GH74.Generic.BProg.B2
