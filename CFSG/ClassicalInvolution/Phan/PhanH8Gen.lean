module

public import CFSG.ClassicalInvolution.Phan.PhanH6Fix

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

abbrev V7 (F : Type) := Fin 3 ⊕ Fin 3 ⊕ Unit → F

abbrev V5 (F : Type) := Fin 2 ⊕ Fin 2 ⊕ Unit → F

variable {F : Type} [Field F]

@[expose] def mk5 (a₀ a₁ b₀ b₁ c : F) : V5 F :=
  Sum.elim ![a₀, a₁] (Sum.elim ![b₀, b₁] fun _ => c)

omit [Field F] in
@[simp] theorem mk5_a0 (a₀ a₁ b₀ b₁ c : F) : mk5 a₀ a₁ b₀ b₁ c (.inl 0) = a₀ := rfl
omit [Field F] in
@[simp] theorem mk5_a1 (a₀ a₁ b₀ b₁ c : F) : mk5 a₀ a₁ b₀ b₁ c (.inl 1) = a₁ := rfl
omit [Field F] in
@[simp] theorem mk5_b0 (a₀ a₁ b₀ b₁ c : F) : mk5 a₀ a₁ b₀ b₁ c (.inr (.inl 0)) = b₀ := rfl
omit [Field F] in
@[simp] theorem mk5_b1 (a₀ a₁ b₀ b₁ c : F) : mk5 a₀ a₁ b₀ b₁ c (.inr (.inl 1)) = b₁ := rfl
omit [Field F] in
@[simp] theorem mk5_c (a₀ a₁ b₀ b₁ c : F) (u : Unit) : mk5 a₀ a₁ b₀ b₁ c (.inr (.inr u)) = c :=
  rfl

omit [Field F] in
theorem mk5_eta (v : V5 F) :
    v = mk5 (v (.inl 0)) (v (.inl 1)) (v (.inr (.inl 0))) (v (.inr (.inl 1)))
      (v (.inr (.inr ()))) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [mk5]
  · fin_cases i <;> simp [mk5]
  · simp [mk5]

theorem quad5_mk5 (a₀ a₁ b₀ b₁ c : F) :
    quadOdd 2 F (mk5 a₀ a₁ b₀ b₁ c) = a₀ * b₀ + a₁ * b₁ + c ^ 2 := by
  simp [quadOdd_apply, mk5, Fin.sum_univ_two]

theorem polar5_mk5 (a₀ a₁ b₀ b₁ c a₀' a₁' b₀' b₁' c' : F) :
    polar (quadOdd 2 F) (mk5 a₀ a₁ b₀ b₁ c) (mk5 a₀' a₁' b₀' b₁' c') =
      a₀ * b₀' + a₀' * b₀ + (a₁ * b₁' + a₁' * b₁) + 2 * (c * c') := by
  simp [polar_quadOdd, mk5, Fin.sum_univ_two]

theorem kappa_mk5 (a₀ a₁ b₀ b₁ c : F) :
    kappa (mk5 a₀ a₁ b₀ b₁ c) = mk7 c (2 * a₀) a₁ (-c) (-(1 / 2) * b₀) (-b₁) 0 := by
  rw [kappa_eq_mk7]
  simp

theorem vP_eq (a b : F) : vP a b = mk5 (a / 2) b (2 * a) b 0 := rfl

@[expose] def pA : V7 F := mk7 (1 / 2) (1 / 2) 0 (1 / 2) (-(1 / 2)) 0 0

@[expose] def pB : V7 F := mk7 0 0 (-(1 / 2)) 0 0 (1 / 2) (1 / 2)

@[expose] def vOne : V7 F := mk7 1 1 0 (-1) 1 0 0

@[expose] def wOne : V7 F := mk7 0 1 0 0 (-1) 0 0

@[expose] def fTwo : V7 F := mk7 0 0 0 0 0 1 0

theorem fr0_e₁ (h2 : (2 : F) ≠ 0) : (fr0 h2).e₁ = pA := fr0_e₁_eq h2

theorem fr0_e₂ (h2 : (2 : F) ≠ 0) : (fr0 h2).e₂ = pB := fr0_e₂_eq h2

theorem quad_pA : quadOdd 3 F pA = 0 := by
  rw [pA, quad_mk7]; ring

theorem quad_pB : quadOdd 3 F pB = 0 := by
  rw [pB, quad_mk7]; ring

theorem quad_vOne : quadOdd 3 F vOne = 0 := by
  rw [vOne, quad_mk7]; ring

theorem polar_vOne_pA : polar (quadOdd 3 F) vOne pA = 0 := by
  rw [vOne, pA, polar_mk7]; ring

theorem polar_vOne_pB : polar (quadOdd 3 F) vOne pB = 0 := by
  rw [vOne, pB, polar_mk7]; ring

theorem polar_pB_pA : polar (quadOdd 3 F) pB pA = 0 := by
  rw [pB, pA, polar_mk7]; ring

theorem polar_wOne_pA (h2 : (2 : F) ≠ 0) : polar (quadOdd 3 F) wOne pA = -1 := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [wOne, pA, polar_mk7]
  linear_combination (-1 : F) * h

theorem polar_wOne_pB : polar (quadOdd 3 F) wOne pB = 0 := by
  rw [wOne, pB, polar_mk7]; ring

theorem polar_fTwo_pA : polar (quadOdd 3 F) fTwo pA = 0 := by
  rw [fTwo, pA, polar_mk7]; ring

theorem polar_fTwo_pB : polar (quadOdd 3 F) fTwo pB = -(1 / 2) := by
  rw [fTwo, pB, polar_mk7]; ring

theorem polar_vOne_wOne : polar (quadOdd 3 F) vOne wOne = 0 := by
  rw [vOne, wOne, polar_mk7]; ring

theorem polar_vOne_fTwo : polar (quadOdd 3 F) vOne fTwo = 0 := by
  rw [vOne, fTwo, polar_mk7]; ring

theorem kappa_u1 (h2 : (2 : F) ≠ 0) : kappa (mk5 (1 / 2) 0 (-2) 0 1 : V5 F) = vOne := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have e1 : 2 * (1 / 2 : F) = 1 := by linear_combination h
  have e2 : -(1 / 2 : F) * (-2) = 1 := by linear_combination h
  rw [kappa_mk5, e1, e2, vOne]
  simp

theorem quad5_u1 (h2 : (2 : F) ≠ 0) : quadOdd 2 F (mk5 (1 / 2) 0 (-2) 0 1) = 0 := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [quad5_mk5]
  linear_combination (-1 : F) * h

theorem kappa_wOne (h2 : (2 : F) ≠ 0) : kappa (vP 1 0 : V5 F) = wOne := by
  rw [kappa_vP h2, wOne]
  simp

theorem kappa_fTwo : kappa (mk5 0 0 0 (-1) 0 : V5 F) = fTwo := by
  rw [kappa_mk5, fTwo]
  simp

theorem polar_pP_kappa (s z : F) (v : V5 F) :
    polar (quadOdd 3 F) (mk7 s 0 0 s 0 0 z) (kappa v) = 0 := by
  rw [kappa_eq_mk7, polar_mk7]
  ring

theorem quad_pP (s z : F) : quadOdd 3 F (mk7 s 0 0 s 0 0 z) = s * s + z ^ 2 := by
  rw [quad_mk7]
  ring

theorem exists_decomp (h2 : (2 : F) ≠ 0) (x : V7 F) :
    ∃ (v : V5 F) (s z : F), x = kappa v + mk7 s 0 0 s 0 0 z := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  refine ⟨mk5 (x (.inl 1) / 2) (x (.inl 2)) (-2 * x (.inr (.inl 1))) (-x (.inr (.inl 2)))
    ((x (.inl 0) - x (.inr (.inl 0))) / 2), (x (.inl 0) + x (.inr (.inl 0))) / 2,
    x (.inr (.inr ())), ?_⟩
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [kappa_mk5, mk7] <;> field_simp <;> ring
  · fin_cases i <;> simp [kappa_mk5, mk7] <;> field_simp <;> ring
  · simp [kappa_mk5, mk7]

theorem pP_eq (h2 : (2 : F) ≠ 0) (s z : F) :
    mk7 s 0 0 s 0 0 z = (2 * s) • (pA : V7 F) + (2 * z) • (pB : V7 F) - kappa (vP s 0 : V5 F) -
      kappa (vP 0 (-z) : V5 F) := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [kappa_vP h2, kappa_vP h2]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [pA, pB, mk7] <;> field_simp <;> ring
  · fin_cases i <;> simp [pA, pB, mk7] <;> field_simp <;> ring
  · simp [pA, pB, mk7]
    field_simp

variable {h2 : (2 : F) ≠ 0}

theorem polar7_kappa (h2 : (2 : F) ≠ 0) (a b : V5 F) :
    polar (quadOdd 3 F) (kappa a) (kappa b) = -polar (quadOdd 2 F) a b :=
  polar_κ (quad_kappa h2) a b

theorem eichler_kappa_apply (h2 : (2 : F) ≠ 0) {u w : V5 F} (hu : quadOdd 2 F u = 0)
    (huw : polar (quadOdd 2 F) u w = 0) (x : V5 F) :
    eichler (quadOdd 3 F) (kappa u) (kappa w) (kappa x) =
      kappa (eichler (quadOdd 2 F) u (-w) x) := by
  have hu7 : quadOdd 3 F (kappa u) = 0 := by rw [quad_kappa h2, hu, neg_zero]
  have huw7 : polar (quadOdd 3 F) (kappa u) (kappa w) = 0 := by
    rw [polar7_kappa h2, huw, neg_zero]
  have hw' : polar (quadOdd 2 F) u (-w) = 0 := by rw [polar_neg_right, huw, neg_zero]
  rw [eichler_apply hu7 huw7, eichler_apply hu hw']
  simp only [map_add, map_sub, map_smul, map_neg, polar7_kappa h2, quad_kappa h2,
    polar_neg_right, QuadraticMap.map_neg]
  module

theorem eichler_kappa_fix (h2 : (2 : F) ≠ 0) {u w : V5 F} (hu : quadOdd 2 F u = 0)
    (huw : polar (quadOdd 2 F) u w = 0) {p : V7 F}
    (hp : ∀ v, polar (quadOdd 3 F) p (kappa v) = 0) :
    eichler (quadOdd 3 F) (kappa u) (kappa w) p = p := by
  have hu7 : quadOdd 3 F (kappa u) = 0 := by rw [quad_kappa h2, hu, neg_zero]
  have huw7 : polar (quadOdd 3 F) (kappa u) (kappa w) = 0 := by
    rw [polar7_kappa h2, huw, neg_zero]
  rw [eichler_apply hu7 huw7, hp u, hp w]
  simp

theorem exists_eichler_theta (D : ThetaData F h2) {u w : V5 F} (hu : quadOdd 2 F u = 0)
    (huw : polar (quadOdd 2 F) u w = 0) :
    ∃ g : StatedSp 2 F, spinAction (quadOdd 3 F) (D.θ g) =
      eichler (quadOdd 3 F) (kappa u) (kappa w) := by
  have hz : ∀ v : V5 F, (∀ k r, polar (quadOdd 2 F) v ((oddFrame 2 F).vec k r) = 0) →
      ∃ c : F, v = c • (oddFrame 2 F).z := fun v hv => ⟨_, eq_smul_oddZ_of_polar_oddFrame_vec hv⟩
  have hle := (oddFrame 2 F).elementaryGroup_le_map_spinAction (R := D.φ.range) D.leviRoots.1
    D.leviRoots.2 hz
  obtain ⟨r, ⟨g, rfl⟩, hr⟩ := hle (eichler_mem_elementaryGroup (quadOdd 2 F) u (-w))
  refine ⟨g, LinearEquiv.ext fun x => ?_⟩
  obtain ⟨v, s, z, rfl⟩ := exists_decomp h2 x
  rw [map_add, map_add, D.nat, D.fix g _ (polar_pP_kappa s z),
    eichler_kappa_fix h2 hu huw (polar_pP_kappa s z), eichler_kappa_apply h2 hu huw, hr]

theorem exists_theta_apply (D : ThetaData F h2) {u v : V5 F} (hu : quadOdd 2 F u = 0)
    (hv : quadOdd 2 F v = 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    ∃ g : StatedSp 2 F, spinAction (quadOdd 3 F) (D.θ g) (kappa u) = kappa v := by
  have hz : ∀ v : V5 F, (∀ k r, polar (quadOdd 2 F) v ((oddFrame 2 F).vec k r) = 0) →
      ∃ c : F, v = c • (oddFrame 2 F).z := fun v hv => ⟨_, eq_smul_oddZ_of_polar_oddFrame_vec hv⟩
  obtain ⟨r, ⟨g, rfl⟩, hr⟩ := (oddFrame 2 F).exists_mem_spinAction_eq (R := D.φ.range)
    D.leviRoots.1 D.leviRoots.2 hz (le_refl 2) hu hv hu0 hv0
  exact ⟨g, by rw [D.nat, hr]⟩

structure GenHyp (D : ThetaData F h2) (M : Subgroup (V7 F ≃ₗ[F] V7 F)) : Prop where
  orth : M ≤ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 F)
  theta : ∀ g, spinAction (quadOdd 3 F) (D.θ g) ∈ M
  root : ∀ c : F, eichler (quadOdd 3 F) pB (c • pA) ∈ M

variable {D : ThetaData F h2} {M : Subgroup (V7 F ≃ₗ[F] V7 F)}

theorem eichler_pB_vOne (c : F) : eichler (quadOdd 3 F) pB (c • pA) vOne = vOne := by
  have hw : polar (quadOdd 3 F) pB (c • pA) = 0 := by
    rw [polar_smul_right_eq, polar_pB_pA, mul_zero]
  rw [eichler_apply quad_pB hw, polar_vOne_pB, polar_smul_right_eq, polar_vOne_pA]
  simp

theorem eichler_pB_wOne (h2 : (2 : F) ≠ 0) (c : F) :
    eichler (quadOdd 3 F) pB (c • pA) wOne = wOne + c • (pB : V7 F) := by
  have hw : polar (quadOdd 3 F) pB (c • pA) = 0 := by
    rw [polar_smul_right_eq, polar_pB_pA, mul_zero]
  rw [eichler_apply quad_pB hw, polar_wOne_pB, polar_smul_right_eq, polar_wOne_pA h2]
  simp

theorem eichler_pB_fTwo (c : F) :
    eichler (quadOdd 3 F) pB (c • pA) fTwo = fTwo + (-(c / 2)) • (pA : V7 F) := by
  have hw : polar (quadOdd 3 F) pB (c • pA) = 0 := by
    rw [polar_smul_right_eq, polar_pB_pA, mul_zero]
  have hq : quadOdd 3 F (c • (pA : V7 F)) = 0 := by
    rw [QuadraticMap.map_smul, quad_pA]
    simp
  rw [eichler_apply quad_pB hw, polar_fTwo_pB, polar_smul_right_eq, polar_fTwo_pA, hq]
  module

theorem mk5_u1_ne_zero (h2' : (2 : F) ≠ 0) : (mk5 (1 / 2) 0 (-2) 0 1 : V5 F) ≠ 0 := by
  intro h
  have := congrFun h (.inl 0)
  simp at this
  exact h2' this

theorem mk7_zero : mk7 (0 : F) 0 0 0 0 0 0 = 0 := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

theorem eq_zero_of_sq_add_sq (hn1 : ¬ IsSquare (-1 : F)) {s z : F} (h : s * s + z ^ 2 = 0) :
    s = 0 ∧ z = 0 := by
  by_cases hz : z = 0
  · subst hz
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    apply hn1
    refine ⟨s / z, ?_⟩
    field_simp
    linear_combination (-1 : F) * h

theorem exists_singular_pairing (h2' : (2 : F) ≠ 0) {v : V5 F} (hv : v ≠ 0) :
    ∃ b : V5 F, quadOdd 2 F b = 0 ∧ polar (quadOdd 2 F) v b ≠ 0 := by
  by_contra hcon0
  have hcon : ∀ b : V5 F, quadOdd 2 F b = 0 → polar (quadOdd 2 F) v b = 0 := fun b hb => by
    by_contra h
    exact hcon0 ⟨b, hb, h⟩
  obtain ⟨a₀, a₁, b₀, b₁, c, rfl⟩ : ∃ a₀ a₁ b₀ b₁ c : F, v = mk5 a₀ a₁ b₀ b₁ c :=
    ⟨_, _, _, _, _, mk5_eta v⟩
  have e1 := hcon (mk5 1 0 0 0 0) (by rw [quad5_mk5]; ring)
  have e2 := hcon (mk5 0 0 1 0 0) (by rw [quad5_mk5]; ring)
  have e3 := hcon (mk5 0 1 0 0 0) (by rw [quad5_mk5]; ring)
  have e4 := hcon (mk5 0 0 0 1 0) (by rw [quad5_mk5]; ring)
  have e5 := hcon (mk5 1 0 (-1) 0 1) (by rw [quad5_mk5]; ring)
  rw [polar5_mk5] at e1 e2 e3 e4 e5
  have hb₀ : b₀ = 0 := by linear_combination e1
  have ha₀ : a₀ = 0 := by linear_combination e2
  have hb₁ : b₁ = 0 := by linear_combination e3
  have ha₁ : a₁ = 0 := by linear_combination e4
  have hc : c = 0 := by
    have : 2 * c = 0 := by linear_combination e5 + ha₀ - hb₀
    exact (mul_eq_zero.mp this).resolve_left h2'
  apply hv
  subst hb₀ ha₀ hb₁ ha₁ hc
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk5]
  · fin_cases i <;> simp [mk5]
  · simp [mk5]

namespace GenHyp

variable (hM : GenHyp D M)
include hM

theorem theta_eichler {u w : V5 F} (hu : quadOdd 2 F u = 0) (huw : polar (quadOdd 2 F) u w = 0) :
    eichler (quadOdd 3 F) (kappa u) (kappa w) ∈ M := by
  obtain ⟨g, hg⟩ := exists_eichler_theta D hu huw
  rw [← hg]
  exact hM.theta g

theorem root_conj (c : F) {w : V7 F} (h : eichler (quadOdd 3 F) vOne w ∈ M) :
    eichler (quadOdd 3 F) vOne (eichler (quadOdd 3 F) pB (c • pA) w) ∈ M := by
  have hg := hM.root c
  have hgO := hM.orth hg
  have := eichler_conj hgO vOne w
  rw [eichler_pB_vOne] at this
  rw [← this]
  exact M.mul_mem (M.mul_mem hg h) (M.inv_mem hg)

theorem eichler_vOne_wOne (h2' : (2 : F) ≠ 0) : eichler (quadOdd 3 F) vOne wOne ∈ M := by
  have h := hM.theta_eichler (u := mk5 (1 / 2) 0 (-2) 0 1) (w := vP 1 0) (quad5_u1 h2')
    (by rw [vP_eq, polar5_mk5]; ring)
  rwa [kappa_u1 h2', kappa_wOne h2'] at h

theorem eichler_vOne_fTwo (h2' : (2 : F) ≠ 0) : eichler (quadOdd 3 F) vOne fTwo ∈ M := by
  have h := hM.theta_eichler (u := mk5 (1 / 2) 0 (-2) 0 1) (w := mk5 0 0 0 (-1) 0) (quad5_u1 h2')
    (by rw [polar5_mk5]; ring)
  rwa [kappa_u1 h2', kappa_fTwo] at h

theorem eichler_vOne_pB (h2' : (2 : F) ≠ 0) (c : F) :
    eichler (quadOdd 3 F) vOne (c • pB) ∈ M := by
  have h1 := hM.eichler_vOne_wOne h2'
  have h2'' := hM.root_conj c h1
  rw [eichler_pB_wOne h2'] at h2''
  have hpol2 : polar (quadOdd 3 F) vOne (c • (pB : V7 F)) = 0 := by
    rw [polar_smul_right_eq, polar_vOne_pB, mul_zero]
  rw [← eichler_mul polar_vOne_wOne hpol2] at h2''
  have := M.mul_mem (M.inv_mem h1) h2''
  rwa [inv_mul_cancel_left] at this

theorem eichler_vOne_pA (h2' : (2 : F) ≠ 0) (c : F) :
    eichler (quadOdd 3 F) vOne (c • pA) ∈ M := by
  have h1 := hM.eichler_vOne_fTwo h2'
  have h2'' := hM.root_conj (-2 * c) h1
  rw [eichler_pB_fTwo] at h2''
  have hc : (-((-2 * c) / 2)) = c := by field_simp
  rw [hc] at h2''
  have hpol2 : polar (quadOdd 3 F) vOne (c • (pA : V7 F)) = 0 := by
    rw [polar_smul_right_eq, polar_vOne_pA, mul_zero]
  rw [← eichler_mul polar_vOne_fTwo hpol2] at h2''
  have := M.mul_mem (M.inv_mem h1) h2''
  rwa [inv_mul_cancel_left] at this

theorem eichler_vOne_mem (h2' : (2 : F) ≠ 0) {w : V7 F} (hw : polar (quadOdd 3 F) vOne w = 0) :
    eichler (quadOdd 3 F) vOne w ∈ M := by
  obtain ⟨v, s, z, rfl⟩ := exists_decomp h2' w
  have hsplit : kappa v + mk7 s 0 0 s 0 0 z = kappa (v - vP s 0 - vP 0 (-z)) +
      (2 * s) • (pA : V7 F) + (2 * z) • (pB : V7 F) := by
    rw [pP_eq h2' s z, map_sub, map_sub]
    abel
  rw [hsplit] at hw ⊢
  have hpA : polar (quadOdd 3 F) vOne ((2 * s) • (pA : V7 F)) = 0 := by
    rw [polar_smul_right_eq, polar_vOne_pA, mul_zero]
  have hpB : polar (quadOdd 3 F) vOne ((2 * z) • (pB : V7 F)) = 0 := by
    rw [polar_smul_right_eq, polar_vOne_pB, mul_zero]
  have hk : polar (quadOdd 3 F) vOne (kappa (v - vP s 0 - vP 0 (-z))) = 0 := by
    rw [polar_add_right, polar_add_right, hpA, hpB, add_zero, add_zero] at hw
    exact hw
  have hu1 : polar (quadOdd 3 F) (kappa (mk5 (1 / 2) 0 (-2) 0 1 : V5 F))
      (kappa (v - vP s 0 - vP 0 (-z))) = 0 := by
    rw [kappa_u1 h2']
    exact hk
  have hu1' : polar (quadOdd 2 F) (mk5 (1 / 2) 0 (-2) 0 1) (v - vP s 0 - vP 0 (-z)) = 0 := by
    rw [polar7_kappa h2'] at hu1
    exact neg_eq_zero.mp hu1
  have h1 := hM.theta_eichler (quad5_u1 h2') hu1'
  rw [kappa_u1 h2'] at h1
  have hkA : polar (quadOdd 3 F) vOne
      (kappa (v - vP s 0 - vP 0 (-z)) + (2 * s) • (pA : V7 F)) = 0 := by
    rw [polar_add_right, hk, hpA, add_zero]
  rw [← eichler_mul hkA hpB, ← eichler_mul hk hpA]
  exact M.mul_mem (M.mul_mem h1 (hM.eichler_vOne_pA h2' _)) (hM.eichler_vOne_pB h2' _)

theorem eichler_kappa_mem (h2' : (2 : F) ≠ 0) {u : V5 F} (hu : quadOdd 2 F u = 0) (hu0 : u ≠ 0)
    {w : V7 F} (hw : polar (quadOdd 3 F) (kappa u) w = 0) :
    eichler (quadOdd 3 F) (kappa u) w ∈ M := by
  obtain ⟨g, hg⟩ := exists_theta_apply D (quad5_u1 h2') hu (mk5_u1_ne_zero h2') hu0
  set t := spinAction (quadOdd 3 F) (D.θ g) with ht
  have htM : t ∈ M := hM.theta g
  have htO := hM.orth htM
  have hpol := polar_map_of_mem htO (kappa (mk5 (1 / 2) 0 (-2) 0 1 : V5 F)) (t⁻¹ w)
  rw [hg, LinearEquiv.apply_inv_apply', kappa_u1 h2'] at hpol
  have h1 : eichler (quadOdd 3 F) vOne (t⁻¹ w) ∈ M :=
    hM.eichler_vOne_mem h2' (by rw [← hpol]; exact hw)
  have hconj := eichler_conj htO vOne (t⁻¹ w)
  have e1 : t vOne = kappa u := by rw [← kappa_u1 h2']; exact hg
  rw [e1, LinearEquiv.apply_inv_apply'] at hconj
  rw [← hconj]
  exact M.mul_mem (M.mul_mem htM h1) (M.inv_mem htM)

theorem exists_mem_apply_eq_vOne (h2' : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F)) {x : V7 F}
    (hx : quadOdd 3 F x = 0) (hx0 : x ≠ 0) : ∃ t ∈ M, t x = vOne := by
  obtain ⟨v, s, z, rfl⟩ := exists_decomp h2' x
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_add, quad_pP] at hx
    obtain ⟨rfl, rfl⟩ := eq_zero_of_sq_add_sq hn1 hx
    apply hx0
    rw [map_zero, zero_add]
    exact mk7_zero
  obtain ⟨b, hb, hpb⟩ := exists_singular_pairing h2' hv0
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hpb
    simp
  have hu7 : quadOdd 3 F (kappa b) = 0 := by rw [quad_kappa h2', hb, neg_zero]
  have hBeq : polar (quadOdd 3 F) (kappa v + mk7 s 0 0 s 0 0 z) (kappa b) =
      -polar (quadOdd 2 F) v b := by
    rw [polar_add_left, polar_pP_kappa, polar7_kappa h2', add_zero]
  have hB0 : polar (quadOdd 3 F) (kappa v + mk7 s 0 0 s 0 0 z) (kappa b) ≠ 0 := by
    rw [hBeq]
    exact neg_ne_zero.mpr hpb
  set B := polar (quadOdd 3 F) (kappa v + mk7 s 0 0 s 0 0 z) (kappa b) with hB
  set w : V7 F := (-B⁻¹) • mk7 s 0 0 s 0 0 z with hw
  have hwp : polar (quadOdd 3 F) (kappa b) w = 0 := by
    rw [hw, polar_smul_right_eq, polar_comm, polar_pP_kappa, mul_zero]
  have ht : eichler (quadOdd 3 F) (kappa b) w ∈ M := hM.eichler_kappa_mem h2' hb hb0 hwp
  have hBw : B • w = -(mk7 s 0 0 s 0 0 z : V7 F) := by
    rw [hw, smul_smul, mul_neg, mul_inv_cancel₀ hB0, neg_smul, one_smul]
  obtain ⟨γ, hγ⟩ : ∃ γ : F, γ = polar (quadOdd 3 F) (kappa v + mk7 s 0 0 s 0 0 z) w +
      quadOdd 3 F w * B := ⟨_, rfl⟩
  have hkb : kappa (v - γ • b) = kappa v - γ • kappa b := by
    rw [map_sub, map_smul kappa γ b]
  have htx : eichler (quadOdd 3 F) (kappa b) w (kappa v + mk7 s 0 0 s 0 0 z) =
      kappa (v - γ • b) := by
    rw [eichler_apply hu7 hwp, ← hB, hBw, ← hγ, hkb]
    module
  have hQ7 : quadOdd 3 F (kappa (v - γ • b)) = 0 := by
    rw [← htx, map_of_mem (hM.orth ht)]
    exact hx
  have hQ5 : quadOdd 2 F (v - γ • b) = 0 := by
    rw [quad_kappa h2'] at hQ7
    exact neg_eq_zero.mp hQ7
  have hu'0 : v - γ • b ≠ 0 := by
    intro h0
    rw [h0, map_zero] at htx
    exact hx0 ((LinearEquiv.map_eq_zero_iff _).mp htx)
  obtain ⟨g, hg⟩ := exists_theta_apply D hQ5 (quad5_u1 h2') hu'0 (mk5_u1_ne_zero h2')
  refine ⟨spinAction (quadOdd 3 F) (D.θ g) * eichler (quadOdd 3 F) (kappa b) w,
    M.mul_mem (hM.theta g) ht, ?_⟩
  rw [LinearEquiv.mul_apply, htx, hg, kappa_u1 h2']

theorem elementaryGroup_le (h2' : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F)) :
    elementaryGroup (quadOdd 3 F) ≤ M := by
  refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
  by_cases hu0 : u = 0
  · subst hu0
    rw [eichler_zero_left]
    exact M.one_mem
  · obtain ⟨t, htM, htu⟩ := hM.exists_mem_apply_eq_vOne h2' hn1 hu hu0
    have htO := hM.orth htM
    have hpol : polar (quadOdd 3 F) vOne (t w) = 0 := by
      rw [← htu, polar_map_of_mem htO]
      exact huw
    have h1 := hM.eichler_vOne_mem h2' hpol
    have hconj := eichler_conj (inv_mem htO) vOne (t w)
    have e1 : t⁻¹ vOne = u := by rw [← htu, LinearEquiv.inv_apply_apply']
    have e2 : t⁻¹ (t w) = w := LinearEquiv.inv_apply_apply' t w
    rw [e1, e2, inv_inv] at hconj
    rw [← hconj]
    exact M.mul_mem (M.mul_mem (M.inv_mem htM) h1) htM

end GenHyp

theorem genHyp_sup (D : ThetaData F h2) {R₀ : Subgroup (spinGroup (quadOdd 3 F))}
    (hR₀ : R₀.map (spinAction (quadOdd 3 F)) = (fr0 h2).La.range) :
    GenHyp D ((R₀ ⊔ D.θ.range).map (spinAction (quadOdd 3 F))) where
  orth := by
    rintro _ ⟨g, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ g)
  theta g := ⟨D.θ g, Subgroup.mem_sup_right ⟨g, rfl⟩, rfl⟩
  root c := by
    have h1 : (fr0 h2).La (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 2) ≠ 1 by decide) c) ∈ (fr0 h2).La.range := ⟨_, rfl⟩
    rw [← hR₀] at h1
    obtain ⟨r, hr, hrg⟩ := h1
    refine ⟨r, Subgroup.mem_sup_left hr, ?_⟩
    rw [hrg, Frame.La_transvection_zero_one, fr0_e₁ h2, fr0_e₂ h2]

theorem sup_theta_eq_top (D : ThetaData F h2) (hn1 : ¬ IsSquare (-1 : F))
    {R₀ : Subgroup (spinGroup (quadOdd 3 F))}
    (hR₀ : R₀.map (spinAction (quadOdd 3 F)) = (fr0 h2).La.range) : R₀ ⊔ D.θ.range = ⊤ := by
  have := isPerfect_spinGroup_quadOdd h2 (le_refl 3)
  refine eq_top_of_range_le_map (spinAction (quadOdd 3 F)) (ker_spinAction_le_center _) ?_
  exact (range_spinAction_quadOdd h2 (le_refl 3)).le.trans
    ((genHyp_sup D hR₀).elementaryGroup_le h2 hn1)

end CFSG.ClassicalInvolution.PhanB3.H
