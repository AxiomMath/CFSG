module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {K : Type} [Field K]

theorem quadOdd_eTwo : quadOdd 3 K (oddVec 3 K 2 true) = 0 := quadOdd_oddVec 3 K 2 true

theorem quadOdd_fTwo : quadOdd 3 K (oddVec 3 K 2 false) = 0 := quadOdd_oddVec 3 K 2 false

theorem polar_eTwo_fTwo : polar (quadOdd 3 K) (oddVec 3 K 2 true) (oddVec 3 K 2 false) = 1 := by
  rw [polar_quadOdd_oddVec, ite_eq_left ⟨rfl, rfl⟩]

theorem polar_fTwo_eTwo : polar (quadOdd 3 K) (oddVec 3 K 2 false) (oddVec 3 K 2 true) = 1 := by
  rw [polar_comm, polar_eTwo_fTwo]

theorem polar_eTwo_eTwo : polar (quadOdd 3 K) (oddVec 3 K 2 true) (oddVec 3 K 2 true) = 0 := by
  rw [polar_self, quadOdd_eTwo, smul_zero]

theorem polar_fTwo_fTwo : polar (quadOdd 3 K) (oddVec 3 K 2 false) (oddVec 3 K 2 false) = 0 := by
  rw [polar_self, quadOdd_fTwo, smul_zero]

theorem polar_eTwo_z : polar (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) = 0 :=
  polar_quadOdd_oddVec_oddZ 3 K 2 true

theorem polar_fTwo_z : polar (quadOdd 3 K) (oddVec 3 K 2 false) (oddZ 3 K) = 0 :=
  polar_quadOdd_oddVec_oddZ 3 K 2 false

theorem polar_z_eTwo : polar (quadOdd 3 K) (oddZ 3 K) (oddVec 3 K 2 true) = 0 := by
  rw [polar_comm, polar_eTwo_z]

theorem polar_z_z : polar (quadOdd 3 K) (oddZ 3 K) (oddZ 3 K) = 2 := by
  rw [polar_self, quadOdd_oddZ]
  norm_num

theorem eichlerThree_apply (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) x =
      x + polar (quadOdd 3 K) x (oddVec 3 K 2 true) • oddZ 3 K -
        (polar (quadOdd 3 K) x (oddZ 3 K) + polar (quadOdd 3 K) x (oddVec 3 K 2 true)) •
          oddVec 3 K 2 true := by
  rw [eichler_apply quadOdd_eTwo polar_eTwo_z, quadOdd_oddZ, one_mul]

theorem eichlerThree_sq_sub (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K)
        (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) x) -
        (2 : K) • eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) x + x =
      (-2 * polar (quadOdd 3 K) x (oddVec 3 K 2 true)) • oddVec 3 K 2 true := by
  rw [eichlerThree_apply (eichler _ _ _ x), eichlerThree_apply x]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_z_eTwo, polar_eTwo_eTwo,
    polar_z_z, polar_eTwo_z, smul_eq_mul, mul_zero, add_zero, sub_zero]
  module

variable {h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}

theorem apply_eTwo_eq_smul (h2 : (2 : K) ≠ 0)
    (hc : h * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * h) :
    h (oddVec 3 K 2 true) =
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) • oddVec 3 K 2 true := by
  have hE : ∀ v, h (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) v) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) (h v) := fun v =>
    LinearEquiv.congr_fun hc v
  have h1 := eichlerThree_sq_sub (K := K) (oddVec 3 K 2 false)
  have h3 := eichlerThree_sq_sub (K := K) (h (oddVec 3 K 2 false))
  rw [polar_fTwo_eTwo, mul_one] at h1
  have h4 := congrArg h h1
  simp only [map_add, map_sub, map_smul, hE] at h4
  rw [h3] at h4
  have h5 : (-2 : K) • h (oddVec 3 K 2 true) = (-2 : K) •
      (polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) • oddVec 3 K 2 true) := by
    rw [smul_smul, ← h4]
  exact smul_right_injective _ (neg_ne_zero.mpr h2) h5

theorem polar_apply_of_map (hO : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v)
    (u v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    polar (quadOdd 3 K) (h u) (h v) = polar (quadOdd 3 K) u v := by
  simp only [polar, ← map_add, hO]

theorem lam_mul_self (h2 : (2 : K) ≠ 0) (hO : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v)
    (hc : h * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * h) :
    polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) *
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) = 1 := by
  have h1 := polar_apply_of_map hO (oddVec 3 K 2 true) (oddVec 3 K 2 false)
  rw [apply_eTwo_eq_smul h2 hc, polar_smul_left, polar_eTwo_fTwo,
    polar_comm (quadOdd 3 K) (oddVec 3 K 2 true) (h (oddVec 3 K 2 false)), smul_eq_mul] at h1
  exact h1

theorem commute_La_of_maps {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (F : Frame Q) {g : V ≃ₗ[K] V} (hperp : ∀ x, F.coords x = 0 → F.coords (g x) = 0)
    (hspan : ∀ X, g (F.incl X) = F.incl (F.coords (g (F.incl X)))) :
    g * F.La (-1) = F.La (-1) * g := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_neg_one_apply,
    Frame.La_neg_one_apply, map_sub, map_smul]
  have hr : F.coords (x - F.incl (F.coords x)) = 0 := by rw [map_sub, F.coords_incl, sub_self]
  have hx : g x = g (F.incl (F.coords x)) + g (x - F.incl (F.coords x)) := by
    rw [← map_add, add_sub_cancel]
  have hc : F.coords (g x) = F.coords (g (F.incl (F.coords x))) := by
    rw [hx, map_add, hperp _ hr, add_zero]
  rw [hc, ← hspan]

theorem eq_zero_of_polar_eq_zero {r : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (h2 : (2 : K) ≠ 0)
    (hv : ∀ m s, polar (quadOdd 3 K) r (oddVec 3 K m s) = 0)
    (hz : polar (quadOdd 3 K) r (oddZ 3 K) = 0) : r = 0 := by
  funext σ
  rcases σ with m | m | ⟨⟩
  · have := hv m false
    rwa [oddVec_false, polar_quadOdd_single_inr_inl] at this
  · have := hv m true
    rwa [oddVec_true, polar_quadOdd_single_inl] at this
  · rw [oddZ, polar_quadOdd_single_inr_inr] at hz
    exact (mul_eq_zero.mp hz).resolve_left h2

theorem polar_eq_zero_of_coords_eq_zero {x : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hx : (frame01 K).coords x = 0) (m : Fin 3) (hm : m ≠ 2) (s : Bool) :
    polar (quadOdd 3 K) x (oddVec 3 K m s) = 0 := by
  rw [coords_frame01] at hx
  have e00 := congrFun (congrFun hx 0) 0
  have e01 := congrFun (congrFun hx 0) 1
  have e10 := congrFun (congrFun hx 1) 0
  have e11 := congrFun (congrFun hx 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, neg_eq_zero] at e00 e01 e10 e11
  fin_cases m
  · cases s
    · exact e00
    · exact e11
  · cases s
    · exact e01
    · exact e10
  · exact absurd rfl hm

theorem coords_eq_zero_of_perp {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : ∀ m : Fin 3, m ≠ 2 → ∀ r, polar (quadOdd 3 K) v (oddVec 3 K m r) = 0) :
    (frame01 K).coords v = 0 := by
  rw [coords_frame01, hv 0 (by decide) false, hv 1 (by decide) false, hv 1 (by decide) true,
    hv 0 (by decide) true, neg_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem coords_eTwo : (frame01 K).coords (oddVec 3 K 2 true) = 0 :=
  coords_eq_zero_of_perp fun m hm r => by
    rw [polar_quadOdd_oddVec, ite_eq_right fun h => hm h.1.symm]

theorem coords_fTwo : (frame01 K).coords (oddVec 3 K 2 false) = 0 :=
  coords_eq_zero_of_perp fun m hm r => by
    rw [polar_quadOdd_oddVec, ite_eq_right fun h => hm h.1.symm]

theorem coords_z : (frame01 K).coords (oddZ 3 K) = 0 :=
  coords_eq_zero_of_perp fun m _ r => by
    rw [polar_comm, polar_quadOdd_oddVec_oddZ]

theorem polar_incl_of_coords_eq_zero (X : Matrix (Fin 2) (Fin 2) K)
    {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hv : (frame01 K).coords v = 0) :
    polar (quadOdd 3 K) ((frame01 K).incl X) v = 0 := by
  rw [polar_comm, Frame.polar_incl_right, hv]
  simp

noncomputable abbrev lamThree (h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :
    K :=
  polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true)

noncomputable abbrev wThree (h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :
    Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  h (oddVec 3 K 2 false) -
    polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false) • oddVec 3 K 2 true -
    lamThree h • oddVec 3 K 2 false

noncomputable abbrev yThree (h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :
    Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  lamThree h • wThree h

theorem polar_wThree_eTwo : polar (quadOdd 3 K) (wThree h) (oddVec 3 K 2 true) = 0 := by
  simp only [wThree, polar_sub_left, polar_smul_left, polar_eTwo_eTwo, polar_fTwo_eTwo,
    smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]

theorem polar_wThree_fTwo : polar (quadOdd 3 K) (wThree h) (oddVec 3 K 2 false) = 0 := by
  simp only [wThree, polar_sub_left, polar_smul_left, polar_eTwo_fTwo, polar_fTwo_fTwo,
    smul_eq_mul, mul_zero, mul_one, sub_self]

theorem polar_eTwo_yThree : polar (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) = 0 := by
  rw [yThree, polar_smul_right, polar_comm, polar_wThree_eTwo, smul_zero]

theorem polar_fTwo_yThree : polar (quadOdd 3 K) (oddVec 3 K 2 false) (yThree h) = 0 := by
  rw [yThree, polar_smul_right, polar_comm, polar_wThree_fTwo, smul_zero]

theorem quadOdd_add_eTwo_fTwo (w : Fin 3 ⊕ Fin 3 ⊕ Unit → K) (a l : K)
    (hwe : polar (quadOdd 3 K) w (oddVec 3 K 2 true) = 0)
    (hwf : polar (quadOdd 3 K) w (oddVec 3 K 2 false) = 0) :
    quadOdd 3 K (w + a • oddVec 3 K 2 true + l • oddVec 3 K 2 false) = quadOdd 3 K w + a * l := by
  simp only [QuadraticMap.map_add, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, quadOdd_eTwo, quadOdd_fTwo, hwe, hwf, polar_eTwo_fTwo, smul_eq_mul,
    mul_zero, zero_add, add_zero, mul_one]
  ring

theorem eichler_yThree_apply (hl : lamThree h * lamThree h = 1)
    (hQ : quadOdd 3 K (h (oddVec 3 K 2 false)) = 0) :
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) (lamThree h • oddVec 3 K 2 false) =
      h (oddVec 3 K 2 false) := by
  have hw : h (oddVec 3 K 2 false) = wThree h +
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false) • oddVec 3 K 2 true +
      lamThree h • oddVec 3 K 2 false := by
    simp only [wThree]
    abel
  have hQw : quadOdd 3 K (wThree h) +
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false) * lamThree h = 0 := by
    have h1 := quadOdd_add_eTwo_fTwo (wThree h)
      (polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false)) (lamThree h)
      polar_wThree_eTwo polar_wThree_fTwo
    rw [← hw, hQ] at h1
    exact h1.symm
  have ha : polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false) =
      -lamThree h * quadOdd 3 K (wThree h) := by
    linear_combination lamThree h * hQw -
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 false) * hl
  rw [eichler_apply quadOdd_eTwo polar_eTwo_yThree, polar_smul_left, polar_smul_left,
    polar_fTwo_eTwo, polar_fTwo_yThree]
  conv_rhs => rw [hw, ha]
  simp only [yThree, QuadraticMap.map_smul, smul_eq_mul, mul_one, mul_zero, zero_add, smul_smul]
  have e1 : (lamThree h * lamThree h) • wThree h = wThree h := by rw [hl, one_smul]
  have e2 : lamThree h * lamThree h * quadOdd 3 K (wThree h) * lamThree h =
      quadOdd 3 K (wThree h) * lamThree h := by
    rw [hl, one_mul]
  rw [e1, e2]
  module

variable (h) in
noncomputable abbrev ellThree :
    (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h))⁻¹ * h

structure CommThree (h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) : Prop where
  two : (2 : K) ≠ 0
  map : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v
  comm : h * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * h

namespace CommThree

variable (hh : CommThree h)
include hh

theorem lam : lamThree h * lamThree h = 1 := lam_mul_self hh.two hh.map hh.comm

theorem mem_orthogonalGroup : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh.map

theorem ell_map (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    quadOdd 3 K (ellThree h v) = quadOdd 3 K v := by
  rw [ellThree, LinearEquiv.mul_apply, map_of_mem (inv_mem
    (eichler_mem_orthogonalGroup (quadOdd 3 K) _ _)), hh.map]

theorem ell_mem_orthogonalGroup :
    ellThree h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh.ell_map

theorem ell_eTwo : ellThree h (oddVec 3 K 2 true) = lamThree h • oddVec 3 K 2 true := by
  rw [ellThree, LinearEquiv.mul_apply, apply_eTwo_eq_smul hh.two hh.comm,
    eichler_inv polar_eTwo_yThree, eichler_apply_smul_self]

theorem ell_fTwo : ellThree h (oddVec 3 K 2 false) = lamThree h • oddVec 3 K 2 false := by
  rw [ellThree, LinearEquiv.mul_apply, ← eichler_yThree_apply hh.lam
    (by rw [hh.map, quadOdd_fTwo])]
  exact LinearEquiv.symm_apply_apply _ _

theorem ell_comm : ellThree h * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * ellThree h := by
  have hc : (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h))⁻¹ *
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
        (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h))⁻¹ :=
    rootGroup_commute (inv_mem (eichler_mem_rootGroup polar_eTwo_yThree))
      (eichler_mem_rootGroup polar_eTwo_z)
  rw [ellThree, mul_assoc, hh.comm, ← mul_assoc, hc, mul_assoc]

theorem smul_ell_eTwo : lamThree h • ellThree h (oddVec 3 K 2 true) = oddVec 3 K 2 true := by
  rw [hh.ell_eTwo, smul_smul, hh.lam, one_smul]

theorem smul_ell_fTwo : lamThree h • ellThree h (oddVec 3 K 2 false) = oddVec 3 K 2 false := by
  rw [hh.ell_fTwo, smul_smul, hh.lam, one_smul]

theorem ell_z : ellThree h (oddZ 3 K) = lamThree h • oddZ 3 K := by
  have hO := hh.ell_mem_orthogonalGroup
  have hconj := eichler_conj hO (oddVec 3 K 2 true) (oddZ 3 K)
  rw [hh.ell_comm, mul_inv_cancel_right, hh.ell_eTwo, eichler_smul_left] at hconj
  have hpe : polar (quadOdd 3 K) (oddVec 3 K 2 true) (lamThree h • ellThree h (oddZ 3 K)) = 0 := by
    rw [polar_smul_right, ← hh.smul_ell_eTwo, polar_smul_left, polar_map_of_mem hO,
      polar_eTwo_z, smul_zero, smul_zero]
  have hpf : polar (quadOdd 3 K) (oddVec 3 K 2 false) (lamThree h • ellThree h (oddZ 3 K)) = 0 := by
    rw [polar_smul_right, ← hh.smul_ell_fTwo, polar_smul_left, polar_map_of_mem hO,
      polar_fTwo_z, smul_zero, smul_zero]
  have hQz : quadOdd 3 K (lamThree h • ellThree h (oddZ 3 K)) = 1 := by
    rw [QuadraticMap.map_smul, map_of_mem hO, quadOdd_oddZ, hh.lam, one_smul]
  have h1 := LinearEquiv.congr_fun hconj (oddVec 3 K 2 false)
  rw [eichler_apply quadOdd_eTwo hpe, eichlerThree_apply] at h1
  simp only [polar_fTwo_eTwo, polar_fTwo_z, hpf, hQz, one_smul, mul_one, zero_add] at h1
  rw [sub_left_inj, add_right_inj] at h1
  conv_rhs => rw [h1]
  rw [smul_smul, hh.lam, one_smul]

theorem ell_apply_of_fix {x : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hx : (frame01 K).La (-1) x = x) :
    ellThree h x = lamThree h • x := by
  rw [eq_of_La_neg_one_apply_eq hh.two hx, map_add, map_add, map_smul, map_smul, map_smul,
    hh.ell_eTwo, hh.ell_fTwo, hh.ell_z]
  module

theorem ell_commute_La :
    ellThree h * (frame01 K).La (-1) = (frame01 K).La (-1) * ellThree h := by
  have hO := hh.ell_mem_orthogonalGroup
  refine commute_La_of_maps (frame01 K) (fun x hx => ?_) (fun X => ?_)
  · rw [hh.ell_apply_of_fix ((frame01 K).La_apply_of_coords_eq_zero (-1) hx), map_smul, hx,
      smul_zero]
  · set v := ellThree h ((frame01 K).incl X) with hv
    have hr : v - (frame01 K).incl ((frame01 K).coords v) = 0 := by
      have hc : (frame01 K).coords (v - (frame01 K).incl ((frame01 K).coords v)) = 0 := by
        rw [map_sub, (frame01 K).coords_incl, sub_self]
      have hperp : ∀ u, (frame01 K).coords u = 0 → lamThree h • ellThree h u = u →
          polar (quadOdd 3 K) (v - (frame01 K).incl ((frame01 K).coords v)) u = 0 := by
        intro u hu hlu
        rw [polar_sub_left, polar_incl_of_coords_eq_zero _ hu, sub_zero, hv, ← hlu,
          polar_smul_right, polar_map_of_mem hO, polar_incl_of_coords_eq_zero _ hu, smul_zero]
      refine eq_zero_of_polar_eq_zero hh.two (fun m s => ?_) ?_
      · by_cases hm : m = 2
        · subst hm
          cases s
          · exact hperp _ coords_fTwo hh.smul_ell_fTwo
          · exact hperp _ coords_eTwo hh.smul_ell_eTwo
        · exact polar_eq_zero_of_coords_eq_zero hc m hm s
      · exact hperp _ coords_z (by rw [hh.ell_z, smul_smul, hh.lam, one_smul])
    exact sub_eq_zero.mp hr

end CommThree

end CFSG.ComponentClassification.HarrisLit.T1.S74
