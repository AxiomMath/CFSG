module

public import CFSG.CGT.Stroth77.Extension22FourZero
public import CFSG.CGT.Stroth77.Extension22Final
import all CFSG.CGT.Stroth77.Extension22Final
import all CFSG.CGT.Stroth77.Extension22FourZero
public import CFSG.CGT.Stroth77.Extension22FourAssembly
public import CFSG.CGT.Stroth77.Extension22FourBasis2
public import CFSG.CGT.Stroth77.Extension22FourQuot

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative commutatorElement

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem StrothTypeData.c_eq_of_e_eq {B : Subgroup S} {τ : StrothTypeIndex}
    (D : StrothTypeData B τ) {x : B}
    (h : D.e (Additive.ofMul x) = (Torus.c : Torus τ.k)) : D.c = x := by
  have h2 : D.e.symm (Torus.c : Torus τ.k) = Additive.ofMul x := by
    rw [← h, AddEquiv.symm_apply_apply]
  show Additive.toMul (D.e.symm (Torus.c : Torus τ.k)) = x
  rw [h2, toMul_ofMul]

theorem StrothTypeData.a_eq_of_e_eq {B : Subgroup S} {τ : StrothTypeIndex}
    (D : StrothTypeData B τ) {x : B}
    (h : D.e (Additive.ofMul x) = (Torus.a : Torus τ.k)) : D.a = x := by
  have h2 : D.e.symm (Torus.a : Torus τ.k) = Additive.ofMul x := by
    rw [← h, AddEquiv.symm_apply_apply]
  show Additive.toMul (D.e.symm (Torus.a : Torus τ.k)) = x
  rw [h2, toMul_ofMul]

theorem StrothTypeData.b_eq_of_e_eq {B : Subgroup S} {τ : StrothTypeIndex}
    (D : StrothTypeData B τ) {x : B}
    (h : D.e (Additive.ofMul x) = (Torus.b : Torus τ.k)) : D.b = x := by
  have h2 : D.e.symm (Torus.b : Torus τ.k) = Additive.ofMul x := by
    rw [← h, AddEquiv.symm_apply_apply]
  show Additive.toMul (D.e.symm (Torus.b : Torus τ.k)) = x
  rw [h2, toMul_ofMul]

theorem one_le_of_noInvolutionsCentralizing_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m := by
  by_contra hlt
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c D hBC hC hrel (hL D.u_mem_L) (hL D.ρ_mem_L) hH hcS hne
  have hc1 : (D.c : S) = 1 := by
    rw [← orderOf_eq_one_iff]
    have h := D.orderOf_c
    rw [m_t100] at h
    simpa using h
  exact hdB (hH d (hcS hdC) (by rw [hd2, hc1]) (hC hdC))

theorem two_le_succ_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    2 ≤ m + 1 := by
  have hm := one_le_of_noInvolutionsCentralizing_of_data D hBC hC hrel hL hH hcS hne
  omega

theorem strothTypeData_t300_or_t310_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    ∃ d ∈ C, d * d = (D.c : S) ∧
      ((∃ D' : StrothTypeData C (StrothTypeIndex.t300 (m + 1)),
          D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ ∧
            (D'.c : S) = d ∧ (D'.a : S) = D.a ∧ (D'.b : S) = D.b) ∨
        (∃ D' : StrothTypeData C (StrothTypeIndex.t310 (m + 1)
            (two_le_succ_of_data D hBC hC hrel hL hH hcS hne)),
          D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ ∧
            (D'.c : S) = d ∧ (D'.a : S) = D.a ∧ (D'.b : S) = D.b)) := by
  classical
  have hm : 1 ≤ m := one_le_of_noInvolutionsCentralizing_of_data D hBC hC hrel hL hH hcS hne
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c D hBC hC hrel (hL D.u_mem_L) (hL D.ρ_mem_L) hH hcS hne
  obtain ⟨ε, δ, hε1, hδ1, hX⟩ := form_xU D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨α, q, hα1, hq1, hY⟩ := form_yT D hBC hC hrel hdC hdB hd2 hL hm
  obtain ⟨θ, η, hη1, hθ1, hZ⟩ := form_zR D hBC hC hrel hdC hdB hd2 hL hm
  have hqq : q = ε :=
    bit_q (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL)
      hm hq1 hε1 hX hY hZ
  have hee : η = δ :=
    bit_eta (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL)
      hm hδ1 hη1 hX hZ
  let d' : S := dAdj D d α θ δ
  have hd'C : d' ∈ C := dAdj_mem D hBC hdC α θ δ
  have hd'B : d' ∉ B := dAdj_notMem D hm hdB α θ δ
  have hd'2 : d' * d' = (D.c : S) := dAdj_sq D hBC hC hrel hdC hd2 hm α θ δ
  let E : TorusBasisEquiv D hBC d' hd'C :=
    addEquivOfSq D hBC hC hrel hd'C hd'B hd'2
  have hd'C' : d' ∈ C := hd'C
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  rcases hε01 with rfl | rfl
  ·
    have huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems D hBC hd'C j))) =
        (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.uv_mem_L) D.uv_mem
              (conj_eq_bUV (D := D) hBC hrel hdC hdB hL))
            (ec_bUV' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (q := q) (η := η) (hq := hqq) (hη := hee) (hY := hY) (hZ := hZ)), Type300.uv_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
        refine gens_eq_of_mul (t0 := -3 * (α : ℤ)) (t1 := 0) (t2 := 0) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k]]
          linear_combination (3 * (α : ℤ)) * two_mul_two_pow_int m
        · ring
        · ring
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (ec_conj_a_uv D), Type300.uv_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type300.action (m + 1)).φuv (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (ec_conj_b_uv D), Type300.uv_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    have ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems D hBC hd'C j))) =
        (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.t_mem_L) D.t_mem
              (conj_eq_bT (D := D) hBC hrel hdC hdB hL))
            (ec_bT' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (q := q) (hq := hqq) (hY := hY)), Type300.t_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (ec_conj_a_t D), Type300.t_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type300.action (m + 1)).φt (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (ec_conj_b_t D), Type300.t_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    have hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems D hBC hd'C j))) =
        (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.u_mem_L) D.u_mem
              (conj_eq_bU (D := D) hBC hrel hdC hdB hL))
            (ec_bU' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 0) (hε := by omega) (hX := hX)), Type300.u_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (ec_conj_a_u D), Type300.u_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type300.action (m + 1)).φu (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (ec_conj_b_u D), Type300.u_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    have hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems D hBC hd'C j))) =
        (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.ρ_mem_L) D.ρ_mem
              (conj_eq_bR (D := D) hBC hrel hdC hdB hL))
            (ec_bR' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (η := η) (hη := hee) (hZ := hZ)), Type300.rho_c (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (ec_conj_a_ρ D), Type300.rho_a (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type300.action (m + 1)).φρ (gen (Type300.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (ec_conj_b_ρ D), Type300.rho_b (m + 1)]
        simp only [Torus.c, Torus.a, Torus.b]
        module
    let D' : StrothTypeData C (StrothTypeIndex.t300 (m + 1)) :=
      { e := E.e
        uv := D.uv
        t := D.t
        u := D.u
        ρ := D.ρ
        uv_sq := D.uv_sq
        t_sq := D.t_sq
        uv_comm_t := D.uv_comm_t
        rho_cube := D.rho_cube
        u_sq := D.u_sq
        u_rho := D.u_rho
        uv_rho := D.uv_rho
        t_rho := D.t_rho
        uv_comm_u := D.uv_comm_u
        t_u := D.t_u
        uv_mem := hL D.uv_mem_L
        t_mem := hL D.t_mem_L
        u_mem := hL D.u_mem_L
        ρ_mem := hL D.ρ_mem_L
        uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E.e
          (Type300.action (m + 1)).φuv E.e_d E.e_a E.e_b (huv 0) (huv 1) (huv 2)
        t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E.e
          (Type300.action (m + 1)).φt E.e_d E.e_a E.e_b (ht 0) (ht 1) (ht 2)
        u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E.e
          (Type300.action (m + 1)).φu E.e_d E.e_a E.e_b (hu 0) (hu 1) (hu 2)
        ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
          (Type300.action (m + 1)).φρ E.e_d E.e_a E.e_b (hρ 0) (hρ 1) (hρ 2) }
    refine ⟨d', hd'C, hd'2, Or.inl ⟨D', rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩⟩
    · have h1 : D'.e (Additive.ofMul (⟨d', hd'C⟩ : C)) =
          (Torus.c : Torus (Type300.k (m + 1))) := E.e_d
      exact congrArg Subtype.val (StrothTypeData.c_eq_of_e_eq D' h1)
    · have h1 : D'.e (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) =
          (Torus.a : Torus (Type300.k (m + 1))) := E.e_a
      exact congrArg Subtype.val (StrothTypeData.a_eq_of_e_eq D' h1)
    · have h1 : D'.e (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) =
          (Torus.b : Torus (Type300.k (m + 1))) := E.e_b
      exact congrArg Subtype.val (StrothTypeData.b_eq_of_e_eq D' h1)

  ·
    have huv : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElems D hBC hd'C j))) =
        (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.uv_mem_L) D.uv_mem
              (conj_eq_bUV (D := D) hBC hrel hdC hdB hL))
            (ec_bUV' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (q := q) (η := η) (hq := hqq) (hη := hee) (hY := hY) (hZ := hZ))]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 0) =
            (-3 : ℤ) • gen (Type300.k (m + 1)) 0 + ((2 : ℤ) * 2 ^ (m - 1) - 1) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        refine gens_eq_of_mul (t0 := -3 * (α : ℤ)) (t1 := 0) (t2 := 0) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k]]
          linear_combination (3 * (α : ℤ)) * two_mul_two_pow_int m
        · rw [two_pow_succ_int hm]; ring
        · ring
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (ec_conj_a_uv D)]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 1) =
            (4 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + (2 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.uv_mem_L) D.uv_mem
            (ec_conj_b_uv D)]
        rw [show (Type310.action (m + 1) (by omega)).φuv (gen (Type310.k (m + 1)) 2) =
            ((-32 : ℤ) * 2 ^ (m - 1) + 4) • gen (Type300.k (m + 1)) 0 + ((-8 : ℤ) * 2 ^ (m - 1) + 2) • gen (Type300.k (m + 1)) 1 + ((-8 : ℤ) * 2 ^ (m - 1) + 1) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.uv_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        refine gens_eq_of_mul (t0 := 8) (t1 := 2) (t2 := 2) ?_ ?_ ?_
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 0) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 1) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
        · rw [show ((2 : ℤ) ^ (Type300.k (m + 1)) 2) = 2 ^ (m + 1) by simp [Type300.k],
              two_pow_succ_eq_four hm]
          ring
    have ht : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElems D hBC hd'C j))) =
        (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.t_mem_L) D.t_mem
              (conj_eq_bT (D := D) hBC hrel hdC hdB hL))
            (ec_bT' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (q := q) (hq := hqq) (hY := hY))]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + ((2 : ℤ) * 2 ^ (m - 1)) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        rw [two_pow_succ_int hm]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (ec_conj_a_t D)]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (-1 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.t_mem_L) D.t_mem
            (ec_conj_b_t D)]
        rw [show (Type310.action (m + 1) (by omega)).φt (gen (Type310.k (m + 1)) 2) =
            (-4 : ℤ) • gen (Type300.k (m + 1)) 0 + (-2 : ℤ) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.t_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
    have hu : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElems D hBC hd'C j))) =
        (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.u_mem_L) D.u_mem
              (conj_eq_bU (D := D) hBC hrel hdC hdB hL))
            (ec_bU' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (ε := 1) (hε := by omega) (hX := hX))]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 0) =
            ((2 : ℤ) * 2 ^ (m - 1) + 1) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (ec_conj_a_u D)]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.u_mem_L) D.u_mem
            (ec_conj_b_u D)]
        rw [show (Type310.action (m + 1) (by omega)).φu (gen (Type310.k (m + 1)) 2) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (1 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.u_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
    have hρ : ∀ j : Fin 3, E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElems D hBC hd'C j))) =
        (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) j) := by
      intro j
      fin_cases j
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d', hd'C⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 0)
        rw [E_image_d (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (conj_dAdj (D := D) hBC hdC hm α θ δ (hL D.ρ_mem_L) D.ρ_mem
              (conj_eq_bR (D := D) hBC hrel hdC hdB hL))
            (ec_bR' (D := D) (hBC := hBC) (hrel := hrel) (hdC := hdC) (hdB := hdB) (hL := hL) (hm := hm) (α := α) (θ := θ) (δ := δ) (η := η) (hη := hee) (hZ := hZ))]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 0) =
            (1 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (0 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_c (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        simp only [Torus.c, Torus.a, Torus.b, Nat.cast_zero, zero_mul, zero_smul]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 1)
        rw [E_image_a (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (ec_conj_a_ρ D)]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 1) =
            (0 : ℤ) • gen (Type300.k (m + 1)) 0 + (0 : ℤ) • gen (Type300.k (m + 1)) 1 + (1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_a (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
      · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) = (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 2)
        rw [E_image_b (D := D) hBC hd'C hd'2 E (hL D.ρ_mem_L) D.ρ_mem
            (ec_conj_b_ρ D)]
        rw [show (Type310.action (m + 1) (by omega)).φρ (gen (Type310.k (m + 1)) 2) =
            (-4 : ℤ) • gen (Type300.k (m + 1)) 0 + (-1 : ℤ) • gen (Type300.k (m + 1)) 1 + (-1 : ℤ) • gen (Type300.k (m + 1)) 2 from by
          rw [Type310.rho_b (m + 1) (by omega)]
          try rw [show m + 1 - 2 = m - 1 from by omega]
          simp only [Torus.c, Torus.a, Torus.b]
          rfl]
        module
    let D' : StrothTypeData C (StrothTypeIndex.t310 (m + 1) (two_le_succ_of_data D hBC hC hrel hL hH hcS hne)) :=
      { e := E.e
        uv := D.uv
        t := D.t
        u := D.u
        ρ := D.ρ
        uv_sq := D.uv_sq
        t_sq := D.t_sq
        uv_comm_t := D.uv_comm_t
        rho_cube := D.rho_cube
        u_sq := D.u_sq
        u_rho := D.u_rho
        uv_rho := D.uv_rho
        t_rho := D.t_rho
        uv_comm_u := D.uv_comm_u
        t_u := D.t_u
        uv_mem := hL D.uv_mem_L
        t_mem := hL D.t_mem_L
        u_mem := hL D.u_mem_L
        ρ_mem := hL D.ρ_mem_L
        uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E.e
          (Type310.action (m + 1) (by omega)).φuv E.e_d E.e_a E.e_b (huv 0) (huv 1) (huv 2)
        t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E.e
          (Type310.action (m + 1) (by omega)).φt E.e_d E.e_a E.e_b (ht 0) (ht 1) (ht 2)
        u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E.e
          (Type310.action (m + 1) (by omega)).φu E.e_d E.e_a E.e_b (hu 0) (hu 1) (hu 2)
        ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E.e
          (Type310.action (m + 1) (by omega)).φρ E.e_d E.e_a E.e_b (hρ 0) (hρ 1) (hρ 2) }
    refine ⟨d', hd'C, hd'2, Or.inr ⟨D', rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩⟩
    · have h1 : D'.e (Additive.ofMul (⟨d', hd'C⟩ : C)) =
          (Torus.c : Torus (Type300.k (m + 1))) := E.e_d
      exact congrArg Subtype.val (StrothTypeData.c_eq_of_e_eq D' h1)
    · have h1 : D'.e (Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C)) =
          (Torus.a : Torus (Type300.k (m + 1))) := E.e_a
      exact congrArg Subtype.val (StrothTypeData.a_eq_of_e_eq D' h1)
    · have h1 : D'.e (Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) =
          (Torus.b : Torus (Type300.k (m + 1))) := E.e_b
      exact congrArg Subtype.val (StrothTypeData.b_eq_of_e_eq D' h1)

theorem not_isCyclic_quotient_four_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    letI : (B.subgroupOf C).Normal :=
      Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
    ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  letI : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  intro hcycQ
  classical
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcycQ
  letI : CommGroup C := { mul_comm := hcomm }
  obtain ⟨q₀, hq₀⟩ := hcycQ.exists_generator
  obtain ⟨z, hzq⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₀
  let q : C ⧸ B.subgroupOf C := QuotientGroup.mk' (B.subgroupOf C) z
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 :=
    card_quotient_four hBC hC hrel
  have hq_gen : Subgroup.zpowers q = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hqq : q = q₀ := hzq
    rw [hqq]
    exact hq₀ y
  have hq_order : orderOf q = 4 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hq_gen, hQcard]
  have hq4 : q ^ 4 = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  have hz4H : z ^ 4 ∈ B.subgroupOf C := by
    have h : QuotientGroup.mk' (B.subgroupOf C) (z ^ 4) = 1 := by
      simpa [q, map_pow] using hq4
    exact (QuotientGroup.eq_one_iff _).mp h
  have hz4B : (z : S) ^ 4 ∈ B := by
    have := Subgroup.mem_subgroupOf.mp hz4H
    simpa using this
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf q ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hq_order] at hdvd
    norm_num at hdvd
  have hAutSq : ∀ σ : MulAut (C ⧸ B.subgroupOf C), σ * σ = 1 := by
    intro σ
    have hcard : Nat.card (MulAut (C ⧸ B.subgroupOf C)) = 2 := by
      rw [IsCyclic.card_mulAut (C ⧸ B.subgroupOf C), hQcard]
      decide
    have h : orderOf σ ∣ 2 := by
      rw [← hcard]
      exact orderOf_dvd_natCard σ
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h
  have huvC : D.uv ∈ Subgroup.normalizer C := hL D.uv_mem_L
  have htC : D.t ∈ Subgroup.normalizer C := hL D.t_mem_L
  have hρC : D.ρ ∈ Subgroup.normalizer C := hL D.ρ_mem_L
  let Auv : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.uv huvC D.uv_mem
  let At : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.t htC D.t_mem
  let Ar : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.ρ hρC D.ρ_mem
  have hAuv_sq : Auv * Auv = 1 := by
    have h := conjByAutQuotient_pow D.uv huvC D.uv_mem 2
    simpa [pow_two, D.uv_sq, conjByAutQuotient_one] using h.symm
  have hAt_sq : At * At = 1 := by
    have h := conjByAutQuotient_pow D.t htC D.t_mem 2
    simpa [pow_two, D.t_sq, conjByAutQuotient_one] using h.symm
  have hAr_cube : Ar ^ 3 = 1 := by
    have h := conjByAutQuotient_pow D.ρ hρC D.ρ_mem 3
    have hρ3 : D.ρ * (D.ρ * D.ρ) = 1 := by
      rw [← mul_assoc]
      exact D.rho_cube
    simpa [pow_three, mul_assoc, hρ3, conjByAutQuotient_one] using h.symm
  have hcomp1 : (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC) =
      (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := by
    have h1 := conjByHom_mul D.uv D.ρ huvC hρC
    have h2 := conjByHom_mul D.ρ D.t hρC htC
    have h3 : conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) =
        conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) :=
      conjByHom_mul_eq huvC hρC hρC htC D.uv_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC)
        = conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) := h1.symm
      _ = conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) := h3
      _ = (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := h2
  have hcomp2 : (conjByHom D.ρ hρC).comp (conjByHom D.t htC) =
      (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
    have h1 := conjByHom_mul D.t D.ρ htC hρC
    have h2 := conjByHom_mul (D.ρ * D.uv) D.t (Subgroup.mul_mem _ hρC huvC) htC
    have h3 := conjByHom_mul D.ρ D.uv hρC huvC
    have h4 : conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) =
        conjByHom ((D.ρ * D.uv) * D.t) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) :=
      conjByHom_mul_eq htC hρC (Subgroup.mul_mem _ hρC huvC) htC D.t_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.t htC)
        = conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) := h1.symm
      _ = conjByHom ((D.ρ * D.uv) * D.t)
            (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) := h4
      _ = (conjByHom D.t htC).comp (conjByHom (D.ρ * D.uv)
            (Subgroup.mul_mem _ hρC huvC)) := h2
      _ = (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
            rw [h3]
  have hAr : Ar = 1 := by
    have hsq := hAutSq Ar
    calc Ar = Ar * 1 := (mul_one Ar).symm
      _ = Ar * (Ar * Ar) := by rw [hsq]
      _ = Ar * Ar * Ar := by rw [← mul_assoc]
      _ = Ar ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := hAr_cube
  have hAuv_Ar : Ar * Auv = At * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk (by simpa using DFunLike.congr_fun hcomp1 x)
  have hAt_Ar : Ar * At = At * Auv * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk
        (by simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hcomp2 x)
  have hAuv_eq_At : Auv = At := by
    simpa [hAr] using hAuv_Ar
  have hAuv : Auv = 1 := by
    have h := hAt_Ar
    rw [hAr] at h
    have h' : At = At * Auv := by simpa using h
    have h'' : At * At = At * (At * Auv) := congrArg (fun x => At * x) h'
    rw [← mul_assoc] at h''
    have h''' : (1 : MulAut (C ⧸ B.subgroupOf C)) = Auv := by
      simpa [hAt_sq] using h''
    exact h'''.symm
  have hAt : At = 1 := hAuv_eq_At.symm.trans hAuv
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  have hcases : (⟨(z : S) ^ 4, hz4B⟩ : B) ∈ fourB D ∨
      (⟨(z : S) ^ 4, hz4B⟩ : B) * D.c ^ (-2 : ℤ) ∈ fourB D := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      exact Or.inl (t100_fixed_rho_t_mod_four_of_mem_zero hρfix)
    · exact t100_fixed_rho_t_mod_four_of_mem (m := m) (D := D) hpos hρfix htfix
  rcases hcases with hy4 | hyc2
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hy4
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC := by
      apply Subtype.ext
      simpa [sC, yC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = 1 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * yC⁻¹ := by rw [hz4C, hsC4]
        _ = 1 := mul_inv_cancel yC
    let winv : C := wC ^ 2
    have hwinv2 : winv * winv = 1 := by
      have h : winv * winv = wC ^ 4 := by
        show (wC ^ 2) * (wC ^ 2) = wC ^ 4
        group
      rw [h, hw4]
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hq2eq : q ^ 2 = 1 := by
        rw [← hmkw, ← map_pow]
        simpa [winv] using h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hyc2
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    let cC : C := ⟨D.c, hBC D.c.2⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC * cC ^ (-2 : ℤ) := by
      apply Subtype.ext
      simpa [sC, yC, cC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = cC ^ 2 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * (yC * cC ^ (-2 : ℤ))⁻¹ := by rw [hz4C, hsC4]
        _ = cC ^ 2 := by
            have hcinv : (cC ^ (-2 : ℤ))⁻¹ = cC ^ 2 := by
              simpa using (zpow_neg cC (-2 : ℤ)).symm
            rw [mul_inv_rev, hcinv]
            calc yC * (cC ^ 2 * yC⁻¹) = (yC * cC ^ 2) * yC⁻¹ := by rw [mul_assoc]
              _ = (cC ^ 2 * yC) * yC⁻¹ := by rw [mul_comm yC (cC ^ 2)]
              _ = cC ^ 2 * (yC * yC⁻¹) := by rw [mul_assoc]
              _ = cC ^ 2 := by rw [mul_inv_cancel, mul_one]
    let winv : C := wC ^ 2 * cC⁻¹
    have hwinv2 : winv * winv = 1 := by
      have hcomm : Commute (wC ^ 2) (cC⁻¹) := (Commute.all wC cC).pow_left 2 |>.inv_right
      have h : winv * winv = wC ^ 4 * cC ^ (-2 : ℤ) := by
        rw [show winv * winv = (wC ^ 2 * cC⁻¹) ^ 2 by rw [pow_two]]
        rw [hcomm.mul_pow 2, ← pow_mul, inv_pow]
        norm_num
      rw [h, hw4, zpow_neg]
      group
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hc1 : QuotientGroup.mk' (B.subgroupOf C) cC = 1 :=
        (QuotientGroup.eq_one_iff cC).mpr (Subgroup.mem_subgroupOf.mpr D.c.2)
      have hq2eq : q ^ 2 = 1 := by
        have hwinv : QuotientGroup.mk' (B.subgroupOf C) winv = q ^ 2 := by
          rw [show winv = wC ^ 2 * cC⁻¹ from rfl, map_mul, map_pow, map_inv, hmkw, hc1]
          simp
        rw [← hwinv]
        exact h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))

theorem isMulCommutative_of_relIndex_four_of_not_cyclic_of_data
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    IsMulCommutative C := by
  classical
  let Bc : Subgroup C := B.subgroupOf C
  have hBcCenter : Bc ≤ Subgroup.center C := by
    simpa [Bc] using subgroupOf_le_center hBC hC
  haveI : Bc.Normal := Subgroup.normal_of_le_center hBcCenter
  have hncyc' : ¬ IsCyclic (C ⧸ Bc) := by
    simpa [Bc] using hncyc
  have hcardQ : Nat.card (C ⧸ Bc) = 4 := by
    simpa [Bc] using card_quotient_four (B := B) (C := C) hBC hC hrel
  have hexpQ : ∀ q : C ⧸ Bc, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc'
    · exact h
  have hcommQ : IsMulCommutative (C ⧸ Bc) := isMulCommutative_of_forall_mul_self hexpQ
  have hcomm_le_Bc : _root_.commutator C ≤ Bc :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
  have hsqBc : ∀ x : C, x * x ∈ Bc := by
    intro x
    have h : (QuotientGroup.mk' Bc x) * (QuotientGroup.mk' Bc x) = 1 := hexpQ _
    have h' : QuotientGroup.mk' Bc (x * x) = 1 := by rwa [map_mul]
    exact (QuotientGroup.eq_one_iff (N := Bc) (x * x)).mp (by simpa using h')
  haveI : Fintype (C ⧸ Bc) := Fintype.ofFinite _
  have hone_lt : 1 < Fintype.card (C ⧸ Bc) := by
    rw [Fintype.card_eq_nat_card, hcardQ]
    norm_num
  obtain ⟨q₁, hq₁⟩ := Fintype.exists_ne_of_one_lt_card hone_lt (1 : C ⧸ Bc)
  have hq₁top : Subgroup.zpowers q₁ ≠ ⊤ := by
    intro htop
    exact hncyc' (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q₁, htop⟩)
  have hnot_subset : ¬ (⊤ : Set (C ⧸ Bc)) ⊆ (Subgroup.zpowers q₁ : Set (C ⧸ Bc)) := by
    intro h
    exact hq₁top (le_antisymm le_top h)
  obtain ⟨q₂, -, hq₂⟩ := Set.not_subset.mp hnot_subset
  have hq₂one : q₂ ≠ 1 := by
    intro h
    apply hq₂
    rw [h]
    exact Subgroup.one_mem _
  have hq₁₂ : q₁ ≠ q₂ := by
    intro h
    apply hq₂
    rw [← h]
    exact Subgroup.mem_zpowers q₁
  haveI : Nontrivial (C ⧸ Bc) := Fintype.one_lt_card_iff_nontrivial.mp hone_lt
  haveI : IsKleinFour (C ⧸ Bc) := by
    refine ⟨hcardQ, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro q hq
    have hq2 : q * q = 1 := hexpQ q
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hq2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hq
    · exact h2
  have hgen : Subgroup.closure ({q₁, q₂} : Set (C ⧸ Bc)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have huniv : ({q₁ * q₂, q₁, q₂, (1 : C ⧸ Bc)} : Finset (C ⧸ Bc)) = Finset.univ :=
      IsKleinFour.eq_finset_univ hq₁ hq₂one hq₁₂
    have hx : x ∈ ({q₁ * q₂, q₁, q₂, (1 : C ⧸ Bc)} : Finset (C ⧸ Bc)) := by
      rw [huniv]
      exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective Bc q₁
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective Bc q₂
  let E : Subgroup C := Subgroup.zpowers e
  let F : Subgroup C := Subgroup.zpowers f
  have hmapH : (Bc ⊔ E ⊔ F).map (QuotientGroup.mk' Bc) = ⊤ := by
    change ((Bc ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f).map
      (QuotientGroup.mk' Bc) = ⊤
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have hker : Bc.map (QuotientGroup.mk' Bc) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hker, bot_sup_eq, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    simpa [Set.pair_comm] using hgen
  have hHtop : Bc ⊔ E ⊔ F = ⊤ :=
    eq_top_of_le_of_map_quotient_eq_top (N := Bc) (K := Bc ⊔ E ⊔ F)
      (le_sup_of_le_left le_sup_left) hmapH
  let z : C := ⁅e, f⁆
  let N : Subgroup C := Subgroup.zpowers z
  have hzBc : z ∈ Bc := by
    have hzC : z ∈ _root_.commutator C := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet e f)
    exact hcomm_le_Bc hzC
  have hzCenter : z ∈ Subgroup.center C := hBcCenter hzBc
  have hNleBc : N ≤ Bc := Subgroup.zpowers_le.mpr hzBc
  have hNcenter : N ≤ Subgroup.center C := hNleBc.trans hBcCenter
  haveI : N.Normal := Subgroup.normal_of_le_center hNcenter
  have hz2 : z * z = 1 := by
    have hcomm_e_z : Commute e z := Subgroup.mem_center_iff.mp hzCenter e
    have hpow := hcomm_e_z.commutatorElement_pow_left 2
    have he2 : Commute (e * e) f :=
      (Subgroup.mem_center_iff.mp (hBcCenter (hsqBc e)) f).symm
    calc
      z * z = ⁅e, f⁆ ^ 2 := by
        change ⁅e, f⁆ * ⁅e, f⁆ = ⁅e, f⁆ ^ 2
        rw [pow_two]
      _ = ⁅e ^ 2, f⁆ := hpow
      _ = ⁅e * e, f⁆ := by rw [pow_two]
      _ = 1 := he2.commutator_eq
  let Te : Subgroup C := commutatorFiberLeft N e
  have hBc_le_Te : Bc ≤ Te := by
    intro b hb
    rw [mem_commutatorFiberLeft]
    have hcomm : Commute e b := Subgroup.mem_center_iff.mp (hBcCenter hb) e
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have hE_le_Te : E ≤ Te := by
    change Subgroup.zpowers e ≤ Te
    rw [Subgroup.zpowers_le, mem_commutatorFiberLeft]
    simpa using N.one_mem
  have hfTe : f ∈ Te := by
    rw [mem_commutatorFiberLeft]
    simpa [z, N] using Subgroup.mem_zpowers z
  have hTeTop : Te = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_Te hE_le_Te) (Subgroup.zpowers_le.mpr hfTe)
  let Tf : Subgroup C := commutatorFiberLeft N f
  have hBc_le_Tf : Bc ≤ Tf := by
    intro b hb
    rw [mem_commutatorFiberLeft]
    have hcomm : Commute f b := Subgroup.mem_center_iff.mp (hBcCenter hb) f
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have heTf : e ∈ Tf := by
    rw [mem_commutatorFiberLeft]
    rw [← commutatorElement_inv]
    exact N.inv_mem (by simpa [z, N] using Subgroup.mem_zpowers z)
  have hF_le_Tf : F ≤ Tf := by
    change Subgroup.zpowers f ≤ Tf
    rw [Subgroup.zpowers_le, mem_commutatorFiberLeft]
    simpa using N.one_mem
  have hTfTop : Tf = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_Tf (Subgroup.zpowers_le.mpr heTf)) hF_le_Tf
  let Ssub : Subgroup C := commutatorCentralizer N
  have hBc_le_S : Bc ≤ Ssub := by
    intro b hb
    rw [mem_commutatorCentralizer]
    intro y
    have hcomm : Commute b y := (Subgroup.mem_center_iff.mp (hBcCenter hb) y).symm
    rw [hcomm.commutator_eq]
    exact N.one_mem
  have heS : e ∈ Ssub := by
    rw [mem_commutatorCentralizer]
    intro y
    have hyTe : y ∈ Te := by rw [hTeTop]; exact Subgroup.mem_top y
    exact mem_commutatorFiberLeft.mp hyTe
  have hfS : f ∈ Ssub := by
    rw [mem_commutatorCentralizer]
    intro y
    have hyTf : y ∈ Tf := by rw [hTfTop]; exact Subgroup.mem_top y
    exact mem_commutatorFiberLeft.mp hyTf
  have hStop : Ssub = ⊤ := by
    rw [eq_top_iff, ← hHtop]
    exact sup_le (sup_le hBc_le_S (Subgroup.zpowers_le.mpr heS))
      (Subgroup.zpowers_le.mpr hfS)
  have hcomm_le_N : _root_.commutator C ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hxS : x ∈ Ssub := by rw [hStop]; exact Subgroup.mem_top x
    exact (mem_commutatorCentralizer.mp hxS) y
  let C' : Subgroup C := _root_.commutator C
  have hC'_le_N : C' ≤ N := hcomm_le_N
  have hC'_le_Bc : C' ≤ Bc := hC'_le_N.trans hNleBc
  haveI : C'.Characteristic := by
    change (_root_.commutator C).Characteristic
    infer_instance
  have hNcard : Nat.card N ≤ 2 := by
    change Nat.card (Subgroup.zpowers z) ≤ 2
    rw [Nat.card_zpowers]
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hz2
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hC'_card : Nat.card C' ≤ 2 := (Subgroup.card_le_of_le hC'_le_N).trans hNcard
  haveI : IsCyclic N := by
    change IsCyclic (Subgroup.zpowers z)
    infer_instance
  haveI : IsCyclic C' := Subgroup.isCyclic_of_le hC'_le_N
  have hAutcard : Nat.card (MulAut C') = 1 := by
    rw [IsCyclic.card_mulAut]
    rw [Nat.totient_eq_one_iff]
    have hpos : 0 < Nat.card C' := Nat.card_pos
    omega
  haveI : Subsingleton (MulAut C') := (Nat.card_eq_one_iff_unique.mp hAutcard).1
  have hfixρ : ∀ x : C, x ∈ C' →
      D.ρ⁻¹ * (x : S) * D.ρ = (x : S) := by
    intro x hx
    let ψ : MulAut C' :=
      MulAut.characteristic C' (conjAutOfMemNormalizer D.ρ⁻¹ (Subgroup.inv_mem _ (hL D.ρ_mem_L)))
    have hψ : ψ = 1 := Subsingleton.elim _ _
    have h := congrArg Subtype.val (congrArg (fun φ : MulAut C' => φ ⟨x, hx⟩) hψ)
    have hS := congrArg (fun y : C => (y : S)) h
    simpa [ψ, conjAutOfMemNormalizer_apply] using hS
  have hfixt : ∀ x : C, x ∈ C' →
      D.t⁻¹ * (x : S) * D.t = (x : S) := by
    intro x hx
    let ψ : MulAut C' :=
      MulAut.characteristic C' (conjAutOfMemNormalizer D.t⁻¹ (Subgroup.inv_mem _ (hL D.t_mem_L)))
    have hψ : ψ = 1 := Subsingleton.elim _ _
    have h := congrArg Subtype.val (congrArg (fun φ : MulAut C' => φ ⟨x, hx⟩) hψ)
    have hS := congrArg (fun y : C => (y : S)) h
    simpa [ψ, conjAutOfMemNormalizer_apply] using hS
  have hC'bot : C' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxB : (x : S) ∈ B := Subgroup.mem_subgroupOf.mp (hC'_le_Bc hx)
    have hρ : conjBy D.ρ_mem ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      have h := hfixρ x hx
      simpa [conjBy] using h
    have ht : conjBy D.t_mem ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply Subtype.ext
      have h := hfixt x hx
      simpa [conjBy] using h
    have hx1 : (⟨x, hxB⟩ : B) = 1 := t100_fixed_rho_t_of_mem D hρ ht
    have hxS : (x : S) = 1 := by
      have := congrArg Subtype.val hx1
      simpa using this
    exact Subtype.ext hxS
  have hcomm_bot : _root_.commutator C = ⊥ := by
    simpa [C'] using hC'bot
  exact (commutator_eq_bot_iff C).mp hcomm_bot
theorem sq_range_eq_ab_of_data
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    (sqQuotientHom (isMulCommutative_of_relIndex_four_of_not_cyclic_of_data D hBC hC hrel hL hncyc)
        D hBC hC hrel hncyc).range = (cParityQuotient D hm).ker := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic_of_data D hBC hC hrel hL hncyc
  refine Subgroup.eq_of_le_of_card_ge
    (sqQuotientHom_range_le_cParity_ker hcommC D hBC hC hrel hncyc hL hH hcS hm) ?_
  rw [sqQuotientHom_range_card hcommC D hBC hC hrel hncyc hH hcS,
    cParityQuotient_ker_card D hm]

theorem exists_sq_eq_a_b_of_data
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    ∃ e f : C, e * e = ⟨D.a, hBC D.a.2⟩ ∧
      f * f = ⟨D.b, hBC D.b.2⟩ := by
  classical
  let hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic_of_data D hBC hC hrel hL hncyc
  let sq := sqQuotientHom hcommC D hBC hC hrel hncyc
  have hca : cParity D hm D.a = 0 := by
    rw [cParity, D.ec_a]
    simp [Torus.a, gen, Pi.single_apply]
  have hcb : cParity D hm D.b = 0 := by
    rw [cParity, D.ec_b]
    simp [Torus.b, gen, Pi.single_apply]
  have ha_range : QuotientGroup.mk' (sqSubgroup D) D.a ∈ sq.range := by
    have hreq := sq_range_eq_ab_of_data D hBC hC hrel hL hncyc hH hcS hm
    rw [show sq.range = (cParityQuotient D hm).ker from hreq]
    rw [MonoidHom.mem_ker, cParityQuotient_mk, cParityHom_apply, hca]
    rfl
  have hb_range : QuotientGroup.mk' (sqSubgroup D) D.b ∈ sq.range := by
    have hreq := sq_range_eq_ab_of_data D hBC hC hrel hL hncyc hH hcS hm
    rw [show sq.range = (cParityQuotient D hm).ker from hreq]
    rw [MonoidHom.mem_ker, cParityQuotient_mk, cParityHom_apply, hcb]
    rfl
  obtain ⟨e0, he0⟩ := MonoidHom.mem_range.mp ha_range
  obtain ⟨f0, hf0⟩ := MonoidHom.mem_range.mp hb_range
  have haC : (⟨D.a, hBC D.a.2⟩ : C) = Subgroup.inclusion hBC D.a := rfl
  have hbC : (⟨D.b, hBC D.b.2⟩ : C) = Subgroup.inclusion hBC D.b := rfl
  let ea : B := ⟨(e0 : S) * (e0 : S),
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc e0⟩
  have hsq_e0 : sq e0 = QuotientGroup.mk' (sqSubgroup D) ea := rfl
  have hza : ea⁻¹ * D.a ∈ sqSubgroup D := by
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp (by simpa [hsq_e0] using he0)
    simpa using h
  obtain ⟨sa, hsa⟩ := exists_sq_eq_of_mem_sqSubgroup D hza
  let saC : C := Subgroup.inclusion hBC sa
  have hsaC : saC * saC = (Subgroup.inclusion hBC ea)⁻¹ * (⟨D.a, hBC D.a.2⟩ : C) := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) hsa
    simpa [saC, ea] using h
  have he_sq : (e0 * saC) * (e0 * saC) = ⟨D.a, hBC D.a.2⟩ := by
    calc (e0 * saC) * (e0 * saC) = (e0 * e0) * (saC * saC) := by
          rw [mul_mul_mul_comm]
      _ = (e0 * e0) * ((Subgroup.inclusion hBC ea)⁻¹ * ⟨D.a, hBC D.a.2⟩) := by rw [hsaC]
      _ = ⟨D.a, hBC D.a.2⟩ := by
          rw [show (e0 * e0 : C) = Subgroup.inclusion hBC ea from rfl]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
  let fb : B := ⟨(f0 : S) * (f0 : S),
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc f0⟩
  have hsq_f0 : sq f0 = QuotientGroup.mk' (sqSubgroup D) fb := rfl
  have hzb : fb⁻¹ * D.b ∈ sqSubgroup D := by
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp (by simpa [hsq_f0] using hf0)
    simpa using h
  obtain ⟨sb, hsb⟩ := exists_sq_eq_of_mem_sqSubgroup D hzb
  let sbC : C := Subgroup.inclusion hBC sb
  have hsbC : sbC * sbC = (Subgroup.inclusion hBC fb)⁻¹ * (⟨D.b, hBC D.b.2⟩ : C) := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) hsb
    simpa [sbC, fb] using h
  have hf_sq : (f0 * sbC) * (f0 * sbC) = ⟨D.b, hBC D.b.2⟩ := by
    calc (f0 * sbC) * (f0 * sbC) = (f0 * f0) * (sbC * sbC) := by
          rw [mul_mul_mul_comm]
      _ = (f0 * f0) * ((Subgroup.inclusion hBC fb)⁻¹ * ⟨D.b, hBC D.b.2⟩) := by rw [hsbC]
      _ = ⟨D.b, hBC D.b.2⟩ := by
          rw [show (f0 * f0 : C) = Subgroup.inclusion hBC fb from rfl]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
  exact ⟨e0 * saC, f0 * sbC, he_sq, hf_sq⟩

theorem torusBasisEquivFour_of_data
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    ∃ e f : C, e * e = ⟨D.a, hBC D.a.2⟩ ∧
      f * f = ⟨D.b, hBC D.b.2⟩ ∧
      Nonempty (TorusBasisEquivFour D hBC e f) := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic_of_data D hBC hC hrel hL hncyc
  obtain ⟨e, f, he, hf⟩ := exists_sq_eq_a_b_of_data D hBC hC hrel hL hncyc hH hcS hm
  exact ⟨e, f, he, hf, torusBasisEquivFour_of_sq hcommC D hBC hrel hm he hf⟩

theorem strothZeroTorusBasis_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hm0 : m = 0) :
    ∃ e f : C, e * e = ⟨D.a, hBC D.a.2⟩ ∧ f * f = ⟨D.b, hBC D.b.2⟩ ∧
      Nonempty (TorusBasisEquivFour D hBC e f) := by
  subst hm0
  classical
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  have hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C) :=
    not_isCyclic_quotient_four_of_data D hBC hC hrel hL hH hcS
  have hcomm : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic_of_data D hBC hC hrel hL hncyc
  have hsqbot : sqSubgroup D = ⊥ := sqSubgroup_eq_bot_of_m_zero D
  have hcardB : Nat.card B = 4 := by
    rw [D.card_t100]
    norm_num
  have htarget : Nat.card (B ⧸ sqSubgroup D) = 4 := by
    rw [hsqbot]
    calc Nat.card (B ⧸ (⊥ : Subgroup B)) = Nat.card B :=
          Nat.card_congr (QuotientGroup.quotientBot (G := B)).toEquiv
      _ = 4 := hcardB
  have hrange : Nat.card (sqQuotientHom hcomm D hBC hC hrel hncyc).range = 4 :=
    sqQuotientHom_range_card hcomm D hBC hC hrel hncyc hH hcS
  have htop : (sqQuotientHom hcomm D hBC hC hrel hncyc).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, htarget]
  have hsurj : Function.Surjective (sqQuotientHom hcomm D hBC hC hrel hncyc) :=
    MonoidHom.range_eq_top.mp htop
  obtain ⟨e, he⟩ := hsurj (QuotientGroup.mk' (sqSubgroup D) D.a)
  obtain ⟨f, hf⟩ := hsurj (QuotientGroup.mk' (sqSubgroup D) D.b)
  have heB : (⟨(e : S) * (e : S), sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc e⟩ :
      B) = D.a := by
    have he' : ((⟨(e : S) * (e : S),
        sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc e⟩ : B) : B ⧸ sqSubgroup D) =
        (D.a : B ⧸ sqSubgroup D) := by
      simpa [sqQuotientHom] using he
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp he'
    rw [hsqbot, Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp h
  have hfB : (⟨(f : S) * (f : S), sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc f⟩ :
      B) = D.b := by
    have hf' : ((⟨(f : S) * (f : S),
        sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc f⟩ : B) : B ⧸ sqSubgroup D) =
        (D.b : B ⧸ sqSubgroup D) := by
      simpa [sqQuotientHom] using hf
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp hf'
    rw [hsqbot, Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp h
  have he_sq : e * e = ⟨D.a, hBC D.a.2⟩ := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) heB
    simpa using h
  have hf_sq : f * f = ⟨D.b, hBC D.b.2⟩ := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) hfB
    simpa using h
  have hgenC : Subgroup.closure
      ({⟨D.c, hBC D.c.2⟩, e, f} : Set C) = ⊤ :=
    closure_c_e_f_of_m_zero hcomm D hBC hrel he_sq hf_sq
  have hgenS : Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S) = C := by
    have himg : C.subtype '' ({⟨D.c, hBC D.c.2⟩, e, f} : Set C) =
        ({(D.c : S), (e : S), (f : S)} : Set S) := by
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨⟨D.c, hBC D.c.2⟩, Or.inl rfl, rfl⟩
        · exact ⟨e, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨f, Or.inr (Or.inr rfl), rfl⟩
    calc Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S)
        = Subgroup.closure (C.subtype '' ({⟨D.c, hBC D.c.2⟩, e, f} : Set C)) := by
          rw [himg]
      _ = (Subgroup.closure ({⟨D.c, hBC D.c.2⟩, e, f} : Set C)).map C.subtype :=
          (MonoidHom.map_closure C.subtype _).symm
      _ = (⊤ : Subgroup C).map C.subtype := by rw [hgenC]
      _ = C := by rw [Subgroup.map_top, Subgroup.range_subtype]
  have haC_order : orderOf (⟨D.a, hBC D.a.2⟩ : C) = 2 ^ (0 + 1) := by
    rw [show (⟨D.a, hBC D.a.2⟩ : C) = Subgroup.inclusion hBC D.a from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a,
      D.orderOf_a, n_t100]
  have hbC_order : orderOf (⟨D.b, hBC D.b.2⟩ : C) = 2 ^ (0 + 1) := by
    rw [show (⟨D.b, hBC D.b.2⟩ : C) = Subgroup.inclusion hBC D.b from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b,
      D.orderOf_b, n_t100]
  have he_order : orderOf e = 2 ^ (0 + 2) :=
    orderOf_eq_two_pow_succ_of_sq (m := 0) he_sq haC_order
  have hf_order : orderOf f = 2 ^ (0 + 2) :=
    orderOf_eq_two_pow_succ_of_sq (m := 0) hf_sq hbC_order
  exact ⟨e, f, he_sq, hf_sq,
    torusBasisEquivFour_of_generators hcomm D hBC hrel hgenS he_order hf_order⟩

@[expose] noncomputable def strothTypeData_t200_of_generator_images
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (huv : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φuv (gen (Type200.k m) j))
    (ht : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φt (gen (Type200.k m) j))
    (hu : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φu (gen (Type200.k m) j))
    (hρ : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φρ (gen (Type200.k m) j)) :
    StrothTypeData C (StrothTypeIndex.t200 m) :=
  { e := E.symm
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_cube := D.rho_cube
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := hL D.uv_mem_L
    t_mem := hL D.t_mem_L
    u_mem := hL D.u_mem_L
    ρ_mem := hL D.ρ_mem_L
    uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E.symm
      (Type200.action m).φuv E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (huv 0) (huv 1) (huv 2)
    t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E.symm
      (Type200.action m).φt E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (ht 0) (ht 1) (ht 2)
    u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E.symm
      (Type200.action m).φu E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (hu 0) (hu 1) (hu 2)
    ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E.symm
      (Type200.action m).φρ E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (hρ 0) (hρ 1) (hρ 2) }

@[expose] noncomputable def strothTypeData_t201_of_generator_images
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (huv : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φuv (gen (Type201.k m) j))
    (ht : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φt (gen (Type201.k m) j))
    (hu : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φu (gen (Type201.k m) j))
    (hρ : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φρ (gen (Type201.k m) j)) :
    StrothTypeData C (StrothTypeIndex.t201 m) :=
  { e := E.symm
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_cube := D.rho_cube
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := hL D.uv_mem_L
    t_mem := hL D.t_mem_L
    u_mem := hL D.u_mem_L
    ρ_mem := hL D.ρ_mem_L
    uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E.symm
      (Type201.action m).φuv E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (huv 0) (huv 1) (huv 2)
    t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E.symm
      (Type201.action m).φt E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (ht 0) (ht 1) (ht 2)
    u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E.symm
      (Type201.action m).φu E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (hu 0) (hu 1) (hu 2)
    ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E.symm
      (Type201.action m).φρ E.symm_gen_zero E.symm_gen_one E.symm_gen_two
      (hρ 0) (hρ 1) (hρ 2) }


theorem strothTypeData_t200_or_t201_of_data
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    ∃ e f : C, e * e = (D.a : S) ∧ f * f = (D.b : S) ∧
      ((∃ D' : StrothTypeData C (StrothTypeIndex.t200 m),
          D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ ∧
            (D'.c : S) = D.c ∧ (D'.a : S) = e ∧ (D'.b : S) = f) ∨
        (∃ D' : StrothTypeData C (StrothTypeIndex.t201 m),
          D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ ∧
            (D'.c : S) = D.c ∧ (D'.a : S) = e ∧ (D'.b : S) = f)) := by
  classical
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  have hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C) :=
    not_isCyclic_quotient_four_of_data D hBC hC hrel hL hH hcS
  obtain ⟨e0, f0, he0, hf0, hE⟩ :
      ∃ e f : C, e * e = ⟨D.a, hBC D.a.2⟩ ∧ f * f = ⟨D.b, hBC D.b.2⟩ ∧
        Nonempty (TorusBasisEquivFour D hBC e f) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · exact strothZeroTorusBasis_of_data D hBC hC hrel hL hH hcS hm0
    · exact torusBasisEquivFour_of_data D hBC hC hrel hL hncyc hH hcS hm
  obtain ⟨E⟩ := hE
  have hcommC : IsMulCommutative C :=
    TorusBasisEquivFour.isMulCommutative_of_torusBasisEquivFour E
  obtain ⟨z, w, hz, hw, E', hImages⟩ :=
    TorusBasisEquivFour.hasType200Or201AdjustedBasis_of_torusBasis E hL he0 hf0
  have he : ((e0 * z) * (e0 * z) : C) = (D.a : S) := by
    have h : (e0 * z) * (e0 * z) = ⟨D.a, hBC D.a.2⟩ := by
      calc (e0 * z) * (e0 * z) = (e0 * e0) * (z * z) := by rw [mul_mul_mul_comm]
        _ = ⟨D.a, hBC D.a.2⟩ := by rw [he0, hz, mul_one]
    exact congrArg Subtype.val h
  have hf : ((f0 * w) * (f0 * w) : C) = (D.b : S) := by
    have h : (f0 * w) * (f0 * w) = ⟨D.b, hBC D.b.2⟩ := by
      calc (f0 * w) * (f0 * w) = (f0 * f0) * (w * w) := by rw [mul_mul_mul_comm]
        _ = ⟨D.b, hBC D.b.2⟩ := by rw [hf0, hw, mul_one]
    exact congrArg Subtype.val h
  refine ⟨e0 * z, f0 * w, he, hf, ?_⟩
  rcases hImages with h | h
  · left
    let D' : StrothTypeData C (StrothTypeIndex.t200 m) :=
      strothTypeData_t200_of_generator_images D hBC hL E' h.uv h.t h.u h.ρ
    have hc : (D'.c : S) = D.c := by
      have h1 : D'.e (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) =
          (Torus.c : Torus (Type200.k m)) := E'.symm_gen_zero
      exact congrArg Subtype.val (StrothTypeData.c_eq_of_e_eq D' h1)
    have ha : (D'.a : S) = (e0 * z : C) := by
      have h1 : D'.e (Additive.ofMul (e0 * z)) = (Torus.a : Torus (Type200.k m)) :=
        E'.symm_gen_one
      exact congrArg Subtype.val (StrothTypeData.a_eq_of_e_eq D' h1)
    have hb : (D'.b : S) = (f0 * w : C) := by
      have h1 : D'.e (Additive.ofMul (f0 * w)) = (Torus.b : Torus (Type200.k m)) :=
        E'.symm_gen_two
      exact congrArg Subtype.val (StrothTypeData.b_eq_of_e_eq D' h1)
    exact ⟨D', rfl, rfl, rfl, rfl, hc, ha, hb⟩
  · right
    let D' : StrothTypeData C (StrothTypeIndex.t201 m) :=
      strothTypeData_t201_of_generator_images D hBC hL E' h.uv h.t h.u h.ρ
    have hc : (D'.c : S) = D.c := by
      have h1 : D'.e (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) =
          (Torus.c : Torus (Type200.k m)) := E'.symm_gen_zero
      exact congrArg Subtype.val (StrothTypeData.c_eq_of_e_eq D' h1)
    have ha : (D'.a : S) = (e0 * z : C) := by
      have h1 : D'.e (Additive.ofMul (e0 * z)) = (Torus.a : Torus (Type200.k m)) :=
        E'.symm_gen_one
      exact congrArg Subtype.val (StrothTypeData.a_eq_of_e_eq D' h1)
    have hb : (D'.b : S) = (f0 * w : C) := by
      have h1 : D'.e (Additive.ofMul (f0 * w)) = (Torus.b : Torus (Type200.k m)) :=
        E'.symm_gen_two
      exact congrArg Subtype.val (StrothTypeData.b_eq_of_e_eq D' h1)
    exact ⟨D', rfl, rfl, rfl, rfl, hc, ha, hb⟩


theorem hasStrothType_t300_or_t310_of_data
    {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t300 (m + 1)) ∨
    HasStrothType C (StrothTypeIndex.t310 (m + 1)
      (two_le_succ_of_data hB.data hBC hC hrel hL hH hcS hne)) := by
  obtain ⟨d, hdC, hd2, h⟩ :=
    strothTypeData_t300_or_t310_of_data hB.data hBC hC hrel hL hH hcS hne
  rcases h with ⟨D', -⟩ | ⟨D', -⟩
  · exact Or.inl ⟨D'⟩
  · exact Or.inr ⟨D'⟩


theorem hasStrothType_t200_or_t201_of_data
    [Finite S] {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t200 m) ∨ HasStrothType C (StrothTypeIndex.t201 m) := by
  obtain ⟨e, f, he, hf, h⟩ :=
    strothTypeData_t200_or_t201_of_data hB.data hBC hC hrel hL hH hcS hne
  rcases h with ⟨D', -⟩ | ⟨D', -⟩
  · exact Or.inl ⟨D'⟩
  · exact Or.inr ⟨D'⟩


end CFSG.CGT.Stroth77
