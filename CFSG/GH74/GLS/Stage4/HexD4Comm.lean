module

public import CFSG.Timmesfeld.RankTwo.ModelD43

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section D4Gen

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem d4_comm_gen
    {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps) (s t : K) :
    ⁅𝕩 (d4Root a) s, 𝕩 (d4Root b) t⁆ = 𝕩 (d4Root g) ((C : K) * (s * t)) := by
  have hr : repCheck d4 a b [(1, 1, g, C)] = true := by
    have := d4PosReps_check
    simp only [repsCheck, List.all_eq_true] at this
    exact this _ h
  rw [commutator_xPar_of_repCheck hr]
  simp [mul_assoc]


variable (σ : K →+* K)

theorem twistSign_rel
    {a b g a' b' g' : ℕ} {C C' : ℤ}
    (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps) (h' : (a', b', [(1, 1, g', C')]) ∈ d4PosReps)
    (ha : rho (d4Root a) = d4Root a') (hb : rho (d4Root b) = d4Root b')
    (hg : rho (d4Root g) = d4Root g') (ha' : a < 24) (hb' : b < 24) (hg' : g < 24) (hg'' : g' < 24) :
    (C' : K) * (twistSign σ (d4Root a) * twistSign σ (d4Root b)) =
      C * twistSign σ (d4Root g) := by
  have e1 := congrArg (twistC .D4 K σ) (d4_comm_gen h (1 : K) 1)
  rw [map_commutatorElement, twistC_xPar σ (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root ha'),
    twistC_xPar σ (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root hb'),
    twistC_xPar σ (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root hg'), ha, hb, hg, map_one, mul_one, mul_one, mul_one,
    d4_comm_gen h'] at e1
  have e2 := xPar_injective (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root hg'') e1
  rw [map_mul, map_intCast, map_one] at e2
  linear_combination e2


theorem d4Root_zero_eq : d4Root 0 = Pi.single (nd 0) 1 := by
  funext k; fin_cases k <;> decide

theorem d4Root_one_eq : d4Root 1 = Pi.single (nd 1) 1 := by
  funext k; fin_cases k <;> decide

theorem d4Root_two_eq : d4Root 2 = Pi.single (nd 2) 1 := by
  funext k; fin_cases k <;> decide

theorem d4Root_three_eq : d4Root 3 = Pi.single (nd 3) 1 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_3' : rho (d4Root 3) = d4Root 0 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_9' : rho (d4Root 9) = d4Root 5 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_12' : rho (d4Root 12) = d4Root 15 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_2' : rho (d4Root 2) = d4Root 2 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_19' : rho (d4Root 19) = d4Root 19 := by
  funext k; fin_cases k <;> decide

theorem rho_d4Root_22' : rho (d4Root 22) = d4Root 22 := by
  funext k; fin_cases k <;> decide

theorem twistSign_R0 :
    twistSign σ (d4Root 0) = 1 := by
  rw [d4Root_zero_eq]; exact twistSign_single σ _

theorem twistSign_R1 :
    twistSign σ (d4Root 1) = 1 := by
  rw [d4Root_one_eq]; exact twistSign_single σ _

theorem twistSign_R2 :
    twistSign σ (d4Root 2) = 1 := by
  rw [d4Root_two_eq]; exact twistSign_single σ _

theorem twistSign_R3 :
    twistSign σ (d4Root 3) = 1 := by
  rw [d4Root_three_eq]; exact twistSign_single σ _

theorem twistSign_R5 :
    twistSign σ (d4Root 5) = 1 := by
  have h := twistSign_rel σ (K := K) (a := 0) (b := 2) (g := 5) (a' := 1) (b' := 2) (g' := 7)
    (C := -1) (C' := -1) (by decide) (by decide) rho_d4Root_0 rho_d4Root_2' rho_d4Root_5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R0, twistSign_R2] at h
  linear_combination h

theorem twistSign_R7 :
    twistSign σ (d4Root 7) = -1 := by
  have h := twistSign_rel σ (K := K) (a := 1) (b := 2) (g := 7) (a' := 3) (b' := 2) (g' := 9)
    (C := -1) (C' := 1) (by decide) (by decide) rho_d4Root_1 rho_d4Root_2' rho_d4Root_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R1, twistSign_R2] at h
  linear_combination h

theorem twistSign_R9 :
    twistSign σ (d4Root 9) = -1 := by
  have h := twistSign_rel σ (K := K) (a := 3) (b := 2) (g := 9) (a' := 0) (b' := 2) (g' := 5)
    (C := 1) (C' := -1) (by decide) (by decide) rho_d4Root_3' rho_d4Root_2' rho_d4Root_9'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R3, twistSign_R2] at h
  linear_combination -h

variable (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem twistSign_R22 :
    twistSign σ (d4Root 22) = 1 :=
  twistSign_of_rho_eq σ hσ (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root (by decide)) rho_d4Root_22'

include hσ in
theorem twistSign_R15 :
    twistSign σ (d4Root 15) = 1 := by
  have h := twistSign_rel σ (K := K) (a := 5) (b := 15) (g := 22) (a' := 7) (b' := 13) (g' := 22)
    (C := 1) (C' := 1) (by decide) (by decide) rho_d4Root_5 rho_d4Root_15 rho_d4Root_22'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R5, twistSign_R22 σ hσ] at h
  linear_combination h

include hσ in
theorem twistSign_R13 :
    twistSign σ (d4Root 13) = 1 := by
  have h := twistSign_rel σ (K := K) (a := 7) (b := 13) (g := 22) (a' := 9) (b' := 12) (g' := 22)
    (C := 1) (C' := -1) (by decide) (by decide) rho_d4Root_7 rho_d4Root_13 rho_d4Root_22'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R7, twistSign_R22 σ hσ] at h
  linear_combination h

include hσ in
theorem twistSign_R12 :
    twistSign σ (d4Root 12) = 1 := by
  have h := twistSign_rel σ (K := K) (a := 9) (b := 12) (g := 22) (a' := 5) (b' := 15) (g' := 22)
    (C := -1) (C' := 1) (by decide) (by decide) rho_d4Root_9' rho_d4Root_12' rho_d4Root_22'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [twistSign_R9, twistSign_R22 σ hσ] at h
  linear_combination -h


theorem xOrbit_R0
    (c : K) : xOrbit σ (d4Root 0) c =
    𝕩 (d4Root 0) c * 𝕩 (d4Root 1) (σ c) * 𝕩 (d4Root 3) (σ (σ c)) := by
  rw [xOrbit, rho_d4Root_0, rho_d4Root_1, twistSign_R0, twistSign_R1, one_mul, one_mul, one_mul]

theorem xOrbit_R5
    (c : K) : xOrbit σ (d4Root 5) c =
    𝕩 (d4Root 5) c * 𝕩 (d4Root 7) (σ c) * 𝕩 (d4Root 9) (-σ (σ c)) := by
  rw [xOrbit, rho_d4Root_5, rho_d4Root_7, twistSign_R5, twistSign_R7 σ]
  simp

include hσ in
theorem xOrbit_R15
    (c : K) : xOrbit σ (d4Root 15) c =
    𝕩 (d4Root 15) c * 𝕩 (d4Root 13) (σ c) * 𝕩 (d4Root 12) (σ (σ c)) := by
  rw [xOrbit, rho_d4Root_15, rho_d4Root_13, twistSign_R15 σ hσ, twistSign_R13 σ hσ]
  simp


theorem d4_comm_symm_gen
    {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps) (s t : K) :
    ⁅𝕩 (d4Root b) t, 𝕩 (d4Root a) s⁆ = 𝕩 (d4Root g) (-((C : K) * (s * t))) := by
  rw [← commutatorElement_inv, d4_comm_gen h, xPar_neg]

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

include hσ in
theorem d4g_comm02
    (s t : K) :
    ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 15) t⁆ = 𝕩 (d4Root 19) (d43Tr hσ (s * t) : K) := by
  have c1 := d4_comm_one (K := K) (a := 3) (b := 15) (by decide +kernel)
  have c2 := d4_comm_one (K := K) (a := 3) (b := 13) (by decide +kernel)
  have c3 := d4_comm_gen (K := K) (a := 3) (b := 12) (g := 19) (C := 1) (by decide)
  have c4 := d4_comm_one (K := K) (a := 1) (b := 15) (by decide +kernel)
  have c5 := d4_comm_gen (K := K) (a := 1) (b := 13) (g := 19) (C := 1) (by decide)
  have c6 := d4_comm_one (K := K) (a := 1) (b := 12) (by decide +kernel)
  have c7 := d4_comm_gen (K := K) (a := 0) (b := 15) (g := 19) (C := 1) (by decide)
  have c8 := d4_comm_one (K := K) (a := 0) (b := 13) (by decide +kernel)
  have c9 := d4_comm_one (K := K) (a := 0) (b := 12) (by decide +kernel)
  rw [xOrbit_R0 σ, xOrbit_R15 σ hσ, commutator_mul3_mul3 (𝕏 (d4Root 19))
    (commute4_of_mem (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ _ _)]
  · simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, one_mul, mul_one, ← xPar_add, Int.cast_one]
    congr 1
    simp only [coe_d43Tr, map_mul]
    ring
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9] <;>
      first | exact one_mem _ | exact xPar_mem (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root (by decide)) _


include hσ in
theorem d4g_comm24
    (s t : K) :
    ⁅xOrbit σ (d4Root 15) s, xOrbit σ (d4Root 5) t⁆ =
      𝕩 (d4Root 22) (-(d43Tr hσ (s * t) : K)) := by
  have c1 := d4_comm_one (K := K) (a := 12) (b := 5) (by decide +kernel)
  have c2 := d4_comm_one (K := K) (a := 12) (b := 7) (by decide +kernel)
  have c3 := d4_comm_symm_gen (K := K) (a := 9) (b := 12) (g := 22) (C := -1) (by decide)
  have c4 := d4_comm_one (K := K) (a := 13) (b := 5) (by decide +kernel)
  have c5 := d4_comm_symm_gen (K := K) (a := 7) (b := 13) (g := 22) (C := 1) (by decide)
  have c6 := d4_comm_one (K := K) (a := 13) (b := 9) (by decide +kernel)
  have c7 := d4_comm_symm_gen (K := K) (a := 5) (b := 15) (g := 22) (C := 1) (by decide)
  have c8 := d4_comm_one (K := K) (a := 15) (b := 7) (by decide +kernel)
  have c9 := d4_comm_one (K := K) (a := 15) (b := 9) (by decide +kernel)
  rw [xOrbit_R15 σ hσ, xOrbit_R5 σ, commutator_mul3_mul3 (𝕏 (d4Root 22))
    (commute4_of_mem (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ _ _)]
  · simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, one_mul, mul_one, ← xPar_add, Int.cast_one,
      Int.cast_neg]
    congr 1
    simp only [coe_d43Tr, map_mul]
    ring
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9] <;>
      first | exact one_mem _ | exact xPar_mem (CFSG.LieType.Steinberg.TwistedD4.isRoot_d4Root (by decide)) _

theorem d4g_comm15
    (s t : fixedField σ) :
    ⁅𝕩 (d4Root 19) (s : K), 𝕩 (d4Root 2) (t : K)⁆ =
      𝕩 (d4Root 22) ((-(s * t) : fixedField σ) : K) := by
  rw [d4_comm_gen (a := 19) (b := 2) (g := 22) (C := -1) (by decide)]
  simp


theorem d4g_commute01
    (s t : K) : Commute (xOrbit σ (d4Root 0) s) (𝕩 (d4Root 19) t) := by
  rw [xOrbit_R0 σ]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d4g_commute03
    (s t : K) : Commute (xOrbit σ (d4Root 0) s) (𝕩 (d4Root 22) t) := by
  rw [xOrbit_R0 σ]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

include hσ in
theorem d4g_commute12
    (s t : K) : Commute (𝕩 (d4Root 19) s) (xOrbit σ (d4Root 15) t) := by
  rw [xOrbit_R15 σ hσ]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

theorem d4g_commute13
    (s t : K) : Commute (𝕩 (d4Root 19) s) (𝕩 (d4Root 22) t) :=
  d4_commute (by decide +kernel) _ _

theorem d4g_commute14
    (s t : K) : Commute (𝕩 (d4Root 19) s) (xOrbit σ (d4Root 5) t) := by
  rw [xOrbit_R5 σ]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

include hσ in
theorem d4g_commute23
    (s t : K) : Commute (xOrbit σ (d4Root 15) s) (𝕩 (d4Root 22) t) := by
  rw [xOrbit_R15 σ hσ]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

include hσ in
theorem d4g_commute25
    (s t : K) : Commute (xOrbit σ (d4Root 15) s) (𝕩 (d4Root 2) t) := by
  rw [xOrbit_R15 σ hσ]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d4g_commute34
    (s t : K) : Commute (𝕩 (d4Root 22) s) (xOrbit σ (d4Root 5) t) := by
  rw [xOrbit_R5 σ]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

theorem d4g_commute35
    (s t : K) : Commute (𝕩 (d4Root 22) s) (𝕩 (d4Root 2) t) :=
  d4_commute (by decide +kernel) _ _

theorem d4g_commute45
    (s t : K) : Commute (xOrbit σ (d4Root 5) s) (𝕩 (d4Root 2) t) := by
  rw [xOrbit_R5 σ]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)


theorem d4_conj_gen
    {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps) (s t : K) :
    MulAut.conj (𝕩 (d4Root a) s) (𝕩 (d4Root b) t) =
      𝕩 (d4Root g) ((C : K) * (s * t)) * 𝕩 (d4Root b) t := by
  rw [_root_.conj_eq_commutatorElement_mul, d4_comm_gen h]

include hσ in
theorem d4g_comm05
    (s u : K) (hu : σ u = u) :
    ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 2) u⁆ =
      𝕩 (d4Root 19) (-(u * (s * σ s * σ (σ s)))) *
        xOrbit σ (d4Root 15) (-(u * (σ s * σ (σ s)))) *
        𝕩 (d4Root 22) (u ^ 2 * (s * σ s * σ (σ s))) * xOrbit σ (d4Root 5) (-(u * s)) := by
  have k1 := d4_conj_gen (K := K) (a := 3) (b := 2) (g := 9) (C := 1) (by decide)
  have k2 := d4_conj_gen (K := K) (a := 1) (b := 9) (g := 15) (C := -1) (by decide)
  have k3 := d4_conj_gen (K := K) (a := 1) (b := 2) (g := 7) (C := -1) (by decide)
  have k4 := d4_conj_gen (K := K) (a := 0) (b := 15) (g := 19) (C := 1) (by decide)
  have k5 := d4_conj_gen (K := K) (a := 0) (b := 9) (g := 13) (C := -1) (by decide)
  have k6 := d4_conj_gen (K := K) (a := 0) (b := 7) (g := 12) (C := 1) (by decide)
  have k7 := d4_conj_gen (K := K) (a := 0) (b := 2) (g := 5) (C := -1) (by decide)
  have hsw : ∀ a b : K, 𝕩 (d4Root 9) a * 𝕩 (d4Root 12) b =
      𝕩 (d4Root 22) (-(a * b)) * 𝕩 (d4Root 12) b * 𝕩 (d4Root 9) a := fun a b => by
    rw [mul_eq_commutatorElement_mul, d4_comm_gen (a := 9) (b := 12) (g := 22) (C := -1)
      (by decide)]
    simp
  calc ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 2) u⁆ =
      𝕩 (d4Root 19) (-(s * (σ s * (σ (σ s) * u)))) * 𝕩 (d4Root 15) (-(σ s * (σ (σ s) * u))) *
        𝕩 (d4Root 13) (-(s * (σ (σ s) * u))) * (𝕩 (d4Root 9) (σ (σ s) * u) *
          𝕩 (d4Root 12) (-(s * (σ s * u)))) * 𝕩 (d4Root 7) (-(σ s * u)) *
            𝕩 (d4Root 5) (-(s * u)) := by
        rw [commutatorElement_eq_conj_mul_inv, xOrbit_R0 σ]
        simp only [map_mul, MulAut.mul_apply, k1, k2, k3, k4, k5, k6, k7, Int.cast_one,
          Int.cast_neg, one_mul, neg_mul, mul_neg]
        group
    _ = 𝕩 (d4Root 19) (-(s * (σ s * (σ (σ s) * u)))) * 𝕩 (d4Root 15) (-(σ s * (σ (σ s) * u))) *
        𝕩 (d4Root 13) (-(s * (σ (σ s) * u))) *
          (𝕩 (d4Root 22) (-(σ (σ s) * u * -(s * (σ s * u)))) *
            𝕩 (d4Root 12) (-(s * (σ s * u))) * 𝕩 (d4Root 9) (σ (σ s) * u)) *
              𝕩 (d4Root 7) (-(σ s * u)) * 𝕩 (d4Root 5) (-(s * u)) := by rw [hsw]
    _ = 𝕩 (d4Root 19) (-(s * (σ s * (σ (σ s) * u)))) * 𝕩 (d4Root 15) (-(σ s * (σ (σ s) * u))) *
        𝕩 (d4Root 13) (-(s * (σ (σ s) * u))) * 𝕩 (d4Root 12) (-(s * (σ s * u))) *
          𝕩 (d4Root 22) (-(σ (σ s) * u * -(s * (σ s * u)))) *
            (𝕩 (d4Root 5) (-(s * u)) * 𝕩 (d4Root 7) (-(σ s * u)) * 𝕩 (d4Root 9) (σ (σ s) * u)) :=
        mul_rearrange8 (d4_commute (by decide +kernel) _ _) (d4_commute (by decide +kernel) _ _)
          (d4_commute (by decide +kernel) _ _) (d4_commute (by decide +kernel) _ _)
    _ = _ := by
        rw [xOrbit_R15 σ hσ, xOrbit_R5 σ]
        simp only [map_mul, map_neg, hσ, hu, mul_assoc]
        have e19 : -(u * (s * (σ s * σ (σ s)))) = -(s * (σ s * (σ (σ s) * u))) := by ring
        have e15 : -(u * (σ s * σ (σ s))) = -(σ s * (σ (σ s) * u)) := by ring
        have e13 : -(u * (σ (σ s) * s)) = -(s * (σ (σ s) * u)) := by ring
        have e12 : -(u * (s * σ s)) = -(s * (σ s * u)) := by ring
        have e22 : u ^ 2 * (s * (σ s * σ (σ s))) = -(σ (σ s) * (u * -(s * (σ s * u)))) := by ring
        have e5 : -(u * s) = -(s * u) := by ring
        have e7 : -(u * σ s) = -(σ s * u) := by ring
        have e9 : - -(u * σ (σ s)) = σ (σ s) * u := by ring
        rw [e19, e15, e13, e12, e22, e5, e7, e9]


local notation "𝕪" => fun (i : Fin 5) => 𝕩 (d4Root (![19, 15, 13, 12, 22] i))

include hσ in
theorem d4g_comm04
    (s t : K) :
    ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 5) t⁆ =
      𝕩 (d4Root 19) (d43Tr hσ (d43Sharp σ s * t) : K) * xOrbit σ (d4Root 15) (d43Cross σ s t) *
        𝕩 (d4Root 22) (d43Tr hσ (s * d43Sharp σ t) : K) := by
  have hA0 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 5) c⁆ =
      𝕩 (d4Root 19) (σ s * (σ (σ s) * c)) * 𝕩 (d4Root 13) (σ (σ s) * c) *
        𝕩 (d4Root 12) (σ s * c) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_R0 σ]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj_gen (K := K) (a := 3) (b := 5) (g := 13) (C := 1) (by decide),
      d4_conj_gen (K := K) (a := 1) (b := 13) (g := 19) (C := 1) (by decide),
      d4_conj_gen (K := K) (a := 1) (b := 5) (g := 12) (C := 1) (by decide),
      d4_conj_of_commute (K := K) (a := 0) (b := 19) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 13) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 12) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 5) (by decide +kernel), Int.cast_one, one_mul]
    group
  have hA1 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 7) c⁆ = 𝕩 (d4Root 19) (s * (σ (σ s) * c)) *
      𝕩 (d4Root 15) (σ (σ s) * c) * 𝕩 (d4Root 12) (s * c) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_R0 σ]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj_gen (K := K) (a := 3) (b := 7) (g := 15) (C := 1) (by decide),
      d4_conj_of_commute (K := K) (a := 1) (b := 15) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 1) (b := 7) (by decide +kernel),
      d4_conj_gen (K := K) (a := 0) (b := 15) (g := 19) (C := 1) (by decide),
      d4_conj_gen (K := K) (a := 0) (b := 7) (g := 12) (C := 1) (by decide), Int.cast_one, one_mul]
    group
  have hA3 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 9) c⁆ =
      𝕩 (d4Root 19) (-(s * (σ s * c))) * 𝕩 (d4Root 15) (-(σ s * c)) *
        𝕩 (d4Root 13) (-(s * c)) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_R0 σ]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj_of_commute (K := K) (a := 3) (b := 9) (by decide +kernel),
      d4_conj_gen (K := K) (a := 1) (b := 9) (g := 15) (C := -1) (by decide),
      d4_conj_gen (K := K) (a := 0) (b := 15) (g := 19) (C := 1) (by decide),
      d4_conj_gen (K := K) (a := 0) (b := 9) (g := 13) (C := -1) (by decide), Int.cast_one,
      Int.cast_neg, one_mul, neg_mul, mul_neg]
    group
  have hP : ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 5) t⁆ =
      ([(0, σ s * (σ (σ s) * t)), (2, σ (σ s) * t), (3, σ s * t),
        (0, s * (σ (σ s) * σ t)), (4, t * (σ (σ s) * σ t)), (1, σ (σ s) * σ t), (3, s * σ t),
        (0, s * (σ s * σ (σ t))), (4, t * (σ s * σ (σ t))), (1, σ s * σ (σ t)),
        (4, σ t * (s * σ (σ t))), (2, s * σ (σ t))].map fun p : Fin 5 × K => 𝕪 p.1 p.2).prod := by
    rw [xOrbit_R5 σ, mul_assoc, commutatorElement_mul_right_conj,
      commutatorElement_mul_right_conj, hA0, hA1, hA3]
    simp only [map_mul,
      d4_conj_of_commute (K := K) (a := 7) (b := 19) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 7) (b := 15) (by decide +kernel),
      d4_conj_gen (K := K) (a := 7) (b := 13) (g := 22) (C := 1) (by decide),
      d4_conj_of_commute (K := K) (a := 5) (b := 19) (by decide +kernel),
      d4_conj_gen (K := K) (a := 5) (b := 15) (g := 22) (C := 1) (by decide),
      d4_conj_of_commute (K := K) (a := 5) (b := 12) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 5) (b := 22) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 5) (b := 13) (by decide +kernel),
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Int.cast_one, one_mul,
      neg_neg, mul_neg]
    simp only [Matrix.cons_val, mul_assoc]
  have hQ : 𝕩 (d4Root 19) (d43Tr hσ (d43Sharp σ s * t) : K) *
      xOrbit σ (d4Root 15) (d43Cross σ s t) * 𝕩 (d4Root 22) (d43Tr hσ (s * d43Sharp σ t) : K) =
      ([(0, (d43Tr hσ (d43Sharp σ s * t) : K)), (1, d43Cross σ s t),
        (2, σ (d43Cross σ s t)), (3, σ (σ (d43Cross σ s t))),
        (4, (d43Tr hσ (s * d43Sharp σ t) : K))].map fun p : Fin 5 × K => 𝕪 p.1 p.2).prod := by
    rw [xOrbit_R15 σ hσ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val, mul_assoc]
  rw [hP, hQ]
  refine prod_map_eq_of_sum_eq _ (fun i a b => xPar_add _ a b)
    (fun i j hij a b => d4_commute (d4_commute_five i j hij) a b) ?_
  funext j
  fin_cases j <;>
    simp [coe_d43Tr, d43Sharp, d43Cross, map_mul, map_add, hσ] <;> ring

end D4Gen

end CFSG.GH74.GLS.Stage4.Hex
