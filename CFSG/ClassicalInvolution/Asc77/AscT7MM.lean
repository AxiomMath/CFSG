module

public import CFSG.ClassicalInvolution.Asc77.AscT7ML
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X
import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ClassicalInvolution.Asc77.AscT7MJ
public import CFSG.ClassicalInvolution.Asc77.AscT7MK

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

set_option linter.unusedSectionVars false

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane
  CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.Assembly.Dichotomy
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem centre_trivial : ∀ p : projectiveSL 4 F, (∀ q, p * q = q * p) → p = 1 := by
  intro p hp
  have : p ∈ Subgroup.center (projectiveSL 4 F) :=
    Subgroup.mem_center_iff.mpr fun q => (hp q).symm
  rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at this
  exact Subgroup.mem_bot.mp this

theorem proj_zneg : proj 4 F (zneg F) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj, scalars_eq_center]
  exact zneg_mem_center

theorem proj_x0_mem_lay {j : Fin 4} (hj : j = 0 ∨ j = 1) : proj 4 F (x0 F) ∈ lay F j := by
  refine ⟨zneg F * x0 F, ?_, ?_⟩
  · show zneg F * x0 F ∈ coordBlockSL F (Jc j)
    rw [mem_coordBlockSL_iff]
    intro i k hik
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_zneg, coe_x0]
    have hi : i ∉ Jc j → (i = 0 ∨ i = 1) := by
      intro h
      have : i = j := by simpa [mem_Jc] using h
      rcases hj with rfl | rfl <;> simp_all
    have hk : k ∉ Jc j → (k = 0 ∨ k = 1) := by
      intro h
      have : k = j := by simpa [mem_Jc] using h
      rcases hj with rfl | rfl <;> simp_all
    rcases hik with h | h
    · rcases hi h with rfl | rfl <;> fin_cases k <;> simp
    · rcases hk h with rfl | rfl <;> fin_cases i <;> simp
  · rw [map_mul, proj_zneg, one_mul]

theorem dGL_mul_self (j : Fin 4) : (dGL j : GL (Fin 4) F) * dGL j = 1 :=
  Units.ext (dMat_mul_self j)

theorem toGL_x0_comm_dGL (j : Fin 4) :
    Matrix.SpecialLinearGroup.toGL (x0 F) * dGL j =
      dGL j * Matrix.SpecialLinearGroup.toGL (x0 F) := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_dGL, coe_x0]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dMat, sgn, Matrix.mul_apply, Fin.sum_univ_four] <;>
    split_ifs <;> simp

theorem toGL_x0_mul_dGL_one :
    Matrix.SpecialLinearGroup.toGL (x0 F) * dGL 1 = dGL 0 := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_dGL, coe_x0]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dMat, sgn, Matrix.mul_apply, Fin.sum_univ_four]

theorem not_scalar_dGL (h2 : (2 : F) ≠ 0) (j : Fin 4) :
    ¬ ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 4) c = dGL j := by
  rintro ⟨c, hc⟩
  obtain ⟨a, b, hab, haj, hbj⟩ := exists_two_ne j
  have h1 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) a a) hc
  have h2' := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) j j) hc
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    coe_dGL, dMat, sgn, haj, ite_true, ite_false] at h1 h2'
  apply h2
  linear_combination h2' - h1

theorem not_scalar_toGL_x0 (h2 : (2 : F) ≠ 0) :
    ¬ ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 4) c = Matrix.SpecialLinearGroup.toGL (x0 F) := by
  rintro ⟨c, hc⟩
  have h1 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) hc
  have h2' := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 2 2) hc
  have e1 : (c : F) = -1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_x0]
      using h1
  have e2 : (c : F) = 1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_x0]
      using h2'
  apply h2
  linear_combination e1 - e2

section Diag

variable [Finite F] {X : Type} [Group X] [Finite X] {θ : X →* MulAut (projectiveSL 4 F)}
  {ι : projectiveSL 4 F →* X}

theorem θ_z (hι : ∀ p, θ (ι p) = MulAut.conj p) :
    θ (ι (proj 4 F (x0 F))) = conjAut 4 F (Matrix.SpecialLinearGroup.toGL (x0 F)) := by
  rw [hι, ← OuterL4.conjAut_toGL]

theorem θ_zy (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    θ (ι (proj 4 F (x0 F)) * y) = conjAut 4 F (dGL 0) := by
  rw [map_mul, θ_z hι, hy, ← map_mul, toGL_x0_mul_dGL_one]

theorem z_mul_self : ι (proj 4 F (x0 F)) * ι (proj 4 F (x0 F)) = 1 := by
  rw [← map_mul, ← map_mul, x0_mul_self, map_one, map_one]

theorem y_mul_self (hθ : Function.Injective θ) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    y * y = 1 := by
  apply hθ
  rw [map_mul, hy, ← map_mul, dGL_mul_self, map_one, map_one]

theorem z_mul_y_comm (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X}
    (hy : θ y = conjAut 4 F (dGL 1)) :
    ι (proj 4 F (x0 F)) * y = y * ι (proj 4 F (x0 F)) := by
  apply hθ
  rw [map_mul, map_mul, θ_z hι, hy, ← map_mul, ← map_mul, toGL_x0_comm_dGL]

theorem z_ne_one (h2 : (2 : F) ≠ 0) (hι : ∀ p, θ (ι p) = MulAut.conj p) :
    ι (proj 4 F (x0 F)) ≠ 1 := by
  intro h
  have h1 : conjAut 4 F (Matrix.SpecialLinearGroup.toGL (x0 F)) = 1 := by
    rw [← θ_z hι, h, map_one]
  exact not_scalar_toGL_x0 h2
    ((CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h1)

theorem y_ne_one (h2 : (2 : F) ≠ 0) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) : y ≠ 1 := by
  intro h
  have h1 : conjAut 4 F (dGL 1) = 1 := by rw [← hy, h, map_one]
  exact not_scalar_dGL h2 1
    ((CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h1)

theorem zy_ne_one (h2 : (2 : F) ≠ 0) (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X}
    (hy : θ y = conjAut 4 F (dGL 1)) : ι (proj 4 F (x0 F)) * y ≠ 1 := by
  intro h
  have h1 : conjAut 4 F (dGL 0) = 1 := by rw [← θ_zy hι hy, h, map_one]
  exact not_scalar_dGL h2 0
    ((CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h1)

theorem layerData_y (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    LayerData ι.range (Subgroup.closure ({ι (proj 4 F (x0 F)), y} : Set X)) y
      ((lay F 1).map ι) := by
  refine layerData_of_fix hθ hι centre_trivial (a := y) (Q := lay F 1) ?_ ?_ (lay_perf h4 1)
    (lay_gen h4 1) ?_
  · intro q hq
    rw [hy]
    exact lay_fix 1 q hq
  · intro g hg q hq
    rw [hy] at hg
    exact lay_norm h2 1 g hg q hq
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem ι (proj_x0_mem_lay (Or.inr rfl)))
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

theorem layerData_zy (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    LayerData ι.range (Subgroup.closure ({ι (proj 4 F (x0 F)), y} : Set X))
      (ι (proj 4 F (x0 F)) * y) ((lay F 0).map ι) := by
  have hθzy := θ_zy hι hy
  have hzmem : ι (proj 4 F (x0 F)) ∈ (lay F 0).map ι :=
    Subgroup.mem_map_of_mem ι (proj_x0_mem_lay (Or.inl rfl))
  refine layerData_of_fix hθ hι centre_trivial (a := ι (proj 4 F (x0 F)) * y) (Q := lay F 0) ?_ ?_
    (lay_perf h4 0) (lay_gen h4 0) ?_
  · intro q hq
    rw [hθzy]
    exact lay_fix 0 q hq
  · intro g hg q hq
    rw [hθzy] at hg
    exact lay_norm h2 0 g hg q hq
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_right hzmem
    · have hyz : ι (proj 4 F (x0 F)) * (ι (proj 4 F (x0 F)) * y) = y := by
        rw [← mul_assoc, z_mul_self, one_mul]
      have hmem := Subgroup.mul_mem (Subgroup.zpowers (ι (proj 4 F (x0 F)) * y) ⊔
        (lay F 0).map ι) (Subgroup.mem_sup_right hzmem)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers (ι (proj 4 F (x0 F)) * y)))
      rw [hyz] at hmem
      rw [hg]
      exact hmem

theorem layerData_z (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) :
    LayerData ι.range ⊥ (ι (proj 4 F (x0 F)))
      (((R0 F ⊔ R0' F).map (proj 4 F)).map ι) := by
  set e : SL(4, F) →* X := ι.comp (proj 4 F) with he
  have hι' := ι_injective hι centre_trivial
  have hker : e.ker ≤ Subgroup.center SL(4, F) := by
    intro s hs
    have h1 : ι (proj 4 F s) = 1 := hs
    have h2' : proj 4 F s = 1 := hι' (h1.trans (map_one ι).symm)
    rw [← scalars_eq_center, ← ker_proj]
    exact h2'
  have hSL := slayer_x0 h2 h4
  have h := layerData_of_hom e hker (a₀ := x0 F) (Q := R0 F ⊔ R0' F) ⊥ hSL.comm
    (fun g hg p hp => hSL.norm g (hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg, mul_inv_cancel])) p hp)
    hSL.perf hSL.gen (by simp)
  have hrange : e.range = ι.range := by
    rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (proj_surjective 4 F),
      ← MonoidHom.range_eq_map]
  have hmap : (R0 F ⊔ R0' F).map e = ((R0 F ⊔ R0' F).map (proj 4 F)).map ι := by
    rw [he, Subgroup.map_map]
  rw [hrange, hmap] at h
  exact h

theorem hN_diag (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    ∀ n ∈ involutionOddCore (ι (proj 4 F (x0 F))), n * y = y * n := by
  intro n hn
  have : ι.range.Normal := range_normal hθ hι
  have hLz := layerData_z h2 h4 hι
  have hι' := ι_injective hι centre_trivial
  have hfix : ∀ r ∈ R0 F ⊔ R0' F, θ n (proj 4 F r) = proj 4 F r := by
    intro r hr
    have := hLz.commutes_of_oddCore hn (p := ι (proj 4 F r)) ⟨proj 4 F r, ⟨r, hr, rfl⟩, rfl⟩
    exact (ι_commute_iff hθ hι hι' n _).mp this
  have hfix0 : ∀ r ∈ R0 F, θ n (proj 4 F r) = proj 4 F r :=
    fun r hr => hfix r (Subgroup.mem_sup_left hr)
  have hfix2 : ∀ r ∈ R0' F, θ n (proj 4 F r) = proj 4 F r :=
    fun r hr => hfix r (Subgroup.mem_sup_right hr)
  have hodd : Odd (orderOf n) :=
    Odd.of_dvd_nat (odd_natCard_involutionOddCore _) (Subgroup.orderOf_dvd_natCard _ hn)
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hφ⟩ := hform (θ n)
  interval_cases ε
  · rw [pow_zero, mul_one] at hφ
    have hfa : ∀ r ∈ R0 F,
        (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r := fun r hr => by
      rw [← hφ]
      exact hfix0 r hr
    have hfa' : ∀ r ∈ R0' F,
        (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r := fun r hr => by
      rw [← hφ]
      exact hfix2 r hr
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := OuterL4.aut_fix_blocks_zero h2 A σ hfa hfa'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hφ
    apply hθ
    rw [map_mul, map_mul, hy, hφ, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    simp only [Units.val_mul, hM, coe_dGL]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [dMat, sgn, Matrix.mul_apply, Fin.sum_univ_four]
  · rw [pow_one] at hφ
    have hfa : ∀ r ∈ R0 F,
        (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r :=
      fun r hr => by
        rw [← hφ]
        exact hfix0 r hr
    have hfa' : ∀ r ∈ R0' F,
        (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r :=
      fun r hr => by
        rw [← hφ]
        exact hfix2 r hr
    obtain ⟨hσ, m, k', hm, hk, hM⟩ := OuterL4.aut_fix_blocks_one h2 A σ hfa hfa'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hφ
    have hnn : θ n * θ n = 1 := by
      rw [hφ]
      exact OuterL4.sq_of_antidiag A m k' hm hk hM
    have hord : orderOf (θ n) ∣ orderOf n := orderOf_map_dvd θ n
    have hodd' : Odd (orderOf (θ n)) := Odd.of_dvd_nat hodd hord
    have hdvd2 : orderOf (θ n) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
    have hle := Nat.le_of_dvd (by norm_num) hdvd2
    have h1' : orderOf (θ n) = 1 := by
      obtain ⟨t, ht⟩ := hodd'
      omega
    have hθn : θ n = 1 := orderOf_eq_one_iff.mp h1'
    have hn1 : n = 1 := hθ (hθn.trans (map_one θ).symm)
    rw [hn1, one_mul, mul_one]

theorem alphaOf_klein_diag (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hθ : Function.Injective θ)
    (hι : ∀ p, θ (ι p) = MulAut.conj p) {y : X} (hy : θ y = conjAut 4 F (dGL 1)) :
    alphaOf (Subgroup.closure ({ι (proj 4 F (x0 F)), y} : Set X)) = ⊥ := by
  have : ι.range.Normal := range_normal hθ hι
  refine alphaOf_klein_outer ι.range z_mul_self (y_mul_self hθ hy) (z_mul_y_comm hθ hι hy)
    (z_ne_one h2 hι) (y_ne_one h2 hy) (zy_ne_one h2 hι hy) (layerData_y h2 h4 hθ hι hy)
    (layerData_zy h2 h4 hθ hι hy) (hN_diag h2 h4 hθ hι hy) ?_
  intro x _ h₁ h₂
  exact eq_one_of_fix_of_sup_eq_top hθ hι centre_trivial (Q₁ := lay F 1) (Q₂ := lay F 0)
    (by rw [sup_comm]; exact lay_sup) h₁ h₂

end Diag

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4
