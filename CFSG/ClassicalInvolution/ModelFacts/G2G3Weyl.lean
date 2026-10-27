module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusFive

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section SL2

variable {F : Type} [Field F]

theorem WSL_eq_vSL_uSL_vSL : (WSL : SL2 F) = vSL (-1) * uSL 1 * vSL (-1) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem glConjSL_antiGL_neg_one_WSL : glConjSL (antiGL (-1 : Fˣ)) (WSL : SL2 F) = WSL := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [glConjSL_coe, antiGL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Sign

variable {F : Type} [Field F]


theorem e0_sign (hK2 : ringChar F ≠ 2) :
    ∃ η : F, η * η = 1 ∧
      (∀ c : F, (g2ChartA F WSL * g2ChartB F WSL) * rootChart Tag.G2 F 1 g2i0 (uSL c) *
        (g2ChartA F WSL * g2ChartB F WSL)⁻¹ = rootChart Tag.G2 F 1 g2i0 (vSL (η * c))) ∧
      (∀ c : F, (g2ChartA F WSL * g2ChartB F WSL) * rootChart Tag.G2 F 1 g2i0 (vSL c) *
        (g2ChartA F WSL * g2ChartB F WSL)⁻¹ = rootChart Tag.G2 F 1 g2i0 (uSL (η * c))) := by
  obtain ⟨η, η', hη, hη', hu, hv⟩ := m0_conj_chart (F := F) 1 g2i0
  have hinj := rootChart_injective hK2 (τ := Tag.G2) (K := F) 1 g2i0
  set m : ModGL Tag.G2 F := g2ChartA F WSL * g2ChartB F WSL with hm
  set Φ : SL2 F →* ModGL Tag.G2 F := rootChart Tag.G2 F 1 g2i0 with hΦ
  have hu1 : m * Φ (uSL 1) * m⁻¹ = Φ (vSL η) := by rw [hu, mul_one]
  have hv1 : m * Φ (vSL (-1)) * m⁻¹ = Φ (uSL (-η')) := by rw [hv, mul_neg_one]
  have hv2 : m * Φ (vSL (-1)) * m⁻¹ = Φ (uSL (-η')) := hv1
  have h1 : m * Φ WSL * m⁻¹ = Φ (vSL η * uSL (-η') * vSL η) := by
    have e : m * Φ (uSL 1 * vSL (-1) * uSL 1) * m⁻¹ =
        (m * Φ (uSL 1) * m⁻¹) * (m * Φ (vSL (-1)) * m⁻¹) * (m * Φ (uSL 1) * m⁻¹) := by
      simp only [map_mul]; group
    have e' : m * Φ (uSL 1 * vSL (-1) * uSL 1) * m⁻¹ = Φ (vSL η * uSL (-η') * vSL η) := by
      rw [e, hu1, hv1, ← map_mul, ← map_mul]
    rwa [← WSL_eq_uSL_vSL_uSL] at e'
  have hu1' : m * Φ (uSL 1) * m⁻¹ = Φ (vSL η) := hu1
  have hv1' : m * Φ (vSL (-1)) * m⁻¹ = Φ (uSL (-η')) := hv1
  have h2 : m * Φ WSL * m⁻¹ = Φ (uSL (-η') * vSL η * uSL (-η')) := by
    have e : m * Φ (vSL (-1) * uSL 1 * vSL (-1)) * m⁻¹ =
        (m * Φ (vSL (-1)) * m⁻¹) * (m * Φ (uSL 1) * m⁻¹) * (m * Φ (vSL (-1)) * m⁻¹) := by
      simp only [map_mul]; group
    have e' : m * Φ (vSL (-1) * uSL 1 * vSL (-1)) * m⁻¹ =
        Φ (uSL (-η') * vSL η * uSL (-η')) := by
      rw [e, hu1', hv1', ← map_mul, ← map_mul]
    rwa [← WSL_eq_vSL_uSL_vSL] at e'
  have hmat : vSL η * uSL (-η') * vSL η = uSL (-η') * vSL η * uSL (-η') :=
    hinj (h1.symm.trans h2)
  have e01 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hmat
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_uSL,
    coe_vSL] at e01
  have hηη : η = η' := by
    rcases e01 with h | h
    · linear_combination (-η') * h + (-η) * hη'
    · exfalso
      rw [h, mul_zero] at hη'
      exact zero_ne_one hη'
  refine ⟨η, hη, fun c => hu c, fun c => ?_⟩
  rw [hv c, hηη]

theorem exists_sign_comm_e0 (hK2 : ringChar F ≠ 2) :
    ∃ η : F, η * η = 1 ∧ ∀ b : Fin Tag.G2.rank → Fˣ, ((b g2i0 : Fˣ) : F) * η = -1 →
      (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) *
          rootChart Tag.G2 F 1 g2i0 WSL =
        rootChart Tag.G2 F 1 g2i0 WSL *
          (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) := by
  obtain ⟨η, hη, hu, hv⟩ := e0_sign (F := F) hK2
  refine ⟨η, hη, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : ModGL Tag.G2 F,
      y = rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL) := ⟨_, rfl⟩
  rw [← hy]
  have hχ : rootChar b ((1 : WeylGroup Tag.G2) • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)) =
      b g2i0 := by
    rw [one_smul, g2_single_0, rootChar_g2vec]
    simp
  have hdc := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i0 b
  rw [hχ] at hdc
  have hηb : ((b g2i0 : Fˣ) : F) = -η := by
    calc ((b g2i0 : Fˣ) : F) = ((b g2i0 : Fˣ) : F) * (η * η) := by rw [hη, mul_one]
      _ = (((b g2i0 : Fˣ) : F) * η) * η := by ring
      _ = -η := by rw [hb]; ring
  have hηb' : (((b g2i0)⁻¹ : Fˣ) : F) = -η := by
    have h1 : ((b g2i0 : Fˣ) : F) * (-η) = 1 := by
      rw [hηb]
      linear_combination hη
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right h1
  have hyu : ∀ c : F, y * rootChart Tag.G2 F 1 g2i0 (uSL c) * y⁻¹ =
      rootChart Tag.G2 F 1 g2i0 (vSL (((-1 : Fˣ) : F) * c)) := by
    intro c
    have e1 : y * rootChart Tag.G2 F 1 g2i0 (uSL c) * y⁻¹ =
        rootDiagUnit Tag.G2 b * ((g2ChartA F WSL * g2ChartB F WSL) *
          rootChart Tag.G2 F 1 g2i0 (uSL c) * (g2ChartA F WSL * g2ChartB F WSL)⁻¹) *
          (rootDiagUnit Tag.G2 b)⁻¹ := by
      rw [hy]
      group
    rw [e1, hu c, hdc (vSL (η * c)), glConjSL_diag_vSL, hηb']
    congr 2
    simp only [Units.val_neg, Units.val_one]
    linear_combination (-c) * hη
  have hyv : ∀ c : F, y * rootChart Tag.G2 F 1 g2i0 (vSL c) * y⁻¹ =
      rootChart Tag.G2 F 1 g2i0 (uSL ((((-1 : Fˣ)⁻¹ : Fˣ) : F) * c)) := by
    intro c
    have e1 : y * rootChart Tag.G2 F 1 g2i0 (vSL c) * y⁻¹ =
        rootDiagUnit Tag.G2 b * ((g2ChartA F WSL * g2ChartB F WSL) *
          rootChart Tag.G2 F 1 g2i0 (vSL c) * (g2ChartA F WSL * g2ChartB F WSL)⁻¹) *
          (rootDiagUnit Tag.G2 b)⁻¹ := by
      rw [hy]
      group
    rw [e1, hv c, hdc (uSL (η * c)), glConjSL_diag_uSL, hηb]
    congr 2
    simp only [inv_neg, inv_one, Units.val_neg, Units.val_one]
    linear_combination (-c) * hη
  have hall := conj_eq_of_generators (Φ := rootChart Tag.G2 F 1 g2i0) (x := y)
    (glConjSL (antiGL (-1 : Fˣ))) (fun c => by rw [hyu c, glConjSL_anti_uSL])
    (fun c => by rw [hyv c, glConjSL_anti_vSL]) WSL
  rw [glConjSL_antiGL_neg_one_WSL] at hall
  exact mul_inv_eq_iff_eq_mul.mp hall

end Sign

section Closure

variable {F : Type} [Field F] [Finite F]


theorem adjointGroup_le_of_weyl_e0 (hodd : Odd (Nat.card F)) {M : Subgroup (ModGL Tag.G2 F)}
    (hX : toralCentralizer Tag.G2 F ![-1, 1] ≤ M)
    (hn : rootChart Tag.G2 F 1 g2i0 WSL ∈ M) : adjointGroup Tag.G2 F ≤ M := by
  obtain ⟨-, -, hker, -⟩ := g2_toral_data_a1 (F := F) hodd (a := ![-1, 1]) rfl
  have hn₁ : rootChart Tag.G2 F 1 g2i1 WSL ∈ M :=
    hX (g2ChartA_mem_toralCentralizer hodd (a := ![-1, 1]) rfl WSL)
  have hβk : g2vec 2 3 ∈ rootCharKernel (τ := Tag.G2) (K := F) ![-1, 1] := by
    rw [hker]; simp
  have hβroot : IsRoot Tag.G2 (g2vec 2 3) := hβk.1
  have hpair : rootPair Tag.G2 F (g2vec 2 3) ≤ M := (rootPair_le_toralCentralizer hβk).trans hX
  have hβ₁ : ∀ c : F, pinnedX Tag.G2 F (g2vec 2 3) c ∈ M := fun c =>
    hpair (Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨c, rfl⟩))
  have hβ₂ : ∀ c : F, pinnedX Tag.G2 F (-g2vec 2 3) c ∈ M := fun c =>
    hpair (Subgroup.mem_sup_right (mem_rootSubgroup.mpr ⟨c, rfl⟩))
  have hw := (signWeyl_rootChart_WSL (τ := Tag.G2) (K := F) 1 g2i1).mul
    (signWeyl_rootChart_WSL (τ := Tag.G2) (K := F) 1 g2i0)
  have hNM : rootChart Tag.G2 F 1 g2i1 WSL * rootChart Tag.G2 F 1 g2i0 WSL ∈ M := mul_mem hn₁ hn
  have hw1 : ((1 * simple Tag.G2 g2i1 * (1 : WeylGroup Tag.G2)⁻¹) *
      (1 * simple Tag.G2 g2i0 * (1 : WeylGroup Tag.G2)⁻¹)) • g2vec 2 3 = g2vec 1 0 := by
    simp only [inv_one, one_mul, mul_one]
    rw [mul_smul, g2_s0_smul, g2_s1_smul]
    norm_num [g2vec_0, g2vec_1]
  have hE : ∀ c : F, pinnedX Tag.G2 F (g2vec 1 0) c ∈ M := by
    intro c
    obtain ⟨ε, hε, h⟩ := hw (g2vec 2 3) hβroot
    have h' := h (ε * c)
    rw [hw1, ← mul_assoc, hε, one_mul] at h'
    rw [← h']
    exact mul_mem (mul_mem hNM (hβ₁ _)) (inv_mem hNM)
  have hE' : ∀ c : F, pinnedX Tag.G2 F (-g2vec 1 0) c ∈ M := by
    intro c
    obtain ⟨ε, hε, h⟩ := hw (-g2vec 2 3) (IsRoot.neg hβroot)
    have h' := h (ε * c)
    rw [smul_neg, hw1, ← mul_assoc, hε, one_mul] at h'
    rw [← h']
    exact mul_mem (mul_mem hNM (hβ₂ _)) (inv_mem hNM)
  have hpair0 : rootPair Tag.G2 F (g2vec 1 0) ≤ M := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
      exact hE c
    · obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
      exact hE' c
  rw [adjointGroup_eq_iSup_rootPair_single]
  refine iSup_le fun i => ?_
  fin_cases i
  · show rootPair Tag.G2 F (Pi.single g2i0 1) ≤ M
    rw [g2_single_0]
    exact hpair0
  · have hker1 : (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ) ∈
        rootCharKernel (τ := Tag.G2) (K := F) ![-1, 1] :=
      ⟨isRoot_single _ _, (rootChar_single_g2 _ _).trans rfl⟩
    exact (rootPair_le_toralCentralizer hker1).trans hX

end Closure

end CFSG.ClassicalInvolution.G2D4Models
