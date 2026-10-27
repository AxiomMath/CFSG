module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem units_cube_mul_fixed (hK : Nat.card K = 16) (δ : Kˣ) :
    δ = (δ ^ 2) ^ 3 * δ ^ 10 ∧ (δ ^ 10) ^ 4 = δ ^ 10 := by
  have h15 : δ ^ 15 = 1 := by
    have h : Nat.card Kˣ = 15 := by rw [Nat.card_units, hK]
    rw [← h]
    exact pow_card_eq_one'
  have h16 : δ ^ 16 = δ := by rw [show 16 = 15 + 1 from rfl, pow_succ, h15, one_mul]
  constructor
  · calc δ = δ ^ 16 := h16.symm
      _ = (δ ^ 2) ^ 3 * δ ^ 10 := by rw [← pow_mul, ← pow_add]
  · calc (δ ^ 10) ^ 4 = δ ^ 15 * δ ^ 15 * δ ^ 10 := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ = δ ^ 10 := by rw [h15, one_mul, one_mul]

theorem coset_conj {G : Type} [Group G] {N : Subgroup G} [N.Normal] {α : G} (hα1 : α ≠ 1)
    (hK : Nat.card K = 16) (φ : N ≃* projectiveSL 3 K) (ρ : G →* MulAut (projectiveSL 3 K))
    (hinj : Function.Injective ρ) (hρW : ∀ w : N, ρ w = MulAut.conj (φ w))
    (c : GL (Fin 3) K) (σ : K ≃+* K) (hσ : ∀ t, σ t = t ^ 4)
    (hρa : ρ α = conjAut 3 K c * fieldAut 3 K σ * (conjAut 3 K c)⁻¹) :
    ∀ x ∈ N, orderOf (α * x) = 2 → ∃ γ ∈ N, γ⁻¹ * α * γ = α * x := by
  intro x hx hord
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hα1
    apply hinj
    rw [hρa, h1, map_one, mul_one, mul_inv_cancel, map_one]
  obtain ⟨g₀, hg₀⟩ := proj_surjective 3 K (φ ⟨x, hx⟩)
  have hρx : ρ x = conjAut 3 K (SpecialLinearGroup.toGL g₀) := by
    rw [conjAut_toGL, hg₀]
    exact hρW ⟨x, hx⟩
  set B : GL (Fin 3) K :=
    c * GeneralLinearGroup.map (σ : K →+* K) (c⁻¹ * SpecialLinearGroup.toGL g₀) with hB
  have hX : ρ (α * x) = conjAut 3 K B * fieldAut 3 K σ := by
    calc ρ (α * x) = conjAut 3 K c *
          (fieldAut 3 K σ * conjAut 3 K (c⁻¹ * SpecialLinearGroup.toGL g₀)) := by
          rw [map_mul, hρa, hρx, map_mul (conjAut 3 K) c⁻¹, map_inv]
          group
      _ = conjAut 3 K B * fieldAut 3 K σ := by
          rw [fieldAut_mul_conjAut, ← mul_assoc, ← map_mul]
  have hX2 : (conjAut 3 K B * fieldAut 3 K σ) ^ 2 = 1 := by
    rw [← hX, ← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent (f := 4) (by norm_num)
    (by rw [hK]; norm_num) le_rfl B σ hσ1 hX2
  set g : GL (Fin 3) K := H * c⁻¹ with hg
  set δ : Kˣ := GeneralLinearGroup.det g with hδ
  obtain ⟨hδeq, hfix⟩ := units_cube_mul_fixed hK δ
  set x₀ : K := ((δ ^ 10 : Kˣ) : K) with hx₀def
  have hσx₀ : σ x₀ = x₀ := by
    rw [hσ, hx₀def, ← Units.val_pow_eq_pow_val, hfix]
  set dM : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![x₀, 1, 1] with hdMdef
  have hdM : dM.det = x₀ := by
    rw [hdMdef, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  set d : GL (Fin 3) K :=
    GeneralLinearGroup.mkOfDetNeZero dM (by rw [hdM]; exact Units.ne_zero _) with hddef
  have hdσ : GeneralLinearGroup.map (σ : K →+* K) d = d := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [hddef, hdMdef, hσx₀]
  have hdetd : GeneralLinearGroup.det d = δ ^ 10 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    exact hdM
  set D : GL (Fin 3) K := c * d * c⁻¹ with hD
  have hdetD : GeneralLinearGroup.det D = δ ^ 10 := by
    rw [hD, map_mul, map_mul, map_inv, hdetd, mul_comm (GeneralLinearGroup.det c),
      mul_assoc, mul_inv_cancel, mul_one]
  set H₁ : GL (Fin 3) K := (GeneralLinearGroup.scalar (Fin 3) (δ ^ 2))⁻¹ * g * D⁻¹ with hH₁
  have hdetH₁ : GeneralLinearGroup.det H₁ = 1 := by
    rw [hH₁, map_mul, map_mul, map_inv, map_inv, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, hdetD, ← hδ]
    calc ((δ ^ 2) ^ 3)⁻¹ * δ * (δ ^ 10)⁻¹ = ((δ ^ 2) ^ 3)⁻¹ * ((δ ^ 2) ^ 3 * δ ^ 10) *
          (δ ^ 10)⁻¹ := by rw [← hδeq]
      _ = 1 := by group
  obtain ⟨h₁, hh₁⟩ : H₁ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* _).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdetH₁
  have hgdec : g = GeneralLinearGroup.scalar (Fin 3) (δ ^ 2) * H₁ * D := by
    rw [hH₁]
    group
  have hcomm : fieldAut 3 K σ * conjAut 3 K d = conjAut 3 K d * fieldAut 3 K σ := by
    rw [fieldAut_mul_conjAut, hdσ]
  have hDcomm : conjAut 3 K D * ρ α * (conjAut 3 K D)⁻¹ = ρ α := by
    have hf : conjAut 3 K d * fieldAut 3 K σ * (conjAut 3 K d)⁻¹ = fieldAut 3 K σ := by
      rw [← hcomm]
      group
    calc conjAut 3 K D * ρ α * (conjAut 3 K D)⁻¹ =
        conjAut 3 K c * (conjAut 3 K d * fieldAut 3 K σ * (conjAut 3 K d)⁻¹) *
          (conjAut 3 K c)⁻¹ := by
          rw [hD, hρa, map_mul, map_mul, map_inv]
          group
      _ = ρ α := by rw [hf, hρa]
  have hconj : ρ (α * x) = conjAut 3 K H₁ * ρ α * (conjAut 3 K H₁)⁻¹ := by
    have hfa : fieldAut 3 K σ = (conjAut 3 K c)⁻¹ * ρ α * conjAut 3 K c := by
      rw [hρa]
      group
    have hgc : conjAut 3 K H = conjAut 3 K g * conjAut 3 K c := by
      rw [hg, map_mul, map_inv]
      group
    calc ρ (α * x) = conjAut 3 K g * ρ α * (conjAut 3 K g)⁻¹ := by
          rw [hX, hH, hgc, hfa]
          group
      _ = conjAut 3 K H₁ * (conjAut 3 K D * ρ α * (conjAut 3 K D)⁻¹) *
          (conjAut 3 K H₁)⁻¹ := by
          rw [hgdec, map_mul, map_mul, conjAut_scalar]
          group
      _ = conjAut 3 K H₁ * ρ α * (conjAut 3 K H₁)⁻¹ := by rw [hDcomm]
  rw [← hh₁, conjAut_toGL] at hconj
  set w : N := φ.symm (proj 3 K h₁) with hw
  have hρw : ρ (w : G) = MulAut.conj (proj 3 K h₁) := by
    rw [hρW, hw, MulEquiv.apply_symm_apply]
  refine ⟨(w : G)⁻¹, N.inv_mem w.2, ?_⟩
  apply hinj
  rw [inv_inv, map_mul, map_mul, map_inv, hρw, hconj]

end CFSG.ComponentClassification.GSThmB.Soc
