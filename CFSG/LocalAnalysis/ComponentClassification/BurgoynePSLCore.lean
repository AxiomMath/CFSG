module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSlice
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem exists_semilinear_of_odd [Finite K] (hn : 3 ≤ n) {y : MulAut (projectiveSL n K)}
    (hy : Odd (orderOf y)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), y = conjAut n K A * fieldAut n K σ :=
  mem_semilinearAutGroup_iff.1
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd hn hy
      (pow_orderOf_eq_one y))

theorem ringEquiv_eq_one_of_prime_card [Finite K] (hp : (Nat.card K).Prime) (σ : K ≃+* K) :
    σ = 1 := by
  have : Fact (Nat.card K).Prime := ⟨hp⟩
  have htop : AddSubgroup.zmultiples (1 : K) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : K)) with h | h
    · exact absurd (h ▸ AddSubgroup.mem_zmultiples (1 : K)) (by simp)
    · exact h
  ext x
  obtain ⟨k, rfl⟩ : x ∈ AddSubgroup.zmultiples (1 : K) := htop ▸ AddSubgroup.mem_top x
  simp

@[expose] def slCentralizer (D₀ : GL (Fin n) K) : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
  (centralizer ({D₀} : Set (GL (Fin n) K))).comap Matrix.SpecialLinearGroup.toGL

theorem mem_slCentralizer {D₀ : GL (Fin n) K} {g : Matrix.SpecialLinearGroup (Fin n) K} :
    g ∈ slCentralizer D₀ ↔
      (g : Matrix (Fin n) (Fin n) K) * (D₀ : Matrix (Fin n) (Fin n) K) = D₀ * g := by
  rw [slCentralizer, mem_comap, mem_centralizer_singleton_iff, Units.ext_iff]
  rfl

theorem exists_scalar_of_commute_conjAut [Finite K] (hn : 3 ≤ n) (D₀ : GL (Fin n) K)
    (h : Matrix.SpecialLinearGroup (Fin n) K)
    (hc : conjProj n K h * conjAut n K D₀ = conjAut n K D₀ * conjProj n K h) :
    ∃ c : Kˣ, Matrix.SpecialLinearGroup.toGL h * D₀ * (Matrix.SpecialLinearGroup.toGL h)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c * D₀ := by
  set X := Matrix.SpecialLinearGroup.toGL h with hX
  have hcX : conjProj n K h = conjAut n K X := (conjAut_toGL h).symm
  rw [hcX] at hc
  have h1 : conjAut n K (X * D₀ * X⁻¹ * D₀⁻¹) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨-, c, hc'⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h1
  refine ⟨c, ?_⟩
  rw [hc', inv_mul_cancel_right]

theorem isSubnormal_map_conjProj [Finite K] (hn : 3 ≤ n) {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    (D₀ : GL (Fin n) K) {F : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)}
    (hF1 : F ≤ slCentralizer D₀) (hF2 : ∀ h ∈ slCentralizer D₀, ∀ g ∈ F, h * g * h⁻¹ ∈ F) :
    F.map (conjProj n K) ≤ B ⊓ centralizer ({conjAut n K D₀} : Set _) ∧
      ((F.map (conjProj n K)).subgroupOf
        (B ⊓ centralizer ({conjAut n K D₀} : Set _))).IsSubnormal := by
  set H := B ⊓ centralizer ({conjAut n K D₀} : Set (MulAut (projectiveSL n K))) with hH
  set Inn := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hInn
  set C₁ := (slCentralizer D₀).map (conjProj n K) with hC₁
  have hInnN : Inn.Normal := conj_range_normal
  have hC₁le : C₁ ≤ Inn ⊓ H := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨_, rfl⟩, hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : conjAut n K D₀ * conjProj n K h * (conjAut n K D₀)⁻¹ = conjProj n K h := by
      rw [conjAut_mul_conjProj_mul_inv]
      congr 1
      apply Subtype.ext
      rw [CatalogueBHigherLinearAction.slConjugation_matrix, ← mem_slCentralizer.1 hh,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    calc conjProj n K h * conjAut n K D₀
        = conjAut n K D₀ * conjProj n K h * (conjAut n K D₀)⁻¹ * conjAut n K D₀ := by
          rw [h1]
      _ = conjAut n K D₀ * conjProj n K h := by group
  have hnC₁ : ∀ c ∈ Inn ⊓ H, ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁ := by
    rintro c ⟨⟨y, rfl⟩, -, hct⟩ _ ⟨h, hh, rfl⟩
    obtain ⟨h₁, rfl⟩ := proj_surjective n K y
    have hct' : conjProj n K h₁ * conjAut n K D₀ = conjAut n K D₀ * conjProj n K h₁ :=
      mem_centralizer_singleton_iff.1 hct
    obtain ⟨s, hs⟩ := exists_scalar_of_commute_conjAut hn D₀ h₁ hct'
    refine ⟨h₁ * h * h₁⁻¹, mem_slCentralizer.2 ?_, by simp only [map_mul, map_inv]; rfl⟩
    have hsc : ∀ Z : GL (Fin n) K, Z * GeneralLinearGroup.scalar (Fin n) s =
        GeneralLinearGroup.scalar (Fin n) s * Z := fun Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
    set X := Matrix.SpecialLinearGroup.toGL h₁ with hX
    set Y := Matrix.SpecialLinearGroup.toGL h with hY
    have hYD : Y * D₀ = D₀ * Y := Units.ext (mem_slCentralizer.1 hh)
    have key : X * Y * X⁻¹ * D₀ = D₀ * (X * Y * X⁻¹) := by
      apply mul_left_cancel (a := GeneralLinearGroup.scalar (Fin n) s)
      calc GeneralLinearGroup.scalar (Fin n) s * (X * Y * X⁻¹ * D₀)
          = X * Y * X⁻¹ * (GeneralLinearGroup.scalar (Fin n) s * D₀) := by
            rw [← mul_assoc, ← hsc]; group
        _ = X * Y * X⁻¹ * (X * D₀ * X⁻¹) := by rw [hs]
        _ = X * (Y * D₀) * X⁻¹ := by group
        _ = X * (D₀ * Y) * X⁻¹ := by rw [hYD]
        _ = (X * D₀ * X⁻¹) * (X * Y * X⁻¹) := by group
        _ = GeneralLinearGroup.scalar (Fin n) s * (D₀ * (X * Y * X⁻¹)) := by rw [hs, mul_assoc]
    have e : Matrix.SpecialLinearGroup.toGL (h₁ * h * h₁⁻¹) = X * Y * X⁻¹ := by
      rw [hX, hY, map_mul, map_mul, map_inv]
    change ((Matrix.SpecialLinearGroup.toGL (h₁ * h * h₁⁻¹) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * D₀ = D₀ * ((Matrix.SpecialLinearGroup.toGL (h₁ * h * h₁⁻¹) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [e]
    exact congrArg Units.val key
  have hC₂ : ((Inn ⊓ H).subgroupOf H).IsSubnormal := isSubnormal_inf_subgroupOf H
  have hC₁s : (C₁.subgroupOf H).IsSubnormal := isSubnormal_subgroupOf_of_normalizes hC₁le hnC₁ hC₂
  have hFC₁ : F.map (conjProj n K) ≤ C₁ := map_mono hF1
  refine ⟨hFC₁.trans (hC₁le.trans inf_le_right), isSubnormal_subgroupOf_of_normalizes hFC₁ ?_ hC₁s⟩
  rintro _ ⟨h, hh, rfl⟩ _ ⟨g, hg, rfl⟩
  exact ⟨h * g * h⁻¹, hF2 h hh g hg, by simp only [map_mul, map_inv]⟩

theorem commute_oddCoreIn_of_component [Finite K] (hn : 3 ≤ n)
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    (D₀ : GL (Fin n) K) {F : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)}
    (hF1 : F ≤ slCentralizer D₀) (hF2 : ∀ h ∈ slCentralizer D₀, ∀ g ∈ F, h * g * h⁻¹ ∈ F)
    (hq : IsQuasisimple (F.map (conjProj n K))) (he : Even (Nat.card (F.map (conjProj n K))))
    {y : MulAut (projectiveSL n K)} (hy : y ∈ oddCoreIn B (conjAut n K D₀))
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ F) :
    y * conjProj n K g = conjProj n K g * y := by
  obtain ⟨hle, hs⟩ := isSubnormal_map_conjProj hn hB D₀ hF1 hF2
  exact commute_of_mem_pPrimeCore hle hq hs he hy ⟨g, hg, rfl⟩

theorem apply_proj_eq_of_commute
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {y : MulAut (projectiveSL n K)} {g : Matrix.SpecialLinearGroup (Fin n) K}
    (h : y * conjProj n K g = conjProj n K g * y) : y (proj n K g) = proj n K g := by
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProj n K g * y⁻¹ = conjProj n K g
  rw [h, mul_inv_cancel_right]

end CFSG.ComponentClassification.Burgoyne.PSL
