module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary

section Conj

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem isometry_inv {d : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (M : GL (Fin d) K)
    (hM : conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) *
      (M : Matrix (Fin d) (Fin d) K) = 1) :
    ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) ∧
    conjTr (unitaryInvolution K p f) ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (M : Matrix (Fin d) (Fin d) K) := by
  have hMMi : (M : Matrix (Fin d) (Fin d) K) * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) := by
    calc ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        = (conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) *
            (M : Matrix (Fin d) (Fin d) K)) *
            ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hM, Matrix.one_mul]
      _ = conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]
  refine ⟨h1, ?_⟩
  rw [h1]
  ext i j
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  exact unitaryInvolution_involutive hK _

theorem conj_mem_SUid {d : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (M : GL (Fin d) K)
    (hM : conjTr (unitaryInvolution K p f) (M : Matrix (Fin d) (Fin d) K) *
      (M : Matrix (Fin d) (Fin d) K) = 1) {g : GL (Fin d) K}
    (hg : g ∈ SUid (unitaryInvolution K p f) d) :
    M * g * M⁻¹ ∈ SUid (unitaryInvolution K p f) d := by
  obtain ⟨hdet, hiso⟩ := mem_SUid.mp hg
  obtain ⟨hMi, hMiT⟩ := isometry_inv hK M hM
  have hMMi : (M : Matrix (Fin d) (Fin d) K) * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (M : Matrix (Fin d) (Fin d) K)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mem_SUid]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one]
    have := congrArg Matrix.det hMMi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact this
  · rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul, hMiT, ← hMi]
    calc (M : Matrix (Fin d) (Fin d) K) * (conjTr (unitaryInvolution K p f)
          (g : Matrix (Fin d) (Fin d) K) * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
          ((M : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
            ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
        = (M : Matrix (Fin d) (Fin d) K) * (conjTr (unitaryInvolution K p f)
            (g : Matrix (Fin d) (Fin d) K) * (((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              (M : Matrix (Fin d) (Fin d) K)) * (g : Matrix (Fin d) (Fin d) K)) *
              ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = (M : Matrix (Fin d) (Fin d) K) * (conjTr (unitaryInvolution K p f)
            (g : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K)) *
              ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [hMiM, Matrix.mul_one]
      _ = 1 := by rw [hiso, Matrix.mul_one, hMMi]

end Conj

section ConjHom

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def suConjHom (hK : Nat.card K = (p ^ f) ^ 2) (M : GL (Fin 4) K)
    (hM : conjTr (unitaryInvolution K p f) (M : Matrix (Fin 4) (Fin 4) K) *
      (M : Matrix (Fin 4) (Fin 4) K) = 1) : Su K p f 4 →* Su K p f 4 :=
  (((MulAut.conj M).toMonoidHom).comp (SUid (unitaryInvolution K p f) 4).subtype).codRestrict _
    (fun g => conj_mem_SUid hK M hM g.2)

theorem suMat_suConjHom (hK : Nat.card K = (p ^ f) ^ 2) (M : GL (Fin 4) K)
    (hM : conjTr (unitaryInvolution K p f) (M : Matrix (Fin 4) (Fin 4) K) *
      (M : Matrix (Fin 4) (Fin 4) K) = 1) (x : Su K p f 4) :
    suMat (suConjHom hK M hM x) = (M : Matrix (Fin 4) (Fin 4) K) * suMat x *
      ((M⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := rfl

theorem suConjHom_surjective (hK : Nat.card K = (p ^ f) ^ 2) (M : GL (Fin 4) K)
    (hM : conjTr (unitaryInvolution K p f) (M : Matrix (Fin 4) (Fin 4) K) *
      (M : Matrix (Fin 4) (Fin 4) K) = 1) : Function.Surjective (suConjHom hK M hM) := by
  have hinj : Function.Injective (suConjHom hK M hM) := by
    intro x y hxy
    have h1 : M * (x : GL (Fin 4) K) * M⁻¹ = M * (y : GL (Fin 4) K) * M⁻¹ :=
      congrArg (fun z : Su K p f 4 => (z : GL (Fin 4) K)) hxy
    have h2 : (x : GL (Fin 4) K) = (y : GL (Fin 4) K) := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact Subtype.ext h2
  exact Finite.injective_iff_surjective.mp hinj

@[expose] noncomputable def negTwoSU (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] : Su K p f 4 :=
  blockEmb K p f 4 2 2 (by norm_num) (negOneSU K p f)

theorem suMat_negTwoSU : suMat (negTwoSU K p f) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [negTwoSU, suMat_blockEmb_two, suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem negTwoSU_mul_self : negTwoSU K p f * negTwoSU K p f = 1 := by
  rw [negTwoSU, ← map_mul, negOneSU_mul_self, map_one]

theorem su_closure_union_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq2 : p ^ f ≠ 2)
    (c : Su K p f 4 →* Su K p f 4) (hc : Function.Surjective c) (S₁ S₂ : Set (Su K p f 4))
    (h₁ : ∀ i : Fin 3, i ≠ 2 → ∀ s ∈ (blockEmb2 K p f 3 i).range, c s ∈ S₁)
    (h₂ : ∀ i : Fin 3, i ≠ 0 → ∀ s ∈ (blockEmb2 K p f 3 i).range, c s ∈ S₂) :
    Subgroup.closure (S₁ ∪ S₂) = ⊤ := by
  have hgen : ⨆ i : Fin 3, ((blockEmb2 K p f 3 i).range).map c = ⊤ := by
    rw [← Subgroup.map_iSup, iSup_range_blockEmb2 hK hq2 3, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hc]
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun i => ?_
  rintro _ ⟨s, hs, rfl⟩
  apply Subgroup.subset_closure
  by_cases hi2 : i = 2
  · exact Or.inr (h₂ i (by rw [hi2]; decide) s hs)
  · exact Or.inl (h₁ i hi2 s hs)

theorem su_closure_fix_eq_top (hK : Nat.card K = (p ^ f) ^ 2) (hq2 : p ^ f ≠ 2) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ) (σ : MulAut X)
    (α : Su K p f 4 →* Su K p f 4) (hlift : ∀ x, θ (α x) = σ (θ x)) (y : Su K p f 4)
    (c : Su K p f 4 →* Su K p f 4) (hc : Function.Surjective c)
    (h₁ : ∀ i : Fin 3, i ≠ 2 → ∀ s ∈ (blockEmb2 K p f 3 i).range, α (c s) = c s)
    (h₂ : ∀ i : Fin 3, i ≠ 0 → ∀ s ∈ (blockEmb2 K p f 3 i).range,
      α (y * c s * y⁻¹) = c s) :
    Subgroup.closure ({g | σ g = g} ∪ {g | σ (θ y * g * (θ y)⁻¹) = g}) = ⊤ := by
  set C := Subgroup.closure ({g | σ g = g} ∪ {g | σ (θ y * g * (θ y)⁻¹) = g}) with hC
  have hcl := su_closure_union_eq_top hK hq2 c hc {x | α x = x} {x | α (y * x * y⁻¹) = x}
    (fun i hi s hs => h₁ i hi s hs) (fun i hi s hs => h₂ i hi s hs)
  have hle : Subgroup.closure ({x | α x = x} ∪ {x | α (y * x * y⁻¹) = x} : Set (Su K p f 4)) ≤
      C.comap θ := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · apply Subgroup.subset_closure
      left
      show σ (θ x) = θ x
      rw [← hlift, show α x = x from hx]
    · apply Subgroup.subset_closure
      right
      show σ (θ y * θ x * (θ y)⁻¹) = θ x
      have : σ (θ y * θ x * (θ y)⁻¹) = θ (α (y * x * y⁻¹)) := by
        rw [hlift]
        congr 1
        rw [map_mul, map_mul, map_inv]
      rw [this, show α (y * x * y⁻¹) = x from hx]
  rw [hcl] at hle
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := hθ g
  exact hle (Subgroup.mem_top x)

end ConjHom

end CFSG.ClassicalInvolution.Asc77.T8W
