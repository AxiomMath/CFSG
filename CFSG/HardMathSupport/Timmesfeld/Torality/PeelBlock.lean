module

public import CFSG.HardMathSupport.Timmesfeld.Torality.SL3Monomial
public import CFSG.RankThree.PartOne.KE.A2Family

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section

variable {τ : Tag} {L : Type} [Field L]

@[expose] def diagSL3 (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) : SL(3, L) :=
  ⟨Matrix.diagonal fun i => (d i : L), by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, h]⟩

theorem coe_diagSL3 (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) :
    ((diagSL3 d h : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L) :=
  rfl

theorem diagSL3_inv (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) :
    (diagSL3 d h)⁻¹ = diagSL3 (fun i => (d i)⁻¹) (by
      have h' : ((d 0)⁻¹ : Lˣ) * (d 1)⁻¹ * (d 2)⁻¹ = 1 := by
        have : (d 0 : Lˣ) * d 1 * d 2 = 1 := Units.ext (by simpa using h)
        calc ((d 0)⁻¹ * (d 1)⁻¹ * (d 2)⁻¹ : Lˣ) = (d 0 * d 1 * d 2)⁻¹ := by rw [mul_inv, mul_inv]
          _ = 1 := by rw [this, inv_one]
      simpa using congrArg Units.val h') := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL3, Matrix.diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem diagSL3_conj (d : Fin 3 → Lˣ) (z : Lˣ) (h : ((z * d 0 : Lˣ) : L) * (z * d 1 : Lˣ) *
    (z * d 2 : Lˣ) = 1) (A : SL(3, L)) :
    diagSL3 (fun i => z * d i) h * A * (diagSL3 (fun i => z * d i) h)⁻¹ = conjDiag3 d A := by
  rw [diagSL3_inv]
  refine Subtype.ext ?_
  rw [coe_conjDiag3]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL3]
  ext i j
  simp [diagGL3, Matrix.mul_apply, Matrix.diagonal_apply]
  have hz : (z : L) ≠ 0 := z.ne_zero
  field_simp

end

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem peel_block {ω : L} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : L) ≠ 0)
    (ρ : SL(3, L) →* ModGL τ L)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    {a b c : L} (habc : a * b * c = 1) (m : SL(3, L))
    (hm : (m : Matrix (Fin 3) (Fin 3) L) = monoM₁ a b c ∨
      (m : Matrix (Fin 3) (Fin 3) L) = monoM₂ a b c)
    {t u : ModGL τ L} (ht : t ∈ torusGroup τ L) (hu : ∀ A : SL(3, L), u * ρ A = ρ A * u) :
    ∃ g : SL(3, L), ∃ h ∈ torusGroup τ L, ∃ t₁ ∈ torusGroup τ L,
      (∀ A : SL(3, L), t₁ * ρ A = ρ A * t₁) ∧
        ρ g * (ρ m * t * u) * (ρ g)⁻¹ = h * (t₁ * u) := by
  obtain ⟨β, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨d, hd⟩ := htor β
  have hdet0 : ((d 0 : L) * d 1 * d 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (d 0).ne_zero (d 1).ne_zero) (d 2).ne_zero
  obtain ⟨z0, hz0⟩ := IsAlgClosed.exists_pow_nat_eq (((d 0 : L) * d 1 * d 2)⁻¹) (by norm_num : 0 < 3)
  have hz0ne : z0 ≠ 0 := fun h => by
    rw [h] at hz0
    simp at hz0
  set z : Lˣ := Units.mk0 z0 hz0ne with hz
  set d' : Fin 3 → Lˣ := fun i => z * d i with hd'
  have hd'det : (d' 0 : L) * d' 1 * d' 2 = 1 := by
    simp only [hd', Units.val_mul, hz, Units.val_mk0]
    calc z0 * (d 0 : L) * (z0 * d 1) * (z0 * d 2) = z0 ^ 3 * ((d 0 : L) * d 1 * d 2) := by ring
      _ = 1 := by rw [hz0, inv_mul_cancel₀ hdet0]
  set D' : SL(3, L) := diagSL3 d' hd'det with hD'
  have hD'T : ρ D' ∈ torusGroup τ L := hdiag D' (fun i j hij => by
    simp [hD', coe_diagSL3, hij])
  set t₂ : ModGL τ L := (ρ D')⁻¹ * rootDiagUnit τ β with ht₂
  have ht₂T : t₂ ∈ torusGroup τ L := mul_mem (inv_mem hD'T) ht
  have ht₂c : ∀ A : SL(3, L), t₂ * ρ A = ρ A * t₂ := by
    intro A
    have h1 : rootDiagUnit τ β * ρ A * (rootDiagUnit τ β)⁻¹ = ρ D' * ρ A * (ρ D')⁻¹ := by
      rw [hd A, ← map_mul, ← map_inv, ← map_mul, diagSL3_conj d z hd'det A]
    calc t₂ * ρ A = (ρ D')⁻¹ * (rootDiagUnit τ β * ρ A * (rootDiagUnit τ β)⁻¹) *
          rootDiagUnit τ β := by rw [ht₂]; group
      _ = (ρ D')⁻¹ * (ρ D' * ρ A * (ρ D')⁻¹) * rootDiagUnit τ β := by rw [h1]
      _ = ρ A * t₂ := by rw [ht₂]; group
  set mD : SL(3, L) := m * D' with hmD
  have hmD' : (mD : Matrix (Fin 3) (Fin 3) L) = monoM₁ (a * d' 0) (b * d' 1) (c * d' 2) ∨
      (mD : Matrix (Fin 3) (Fin 3) L) = monoM₂ (a * d' 1) (b * d' 2) (c * d' 0) := by
    rcases hm with hm | hm
    · left
      simp only [hmD, Matrix.SpecialLinearGroup.coe_mul, hm, hD', coe_diagSL3, monoM₁]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,
        Matrix.diagonal_apply]
    · right
      simp only [hmD, Matrix.SpecialLinearGroup.coe_mul, hm, hD', coe_diagSL3, monoM₂]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,
        Matrix.diagonal_apply]
  obtain ⟨g', hg'⟩ : ∃ g' : SL(3, L), ((g'⁻¹ * mD * g' : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![1, ω, ω ^ 2] := by
    rcases hmD' with h' | h'
    · exact exists_sl3_conj_M₁ hω h3 (by
        have : (a * d' 0) * (b * d' 1) * (c * d' 2) = (a * b * c) * ((d' 0 : L) * d' 1 * d' 2) := by
          ring
        rw [this, habc, hd'det, one_mul]) mD h'
    · exact exists_sl3_conj_M₂ hω h3 (by
        have : (a * d' 1) * (b * d' 2) * (c * d' 0) = (a * b * c) * ((d' 0 : L) * d' 1 * d' 2) := by
          ring
        rw [this, habc, hd'det, one_mul]) mD h'
  have hΔT : ρ (g'⁻¹ * mD * g') ∈ torusGroup τ L := hdiag _ (fun i j hij => by
    rw [hg']
    simp [hij])
  have hcomm : ∀ A : SL(3, L), (t₂ * u) * ρ A = ρ A * (t₂ * u) := fun A => by
    rw [mul_assoc, hu A, ← mul_assoc, ht₂c A, mul_assoc]
  refine ⟨g'⁻¹, ρ (g'⁻¹ * mD * g'), hΔT, t₂, ht₂T, ht₂c, ?_⟩
  have hx : ρ m * rootDiagUnit τ β * u = ρ mD * (t₂ * u) := by
    rw [hmD, map_mul, ht₂]
    group
  rw [hx]
  have hc1 : ρ g'⁻¹ * (t₂ * u) * (ρ g'⁻¹)⁻¹ = t₂ * u := by
    rw [← hcomm g'⁻¹, mul_inv_cancel_right]
  calc ρ g'⁻¹ * (ρ mD * (t₂ * u)) * (ρ g'⁻¹)⁻¹
      = (ρ g'⁻¹ * ρ mD * (ρ g'⁻¹)⁻¹) * (ρ g'⁻¹ * (t₂ * u) * (ρ g'⁻¹)⁻¹) := by group
    _ = ρ (g'⁻¹ * mD * g') * (t₂ * u) := by
      rw [hc1, ← map_inv, ← map_mul, ← map_mul, inv_inv]

end Main

end CFSG.HardMathSupport.Timmesfeld.Torality
