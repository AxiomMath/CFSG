module

public import CFSG.RankThree.PartOne.KE.SLnFamily

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open Matrix MatrixGroups CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section

variable {τ : Tag} {L : Type} [Field L] {n : ℕ}

@[expose] def diagSLn (d : Fin n → Lˣ) (h : ∏ i, (d i : L) = 1) : SL(n, L) :=
  ⟨Matrix.diagonal fun i => (d i : L), by simp [Matrix.det_diagonal, h]⟩

theorem coe_diagSLn (d : Fin n → Lˣ) (h : ∏ i, (d i : L) = 1) :
    ((diagSLn d h : SL(n, L)) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (d i : L) :=
  rfl

theorem diagSLn_inv (d : Fin n → Lˣ) (h : ∏ i, (d i : L) = 1)
    (h' : ∏ i, (((d i)⁻¹ : Lˣ) : L) = 1) : (diagSLn d h)⁻¹ = diagSLn (fun i => (d i)⁻¹) h' := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagSLn, Matrix.diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem diagSLn_conj (d : Fin n → Lˣ) (z : Lˣ) (h : ∏ i, (((z * d i : Lˣ)) : L) = 1)
    (h' : ∏ i, ((((z * d i)⁻¹ : Lˣ)) : L) = 1) (A : SL(n, L)) :
    diagSLn (fun i => z * d i) h * A * (diagSLn (fun i => z * d i) h)⁻¹ = conjDiagn d A := by
  rw [diagSLn_inv _ h h']
  refine Subtype.ext ?_
  rw [coe_conjDiagn]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagSLn]
  ext i j
  simp [diagGLn, Matrix.mul_apply, Matrix.diagonal_apply]
  have hz : (z : L) ≠ 0 := z.ne_zero
  field_simp

end

section Main

variable {τ : Tag} {L : Type} [Field L]
  [IsAlgClosed L] {n : ℕ}

theorem peel_block_gen (hn : 0 < n) (ρ : SL(n, L) →* ModGL τ L)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin n → Lˣ, ∀ A : SL(n, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(n, L), (∀ i j, i ≠ j → (A : Matrix (Fin n) (Fin n) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (m : SL(n, L))
    (hconj : ∀ (d' : Fin n → Lˣ) (h : ∏ i, (d' i : L) = 1), ∃ g : SL(n, L), ∀ i j, i ≠ j →
      ((g⁻¹ * (m * diagSLn d' h) * g : SL(n, L)) : Matrix (Fin n) (Fin n) L) i j = 0)
    {t u : ModGL τ L} (ht : t ∈ torusGroup τ L) (hu : ∀ A : SL(n, L), u * ρ A = ρ A * u) :
    ∃ g : SL(n, L), ∃ h ∈ torusGroup τ L, ∃ t₁ ∈ torusGroup τ L,
      (∀ A : SL(n, L), t₁ * ρ A = ρ A * t₁) ∧
        ρ g * (ρ m * t * u) * (ρ g)⁻¹ = h * (t₁ * u) := by
  obtain ⟨β, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨d, hd⟩ := htor β
  have hdet0 : (∏ i, (d i : L)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (d i).ne_zero
  obtain ⟨z0, hz0⟩ := IsAlgClosed.exists_pow_nat_eq ((∏ i, (d i : L))⁻¹) hn
  have hz0ne : z0 ≠ 0 := fun h => by
    rw [h, zero_pow hn.ne'] at hz0
    exact (inv_ne_zero hdet0) hz0.symm
  set z : Lˣ := Units.mk0 z0 hz0ne with hz
  set d' : Fin n → Lˣ := fun i => z * d i with hd'
  have hd'det : ∏ i, (d' i : L) = 1 := by
    simp only [hd', Units.val_mul, hz, Units.val_mk0, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, hz0]
    exact inv_mul_cancel₀ hdet0
  have hd'inv : ∏ i, (((d' i)⁻¹ : Lˣ) : L) = 1 := by
    simp only [Units.val_inv_eq_inv_val]
    rw [Finset.prod_inv_distrib, hd'det, inv_one]
  set D' : SL(n, L) := diagSLn d' hd'det with hD'
  have hD'T : ρ D' ∈ torusGroup τ L := hdiag D' (fun i j hij => by
    simp [hD', coe_diagSLn, hij])
  set t₂ : ModGL τ L := (ρ D')⁻¹ * rootDiagUnit τ β with ht₂
  have ht₂T : t₂ ∈ torusGroup τ L := mul_mem (inv_mem hD'T) ht
  have ht₂c : ∀ A : SL(n, L), t₂ * ρ A = ρ A * t₂ := by
    intro A
    have h1 : rootDiagUnit τ β * ρ A * (rootDiagUnit τ β)⁻¹ = ρ D' * ρ A * (ρ D')⁻¹ := by
      rw [hd A, ← map_mul, ← map_inv, ← map_mul, hD']
      congr 1
      exact (diagSLn_conj d z hd'det (by
        simpa only [hd'] using hd'inv) A).symm
    calc t₂ * ρ A = (ρ D')⁻¹ * (rootDiagUnit τ β * ρ A * (rootDiagUnit τ β)⁻¹) *
          rootDiagUnit τ β := by rw [ht₂]; group
      _ = (ρ D')⁻¹ * (ρ D' * ρ A * (ρ D')⁻¹) * rootDiagUnit τ β := by rw [h1]
      _ = ρ A * t₂ := by rw [ht₂]; group
  set mD : SL(n, L) := m * D' with hmD
  obtain ⟨g', hg'⟩ := hconj d' hd'det
  have hΔT : ρ (g'⁻¹ * mD * g') ∈ torusGroup τ L := hdiag _ hg'
  have hcomm : ∀ A : SL(n, L), (t₂ * u) * ρ A = ρ A * (t₂ * u) := fun A => by
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
