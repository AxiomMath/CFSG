module

public import CFSG.CGT.PushingUpLit.CGT6X.K7aOrth
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Fixed

variable (K : Type) [Field K]

@[expose] def orthProj : Subgroup (projectiveSL 3 K) := (orthSL K).map (proj 3 K)

variable {K}

theorem mem_orthProj {x : projectiveSL 3 K} :
    x ∈ orthProj K ↔ ∃ A ∈ orthSL K, proj 3 K A = x := Subgroup.mem_map

theorem dualAut_proj_of_mem {A : SpecialLinearGroup (Fin 3) K} (hA : A ∈ orthSL K) :
    dualAut 3 K (proj 3 K A) = proj 3 K A := by
  rw [dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_inv_eq_transpose hA, transpose_transpose]

theorem scalar_eq_smul_one (a : K) : scalar (Fin 3) a = a • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.smul_one_eq_diagonal]
  rfl

theorem dualAut_fixed_iff (x : projectiveSL 3 K) : dualAut 3 K x = x ↔ x ∈ orthProj K := by
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 K x
    rw [dualAut_proj] at hx
    have h : (((g⁻¹).transpose : SpecialLinearGroup (Fin 3) K))⁻¹ * g ∈ scalars 3 K :=
      QuotientGroup.eq.1 hx
    obtain ⟨c, hc3, hc⟩ := h
    have hgz : g = ((g⁻¹).transpose : SpecialLinearGroup (Fin 3) K) *
        ((((g⁻¹).transpose : SpecialLinearGroup (Fin 3) K))⁻¹ * g) := (mul_inv_cancel_left _ _).symm
    have hgm : (g : Matrix (Fin 3) (Fin 3) K) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
          scalar (Fin 3) (c : K) := by
      conv_lhs => rw [hgz]
      rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_transpose]
    have hgg : (g : Matrix (Fin 3) (Fin 3) K)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have hgt : (g : Matrix (Fin 3) (Fin 3) K)ᵀ =
          (c : K) • ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        conv_lhs => rw [hgm]
        rw [transpose_mul, transpose_transpose, scalar_eq_smul_one, transpose_smul, transpose_one,
          Matrix.smul_mul, Matrix.one_mul]
      rw [hgt, Matrix.smul_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hc3' : (c : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    set g' : SpecialLinearGroup (Fin 3) K := scalarElement c hc3 * g with hg'
    have hg'm : (g' : Matrix (Fin 3) (Fin 3) K) = (c : K) • (g : Matrix (Fin 3) (Fin 3) K) := by
      rw [hg', Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, scalar_eq_smul_one,
        Matrix.smul_mul, Matrix.one_mul]
    refine mem_orthProj.2 ⟨g', ?_, ?_⟩
    ·
      rw [mem_orthSL]
      apply mul_eq_one_comm.mp
      rw [hg'm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgg, smul_smul]
      have : (c : K) * (c : K) * (c : K) = 1 := by rw [← pow_three', hc3']
      rw [this, one_smul]
    · rw [hg']
      have hz : proj 3 K (scalarElement c hc3) = 1 :=
        (MonoidHom.mem_ker).1 (by rw [ker_proj]; exact scalarElement_mem_scalars c hc3)
      rw [map_mul, hz, one_mul]
  · rintro ⟨A, hA, rfl⟩
    exact dualAut_proj_of_mem hA

theorem card_orthProj_le [Finite K] : Nat.card (orthProj K) ≤ Nat.card (orthSL K) := by
  calc Nat.card (orthProj K)
      = Nat.card (proj 3 K '' (orthSL K : Set (SpecialLinearGroup (Fin 3) K))) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
    _ ≤ Nat.card (orthSL K : Set (SpecialLinearGroup (Fin 3) K)) :=
        Nat.card_image_le (Set.toFinite _)
    _ = Nat.card (orthSL K) := rfl

end Fixed

section Surviving

variable {K : Type} [Field K]

theorem linear_graph_surviving [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (A : GL (Fin 3) K) (hα : (conjAut 3 K A * dualAut 3 K) ^ 2 = 1)
    (Y : Subgroup (projectiveSL 3 K))
    (hY : Nat.card Y = Nat.card (SpecialLinearGroup (Fin 2) K))
    (hYt : ∀ y ∈ Y, (conjAut 3 K A * dualAut 3 K) y = y) :
    ∃ H : GL (Fin 3) K, conjAut 3 K A * dualAut 3 K =
        conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹ ∧
      Y = (orthProj K).map (conjAut 3 K H : MulAut (projectiveSL 3 K)).toMonoidHom := by
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
    even_linear_pure_graph_involution_normal_forms hf hK (by norm_num) A hα
  have hC1 : C = 1 := by
    rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext hC1
    · omega
  rw [hC1, map_one, one_mul] at hconj
  refine ⟨H, hconj, ?_⟩
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcH
  set Y' : Subgroup (projectiveSL 3 K) := Y.map (cH⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom
    with hY'
  have hY'fix : ∀ y' ∈ Y', dualAut 3 K y' = y' := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hYt y hy
    rw [hconj] at h1
    have h2 : cH (dualAut 3 K ((cH⁻¹ : MulAut (projectiveSL 3 K)) y)) = y := by
      have := h1
      simpa [hcH, MulAut.mul_apply] using this
    have h3 := congrArg (cH⁻¹ : MulAut (projectiveSL 3 K)) h2
    simpa using h3
  have hle : Y' ≤ orthProj K := fun y' hy' => (dualAut_fixed_iff y').1 (hY'fix y' hy')
  have hcardY' : Nat.card Y' = Nat.card Y :=
    (Nat.card_congr (Subgroup.equivMapOfInjective Y
      (cH⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom
      (cH⁻¹ : MulAut (projectiveSL 3 K)).injective).toEquiv).symm
  have hfin : Finite (orthProj K) := inferInstance
  have hEq : Y' = orthProj K := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcardY', hY]
    exact (card_orthProj_le).trans card_orthSL_le
  ext x
  constructor
  · intro hx
    have hmem : (cH⁻¹ : MulAut (projectiveSL 3 K)) x ∈ orthProj K := by
      rw [← hEq]
      exact ⟨x, hx, rfl⟩
    exact ⟨_, hmem, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    rw [← hEq] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa using hy

end Surviving

end CFSG.CGT.PushingUpLit.CGT6X.K7a
