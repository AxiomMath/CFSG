module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.SelL39

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

@[expose] def slCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K' where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

@[expose] def projectiveSLCongr {n : ℕ} {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') :
    projectiveSL n K ≃* projectiveSL n K' :=
  QuotientGroup.congr (scalars n K) (scalars n K') (slCongr e) (by
    rw [scalars_eq_center, scalars_eq_center]
    exact CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (slCongr e))

variable {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem conjAut_mem_range_conj (hK : Nat.card K = 9) (A : GL (Fin 3) K) :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, hK]
    norm_num
  set μ : Kˣ := (powCoprime hcop).symm (GeneralLinearGroup.det A)
  have hμ : μ ^ 3 = GeneralLinearGroup.det A := by
    rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]
  set B := (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * A with hB
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, map_inv]
    have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) μ) = μ ^ 3 := by
      ext
      simp [GeneralLinearGroup.scalar]
    rw [this, hμ, inv_mul_cancel]
  have hBmem : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hdetB
    simpa using this
  let g : SpecialLinearGroup (Fin 3) K := ⟨(B : Matrix (Fin 3) (Fin 3) K), hBmem⟩
  refine ⟨proj 3 K g, ?_⟩
  rw [← conjAut_toGL]
  have hAB : A = GeneralLinearGroup.scalar (Fin 3) μ * B := by rw [hB]; group
  have hg : SpecialLinearGroup.toGL g = B := by
    ext1
    rfl
  rw [hg]
  conv_rhs => rw [hAB, map_mul, conjAut_scalar, one_mul]

theorem card_mulAut_projectiveSL_le (hK : Nat.card K = 9) :
    Nat.card (MulAut (projectiveSL 3 K)) ≤ 4 * Nat.card (projectiveSL 3 K) := by
  classical
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  have hRA : Nat.card (K ≃+* K) = 2 :=
    (card_ringAut_and_isCyclic Nat.prime_three K (by rw [hK]; norm_num)).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hRA]; norm_num)
  let f : projectiveSL 3 K × (K ≃+* K) × Fin 2 → MulAut (projectiveSL 3 K) :=
    fun x => MulAut.conj x.1 * fieldAut 3 K x.2.1 * dualAut 3 K ^ (x.2.2 : ℕ)
  have hf : Function.Surjective f := by
    intro α
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
    obtain ⟨x, hx⟩ := conjAut_mem_range_conj hK A
    exact ⟨(x, σ, ⟨ε, by omega⟩), by simp only [f, hx]⟩
  calc Nat.card (MulAut (projectiveSL 3 K))
      ≤ Nat.card (projectiveSL 3 K × (K ≃+* K) × Fin 2) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card (projectiveSL 3 K) * 2 * 2 := by
      rw [Nat.card_prod, Nat.card_prod, hRA, Nat.card_fin, mul_assoc]
    _ = 4 * Nat.card (projectiveSL 3 K) := by ring

end CFSG.EvenSmallLie.Child3.SelL39
