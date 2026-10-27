module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GField
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def psiU (σ : F ≃+* F) : SL(3, F) →* SL(3, F) :=
  (SpecialLinearGroup.map σ.toRingHom).comp
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F).toMonoidHom

theorem proj_psiU (σ : F ≃+* F) (g : SL(3, F)) :
    (fieldAut 3 F σ * dualAut 3 F) (LinearFlag.proj 3 F g) =
      LinearFlag.proj 3 F (psiU σ g) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  rfl

theorem coe_psiU (σ : F ≃+* F) (g : SL(3, F)) :
    ((psiU σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ).map σ := by
  have h1 : ((psiU σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      σ.toRingHom.mapMatrix (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F g :
        Matrix (Fin 3) (Fin 3) F) := SpecialLinearGroup.map_apply_coe _ _
  have h2 : (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F g :
      Matrix (Fin 3) (Fin 3) F) = (adjugate (g : Matrix (Fin 3) (Fin 3) F))ᵀ :=
    congrArg transpose (Matrix.SpecialLinearGroup.coe_inv g)
  rw [h1, h2]
  rfl

theorem psiU_fix_iff (σ : F ≃+* F) (hσσ : ∀ x, σ (σ x) = x) (g : SL(3, F)) :
    psiU σ g = g ↔ ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ * g = 1 := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  have hmm : ∀ N : Matrix (Fin 3) (Fin 3) F, (N.map σ).map σ = N := fun N => by
    ext i j; simp [hσσ]
  constructor
  · intro h
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
    simp only [coe_psiU] at h1
    have h2 := congrArg (fun N : Matrix (Fin 3) (Fin 3) F => N.map σ) h1
    simp only [hmm] at h2
    have h3 : adjugate (g : Matrix (Fin 3) (Fin 3) F) =
        ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ := by
      rw [← h2, transpose_transpose]
    rw [← h3, adjugate_mul, hdet, one_smul]
  · intro h
    have h3 : adjugate (g : Matrix (Fin 3) (Fin 3) F) =
        ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ := by
      have h4 := Matrix.inv_eq_left_inv h
      rwa [Matrix.inv_def, hdet, Ring.inverse_one, one_smul] at h4
    apply Subtype.ext
    rw [coe_psiU, h3, transpose_transpose, hmm]

@[expose] def cycM : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def sg1 : Matrix (Fin 3) (Fin 3) F := diagonal ![-1, -1, 1]

@[expose] def sg2 : Matrix (Fin 3) (Fin 3) F := diagonal ![1, -1, -1]

@[expose] def sgnSet : Set SL(3, F) :=
  {g | (g : Matrix (Fin 3) (Fin 3) F) = cycM ∨ (g : Matrix (Fin 3) (Fin 3) F) = sg1 ∨
    (g : Matrix (Fin 3) (Fin 3) F) = sg2}

theorem sgn_map (ρ : F ≃+* F) : ∀ g ∈ (sgnSet : Set SL(3, F)),
    (g : Matrix (Fin 3) (Fin 3) F).map ρ = g := by
  rintro g (h | h | h) <;> rw [h] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cycM, sg1, sg2]

theorem sgn_unitary (σ : F ≃+* F) : ∀ g ∈ (sgnSet : Set SL(3, F)),
    ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ * g = 1 := by
  intro g hg
  rw [sgn_map σ g hg]
  rcases hg with h | h | h <;> rw [h] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cycM, sg1, sg2, Matrix.mul_apply, Fin.sum_univ_three]

theorem sgn_comm (h2 : (2 : F) ≠ 0) (T : Matrix (Fin 3) (Fin 3) F)
    (hT : ∀ g ∈ (sgnSet : Set SL(3, F)),
      T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hc := hT ⟨cycM, by simp [cycM, det_fin_three]⟩ (Or.inl rfl)
  have h1 := hT ⟨sg1, by simp [sg1, det_diagonal, Fin.prod_univ_three]⟩ (Or.inr (Or.inl rfl))
  have h2' := hT ⟨sg2, by simp [sg2, det_diagonal, Fin.prod_univ_three]⟩ (Or.inr (Or.inr rfl))
  simp only at hc h1 h2'
  have z : ∀ a : F, a = -a → a = 0 := fun a h => by
    have h' : (2 : F) * a = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left h2
  have e1 : ∀ i j, T i j * ![-1, -1, (1 : F)] j = ![-1, -1, (1 : F)] i * T i j := fun i j => by
    have h := congrFun (congrFun h1 i) j
    rwa [sg1, mul_diagonal, diagonal_mul] at h
  have e2 : ∀ i j, T i j * ![1, -1, (-1 : F)] j = ![1, -1, (-1 : F)] i * T i j := fun i j => by
    have h := congrFun (congrFun h2' i) j
    rwa [sg2, mul_diagonal, diagonal_mul] at h
  have ec : ∀ i j, (T * (cycM : Matrix (Fin 3) (Fin 3) F)) i j =
      ((cycM : Matrix (Fin 3) (Fin 3) F) * T) i j := fun i j => congrFun (congrFun hc i) j
  have o01 : T 0 1 = 0 := z _ (by have := e2 0 1; simp at this; linear_combination -this)
  have o02 : T 0 2 = 0 := z _ (by have := e1 0 2; simp at this; linear_combination this)
  have o10 : T 1 0 = 0 := z _ (by have := e2 1 0; simp at this; linear_combination this)
  have o12 : T 1 2 = 0 := z _ (by have := e1 1 2; simp at this; linear_combination this)
  have o20 : T 2 0 = 0 := z _ (by have := e1 2 0; simp at this; linear_combination -this)
  have o21 : T 2 1 = 0 := z _ (by have := e1 2 1; simp at this; linear_combination -this)
  have d1 : T 1 1 = T 0 0 := by
    have := ec 0 1
    simp [cycM, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination -this
  have d2 : T 2 2 = T 0 0 := by
    have := ec 1 2; simp [cycM, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination d1 - this
  refine ⟨T 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [o01, o02, o10, o12, o20, o21, d1, d2]

@[expose] noncomputable def diagU (x : F) : Matrix (Fin 3) (Fin 3) F := diagonal ![x, x⁻¹, 1]

theorem diagU_det {x : F} (hx : x ≠ 0) : (diagU x).det = 1 := by
  simp [diagU, det_diagonal, Fin.prod_univ_three, hx]

theorem diagU_unitary (σ : F ≃+* F) {q : ℕ} (hσ : ∀ y, σ y = y ^ q) {x : F}
    (hx : x ^ (q + 1) = 1) : ((diagU x).map σ)ᵀ * diagU x = 1 := by
  rw [diagU, diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change σ x * x = 1
    rw [hσ, ← pow_succ, hx]
  · change σ x⁻¹ * x⁻¹ = 1
    rw [map_inv₀, hσ, ← mul_inv, ← pow_succ, hx, inv_one]
  · change σ 1 * 1 = 1
    rw [map_one, one_mul]

variable [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]

theorem mem_suRange_iff (hF : Nat.card F = (p ^ e) ^ 2) {σ : F ≃+* F}
    (hσ : ∀ x, σ x = x ^ p ^ e) (g : SL(3, F)) :
    g ∈ (Odd87.suSL (F := F) (p ^ e)).range ↔
      ((g : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ * g = 1 := by
  have hσ' : σ = unitaryInvolution F p e :=
    RingEquiv.ext fun x => by rw [hσ, unitaryInvolution_apply]
  rw [hσ']
  constructor
  · rintro ⟨B, rfl⟩
    have hmem : (B : GL (Fin 3) F) ∈ SUid (unitaryInvolution F p e) 3 := by
      rw [SUid_eq_statedSU hF 3]; exact B.2
    exact hmem.2
  · intro h
    have hmem : Matrix.SpecialLinearGroup.toGL g ∈ StatedSU 3 (p ^ e) F := by
      rw [← SUid_eq_statedSU hF 3]
      exact ⟨g.2, h⟩
    exact ⟨⟨_, hmem⟩, Subtype.ext rfl⟩

end CFSG.GH74.Generic.BProg.B3.S3T5L3
