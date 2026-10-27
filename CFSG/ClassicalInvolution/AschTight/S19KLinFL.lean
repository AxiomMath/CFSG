module

public import CFSG.ClassicalInvolution.AschTight.S19KLin

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem conj_eq_of_isBlockDiag {G : GL (Fin 3) F} (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F))
    {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlockScalar M) :
    (G : Matrix (Fin 3) (Fin 3) F) * M * ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := by
  rw [commute_of_isBlockDiag hG hM, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem lift_apply_of_mem_centralizer {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} {ε : Bool}
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F)) {x : SL(3, F)}
    (hx : x ∈ Subgroup.centralizer (Models.rootSL2 F (n := 3) (by norm_num) : Set SL(3, F))) :
    α x = if ε then x⁻¹ else x := by
  have hx1 := isBlockScalar_of_mem_centralizer hx
  have hx2 := isBlockScalar_of_mem_centralizer (Subgroup.inv_mem _ hx)
  apply Subtype.ext
  rw [hform]
  cases ε
  · exact conj_eq_of_isBlockDiag hG hx1
  · show (G : Matrix (Fin 3) (Fin 3) F) *
      (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose *
      ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [transpose_eq_of_isBlockScalar hx2, conj_eq_of_isBlockDiag hG hx2]
    rfl

variable [Finite F]

theorem lin_centralizer {E : Type} [Group E] (θ : SL(3, F) →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (h4 : 4 ≤ Nat.card F) {φ : MulAut E}
    {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} {ε : Bool} (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F)) (hodd : Odd (Nat.card F)) :
    ∀ c ∈ Subgroup.centralizer
      (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
      φ c = if ε then c⁻¹ else c := by
  intro c hc
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  have : Group.IsPerfect (Models.rootSL2 F (n := 3) (by norm_num)) :=
    (Models.isClassicalSL2_rootSL2 (K := F) h2 (n := 3) (by norm_num)).isPerfect h4
  obtain ⟨x, rfl⟩ := hθ c
  have hx := mem_centralizer_of_map θ hker hc
  rw [← hα, lift_apply_of_mem_centralizer hform hG hx]
  cases ε <;> simp

omit [Finite F] in
theorem lin_inner {E : Type} [Group E] (θ : SL(3, F) →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {φ : MulAut E} {α : SL(3, F) →* SL(3, F)}
    {G : GL (Fin 3) F} (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist false x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hφ2 : φ * φ = 1) : ∃ y : E, φ = MulAut.conj y := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hσσ : ∀ x, φ (φ x) = x := fun x => by rw [← MulAut.mul_apply, hφ2, MulAut.one_apply]
  have hαα := ModelFacts.UnitaryAut.lift_comp_self_eq_id hker hσσ hα
  set Gm := (G : Matrix (Fin 3) (Fin 3) F)
  set Gi := ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hGi : Gi * Gm = 1 := Units.inv_mul G
  have hGi' : Gm * Gi = 1 := Units.mul_inv G
  have hcomm : ∀ x : SL(3, F), (Gm * Gm) * (x : Matrix (Fin 3) (Fin 3) F) =
      (x : Matrix (Fin 3) (Fin 3) F) * (Gm * Gm) := by
    intro x
    have h1 := congrArg (fun y : SL(3, F) => (y : Matrix (Fin 3) (Fin 3) F))
      (DFunLike.congr_fun hαα x)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [hform] at h1
    change Gm * ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Gi = x at h1
    rw [hform] at h1
    change Gm * (Gm * (x : Matrix (Fin 3) (Fin 3) F) * Gi) * Gi = x at h1
    have hII : Gi * Gi * (Gm * Gm) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gi Gm Gm, hGi, Matrix.one_mul, hGi]
    calc Gm * Gm * (x : Matrix (Fin 3) (Fin 3) F) =
        Gm * Gm * (x : Matrix (Fin 3) (Fin 3) F) * (Gi * Gi * (Gm * Gm)) := by
          rw [hII, Matrix.mul_one]
      _ = (Gm * (Gm * (x : Matrix (Fin 3) (Fin 3) F) * Gi) * Gi) * (Gm * Gm) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := Gm * Gm)
    fun t => (hcomm t.toSpecialLinearGroup).symm
  have hdet0 : Gm.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hGi'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : Gm.det ^ 2 = s ^ 3 := by
    have := congrArg Matrix.det hs
    rw [Matrix.det_mul, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three] at this
    rw [pow_two, ← this]
    ring
  have hs0 : s ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hdet
    exact hdet0 (pow_eq_zero_iff (by norm_num) |>.mp hdet)
  set ν := Gm.det / s with hνdef
  have hν3 : ν ^ 3 = Gm.det := div_pow_three_eq hs0 hdet
  have hν0 : ν ≠ 0 := div_ne_zero hdet0 hs0
  let y₀ : SL(3, F) := ⟨ν⁻¹ • Gm, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hν3, inv_mul_cancel₀ hdet0]⟩
  have hy : ∀ x, α x = y₀ * x * y₀⁻¹ := by
    intro x
    refine eq_mul_inv_of_mul_eq (Subtype.ext ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hform]
    change Gm * (x : Matrix (Fin 3) (Fin 3) F) * Gi * (ν⁻¹ • Gm) =
      (ν⁻¹ • Gm) * (x : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hGi, Matrix.mul_one]
  exact ⟨θ y₀, eq_conj_of_lift θ hθ hα hy⟩

theorem flLin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ) ≃* SL(2, F))
        (g : GL (Fin 2) F),
      ∀ x : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ)) : E) = φ x) :
    ((∀ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E), φ c = c) ∨
      (∀ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
          φ c = c⁻¹)) ∧
    (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
          φ c = c ∧ c * c ≠ 1) → ∃ y : E, φ = MulAut.conj y) := by
  obtain ⟨α, G, ε, hα, hform, hG⟩ := lin_lift_data hodd h5 hcl θ hθ hker φ hφ
  have hC := lin_centralizer θ hθ hker (by omega) hα hform hG hodd
  refine ⟨?_, fun hφ2 ⟨c, hc, hφc, hcc⟩ => ?_⟩
  · cases ε
    · exact Or.inl fun c hc => by simpa using hC c hc
    · exact Or.inr fun c hc => by simpa using hC c hc
  · cases ε
    · exact lin_inner θ hθ hker hα hform hφ2
    · have h1 : φ c = c⁻¹ := by simpa using hC c hc
      rw [hφc] at h1
      refine absurd ?_ hcc
      calc c * c = c * c⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel c

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
