module

public import CFSG.ClassicalInvolution.AschTight.S19KUniFL
public import CFSG.ClassicalInvolution.AschTight.S19KUni

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem uni_inner (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f) {E : Type}
    [Group E] (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) {φ : MulAut E}
    {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K} (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) *
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hiso : conjTr (unitaryInvolution K p f) (G : Matrix (Fin 3) (Fin 3) K) *
      (G : Matrix (Fin 3) (Fin 3) K) = 1)
    (hφ2 : φ * φ = 1) : ∃ y : E, φ = MulAut.conj y := by
  set σ := unitaryInvolution K p f
  have : Group.IsPerfect (Phan.Su K p f 3) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
      fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
        (Models.prime_pow_ne_two_of_ne_two hp f)
  have hσσ : ∀ x, φ (φ x) = x := fun x => by rw [← MulAut.mul_apply, hφ2, MulAut.one_apply]
  have hαα := ModelFacts.UnitaryAut.lift_comp_self_eq_id hker hσσ hα
  set Gm := (G : Matrix (Fin 3) (Fin 3) K)
  set Gi := ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hGi : Gi * Gm = 1 := Units.inv_mul G
  have hGi' : Gm * Gi = 1 := Units.mul_inv G
  have hII : Gi * Gi * (Gm * Gm) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gi Gm Gm, hGi, Matrix.one_mul, hGi]
  have hcomm : ∀ x : Phan.Su K p f 3, (Gm * Gm) *
      (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (Gm * Gm) := by
    intro x
    have h1 := congrArg (fun y : Phan.Su K p f 3 =>
      (((y : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (DFunLike.congr_fun hαα x)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [hform, hform] at h1
    calc Gm * Gm * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Gm * Gm * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (Gi * Gi * (Gm * Gm)) := by rw [hII, Matrix.mul_one]
      _ = (Gm * (Gm * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Gi) * Gi) * (Gm * Gm) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨s, hs⟩ := ModelFacts.UnitaryAut.eq_smul_one_of_commute h hp (le_refl 3) (Gm * Gm)
    fun y hy => by
      have hy' : y ∈ SUid σ 3 := by rw [SUid_eq_statedSU hK]; exact hy
      exact hcomm ⟨y, hy'⟩
  have hdet0 : Gm.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hGi'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : Gm.det ^ 2 = s ^ 3 := by
    have := congrArg Matrix.det hs
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
    rw [pow_two, this]
  have hs0 : s ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hdet
    exact hdet0 (pow_eq_zero_iff (by norm_num) |>.mp hdet)
  have hNdet : σ Gm.det * Gm.det = 1 := by
    have := congrArg Matrix.det hiso
    rw [Matrix.det_mul, conjTr, Matrix.det_transpose, Matrix.det_one] at this
    have e : σ Gm.det = (Gm.map σ).det := by
      rw [← RingEquiv.coe_toRingHom, RingHom.map_det]
      rfl
    rw [e]
    exact this
  have hNs : σ s * s = 1 := by
    have e1 : conjTr σ (Gm * Gm) * (Gm * Gm) = 1 := by
      rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ Gm) Gm Gm, hiso,
        Matrix.one_mul, hiso]
    rw [hs, conjTr_smul, conjTr_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul] at e1
    have := congrFun (congrFun e1 0) 0
    simpa using this
  set ν := Gm.det / s with hνdef
  have hν3 : ν ^ 3 = Gm.det := div_pow_three_eq hs0 hdet
  have hν0 : ν ≠ 0 := div_ne_zero hdet0 hs0
  have hNν : σ ν⁻¹ * ν⁻¹ = 1 := by
    rw [hνdef, inv_div, map_div₀, div_mul_div_comm, hNs, hNdet, div_one]
  let y₁ : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν⁻¹ (inv_ne_zero hν0)) * G
  have hy₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) = ν⁻¹ • Gm := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_mk0]
  have hy₁mem : y₁ ∈ SUid σ 3 := by
    refine mem_SUid.mpr ⟨?_, ?_⟩
    · rw [hy₁, Matrix.det_smul, Fintype.card_fin, inv_pow, hν3, inv_mul_cancel₀ hdet0]
    · rw [hy₁, conjTr_smul, Matrix.smul_mul, Matrix.mul_smul, hiso, smul_smul, hNν, one_smul]
  let y₀ : Phan.Su K p f 3 := ⟨y₁, hy₁mem⟩
  have hy : ∀ x, α x = y₀ * x * y₀⁻¹ := by
    intro x
    refine eq_mul_inv_of_mul_eq (Subtype.ext (Units.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hform]
    change Gm * (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Gi *
      (y₁ : Matrix (Fin 3) (Fin 3) K) =
      (y₁ : Matrix (Fin 3) (Fin 3) K) *
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hy₁, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hGi, Matrix.mul_one]
  exact ⟨θ y₀, eq_conj_of_lift θ hθ hα hy⟩

theorem flUni (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = p ^ f) {E : Type} [Group E]
    (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((rootU K p f).map θ) ≃* SL(2, F')) (g : GL (Fin 2) F'),
      ∀ x : ↥((rootU K p f).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((rootU K p f).map θ)) : E) = φ x) :
    ((∀ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E), φ c = c) ∨
      (∀ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E), φ c = c⁻¹)) ∧
    (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E),
        φ c = c ∧ c * c ≠ 1) → ∃ y : E, φ = MulAut.conj y) := by
  obtain ⟨α, G, τ, hα, hform, hiso, hG, hτ⟩ := uni_lift_data hK hp hq hF' θ hθ hker φ hφ
  obtain ⟨hC1, hC2⟩ := uni_centralizer hK hp hq θ hθ hker hα hform hG
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  refine ⟨hτ.imp hC1 hC2, fun hφ2 ⟨c, hc, hφc, hcc⟩ => ?_⟩
  rcases hτ with h | h
  · subst h
    refine uni_inner hK hp hf θ hθ hker hα (fun x => ?_) hiso hφ2
    rw [hform, RingEquiv.mapMatrix_refl]
    rfl
  · have h1 := hC2 h c hc
    rw [hφc] at h1
    refine absurd ?_ hcc
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel c

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
