module

public import CFSG.ClassicalInvolution.AschTight.S19KGen
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem conjTr_smul {K : Type} [Field K] (σ : K ≃+* K) {n : ℕ} (c : K)
    (M : Matrix (Fin n) (Fin n) K) : conjTr σ (c • M) = σ c • conjTr σ M := by
  ext i j
  simp [conjTr]

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_eq_inv {n : ℕ} (x : Phan.Su K p f n) :
    conjTr (unitaryInvolution K p f) (((x : Phan.Su K p f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (((x⁻¹ : Phan.Su K p f n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
  have h1 := (mem_SUid.mp x.2).2
  have h2 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((x⁻¹ : Phan.Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  calc conjTr (unitaryInvolution K p f) (((x : Phan.Su K p f n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      conjTr (unitaryInvolution K p f) ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((x⁻¹ : Phan.Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [h2, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem uni_lift_apply_of_mem_centralizer (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 2 ≤ p ^ f) {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K} {τ : K ≃+* K}
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) *
        τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K)) {x : Phan.Su K p f 3}
    (hx : x ∈ Subgroup.centralizer (rootU K p f : Set (Phan.Su K p f 3))) :
    (τ = RingEquiv.refl K → α x = x) ∧ (τ = unitaryInvolution K p f → α x = x⁻¹) := by
  have hx1 := isBlockScalar_of_mem_centralizerU hK hp hq hx
  have hx2 := isBlockScalar_of_mem_centralizerU hK hp hq (Subgroup.inv_mem _ hx)
  have hGc : ∀ {M : Matrix (Fin 3) (Fin 3) K}, IsBlockScalar M →
      (G : Matrix (Fin 3) (Fin 3) K) * M * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        M := fun hM => by
    rw [commute_of_isBlockDiag hG hM, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · subst hτ
    apply Subtype.ext
    apply Units.ext
    rw [hform, RingEquiv.mapMatrix_refl]
    exact hGc hx1
  · subst hτ
    apply Subtype.ext
    apply Units.ext
    rw [hform]
    have h1 : (unitaryInvolution K p f).mapMatrix
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((x⁻¹ : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← transpose_eq_of_isBlockScalar hx2, ← conjTr_eq_inv, conjTr, RingEquiv.mapMatrix_apply,
        Matrix.transpose_transpose]
    rw [h1]
    exact hGc hx2

theorem uni_centralizer (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {E : Type} [Group E] (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) {φ : MulAut E}
    {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K} {τ : K ≃+* K}
    (hα : ∀ x, θ (α x) = φ (θ x))
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) *
        τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K)) :
    (τ = RingEquiv.refl K →
      ∀ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E), φ c = c) ∧
    (τ = unitaryInvolution K p f →
      ∀ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E), φ c = c⁻¹) := by
  have hcl2 := Models.isClassicalSL2_rootSU2 (K := K) (p := p) (f := f) hK hp (n := 3)
    (by norm_num)
  have : Group.IsPerfect (rootU K p f) :=
    hcl2.isPerfect (by rw [card_fixedSubfield hK]; omega)
  have key : ∀ c ∈ Subgroup.centralizer (((rootU K p f).map θ : Subgroup E) : Set E),
      ∃ x, θ x = c ∧ (τ = RingEquiv.refl K → α x = x) ∧
        (τ = unitaryInvolution K p f → α x = x⁻¹) := by
    intro c hc
    obtain ⟨x, rfl⟩ := hθ c
    exact ⟨x, rfl, uni_lift_apply_of_mem_centralizer hK hp (by omega) hform hG
      (mem_centralizer_of_map θ hker hc)⟩
  refine ⟨fun hτ c hc => ?_, fun hτ c hc => ?_⟩
  · obtain ⟨x, rfl, h1, -⟩ := key c hc
    rw [← hα, h1 hτ]
  · obtain ⟨x, rfl, -, h2⟩ := key c hc
    rw [← hα, h2 hτ, map_inv]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
