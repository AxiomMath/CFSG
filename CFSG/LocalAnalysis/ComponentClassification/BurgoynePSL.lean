module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit CFSG.Blueprint
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem inv_transpose_of_transpose_eq (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (A⁻¹ : GL (Fin n) K) :=
  CFSG.ComponentClassification.CatalogueBLinearHigherB.transpose_inv_of_transpose_eq A hA

theorem conjAut_mul_conjAut_dualAut_mul_inv (H A : GL (Fin n) K) :
    conjAut n K H * (conjAut n K A * dualAut n K) * (conjAut n K H)⁻¹ =
      conjAut n K (H * A * GeneralLinearGroup.inverseTranspose H⁻¹) * dualAut n K := by
  calc conjAut n K H * (conjAut n K A * dualAut n K) * (conjAut n K H)⁻¹
      = conjAut n K H * conjAut n K A * (dualAut n K * conjAut n K H⁻¹) := by
        rw [← map_inv]
        group
    _ = conjAut n K H * conjAut n K A *
        (conjAut n K (GeneralLinearGroup.inverseTranspose H⁻¹) * dualAut n K) := by
        rw [LocalAnalysis.ComponentInitial.LinearFlag.dualAut_mul_conjAut]
    _ = _ := by rw [map_mul, map_mul]; group

theorem orthogonal_eq_bot [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL n K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range)
    {t : X} {A : GL (Fin n) K} (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A)
    (htA : ψ t = conjAut n K A * dualAut n K) {Y : Subgroup X}
    (hYO : Y ≤ oddCentralizerCore t) : Y = ⊥ := by
  have hR := inv_transpose_of_transpose_eq A hA
  obtain ⟨P, w, hw, hP⟩ := exists_orth_normal_form hK hn A⁻¹ hR
  set H := P⁻¹ with hH
  have hHA : H * A * GeneralLinearGroup.inverseTranspose H⁻¹ = (diagGL hw.1)⁻¹ := by
    have hT : CatalogueBGraphForm.glTranspose n K P * A⁻¹ * P = diagGL hw.1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, coe_diagGL]
      exact hP
    have hT' : CatalogueBGraphForm.glTranspose n K P =
        (GeneralLinearGroup.inverseTranspose P)⁻¹ := rfl
    rw [← hT, hT', hH, inv_inv]
    group
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut n K H)
  set ψ' := (MulAut.conj (conjAut n K H)).toMonoidHom.comp ψ with hψ'def
  have hψ't : ψ' t = conjAut n K (diagGL hw.1)⁻¹ * dualAut n K := by
    change conjAut n K H * ψ t * (conjAut n K H)⁻¹ = _
    rw [htA, conjAut_mul_conjAut_dualAut_mul_inv, hHA]
  refine eq_bot_of_oddCoreIn hinj' ?_ hYO
  rw [hψ't]
  by_cases hexc : Nat.card K = 3 ∧ n ≤ 4
  · exact orth_oddCoreIn_eq_bot_three hexc.1 hn hexc.2 hInn' hw.1
  · have hRsym : ((diagGL hw.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = diagGL hw.1 := by
      rw [coe_diagGL, diagonal_transpose]
    exact orth_oddCoreIn_eq_bot_of_data hK hn hinj hInn' hw
      (orthComponentData hK hn _ hRsym hexc)

theorem conj_injective_of_mulEquiv {X : Type} [Group X] {T : Type*} [Group T]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* T) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hcomm : ∀ y : T, x * y = y * x := by
    intro y
    have := congrArg (fun α : MulAut T => α y) (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hcenter : center (GeneralizedFitting.subgroup X) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center _) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
  have hz : θ.symm x ∈ center (GeneralizedFitting.subgroup X) := by
    rw [mem_center_iff]
    intro g
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (hcomm (θ g)).symm
  rw [hcenter, mem_bot] at hz
  rw [← θ.apply_symm_apply x, hz, map_one]

theorem burgoynePropA_PSL (X : Type) [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSL n p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, hnot2, -⟩ := hX
  obtain ⟨hp, hf, hn2⟩ : p.Prime ∧ 1 ≤ f ∧ 2 ≤ n := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hn : 3 ≤ n := by
    by_contra hn
    have h2 : n = 2 := by omega
    subst h2
    exact hnot2 p f hp hp2 hL
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set ψ := socleAction θ with hψdef
  have hψ : Function.Injective ψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hsq : ψ t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 (ψ t)
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      exact inner_propAConclusion hK hn hinj hψ hInn ht hα hY hYO
    · exact absurd (field_eq_bot hp hp2 hf hKc hn hinj hψ hInn ht hσ hα hYO) hY
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      have hα' : ψ t = conjAut n K A * dualAut n K := by rw [hα, map_one, mul_one]
      have hsq' : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1 := by
        rw [← hα]
        exact hsq
      rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq hn A
          hsq' with hA | hA
      · exact absurd (orthogonal_eq_bot hK hn hinj hψ hInn hA hα' hYO) hY
      · refine absurd (eq_bot_of_oddCoreIn hψ ?_ hYO) hY
        rw [hα']
        exact symplectic_oddCoreIn_eq_bot hK hn hinj hInn hA
    · exact absurd (graphField_eq_bot hp hp2 hf hKc hn hinj hψ hInn ht hσ hα hYO) hY

end CFSG.ComponentClassification.Burgoyne.PSL
