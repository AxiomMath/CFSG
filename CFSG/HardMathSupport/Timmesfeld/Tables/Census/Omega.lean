module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Klein
public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv Matrix CFSG.Open
open scoped commutatorElement

abbrev P6 : Type := Fin 3 ⊕ Fin 3

@[expose] def tauP (i : Fin 3) : Perm P6 := Equiv.swap (Sum.inl i) (Sum.inr i)

@[expose] def swP (i j : Fin 3) : Perm P6 :=
  Equiv.swap (Sum.inl i) (Sum.inl j) * Equiv.swap (Sum.inr i) (Sum.inr j)

@[expose] def cycP : Perm P6 := Perm.sumCongr (finRotate 3) (finRotate 3)

theorem tauP_rel1 : (tauP 0 * tauP 1) * (tauP 0 * tauP 1) = 1 := by decide +kernel
theorem tauP_rel2 : (tauP 1 * tauP 2) * (tauP 1 * tauP 2) = 1 := by decide +kernel
theorem tauP_rel3 : (tauP 0 * tauP 1) * (tauP 1 * tauP 2) = (tauP 1 * tauP 2) * (tauP 0 * tauP 1) :=
  by decide +kernel
theorem cycP_pow : cycP ^ 3 = 1 := by decide +kernel
theorem cycP_rel1 : cycP * (tauP 0 * tauP 1) * cycP⁻¹ = tauP 1 * tauP 2 := by decide +kernel
theorem cycP_rel2 : cycP * (tauP 1 * tauP 2) * cycP⁻¹ = (tauP 0 * tauP 1) * (tauP 1 * tauP 2) := by
  decide +kernel
theorem tauP_comm1 : tauP 0 * tauP 1 = ⁅swP 0 1, tauP 0⁆ := by decide +kernel
theorem tauP_comm2 : tauP 1 * tauP 2 = ⁅swP 1 2, tauP 1⁆ := by decide +kernel
theorem cycP_comm : cycP = ⁅swP 0 1, swP 0 2⁆ ∨ cycP = ⁅swP 0 2, swP 0 1⁆ := by decide +kernel
theorem tauP_ne_one : tauP 0 * tauP 1 ≠ 1 := by decide +kernel
theorem cycP_ne_one : cycP ≠ 1 := by decide +kernel

@[expose] def PairIso {K : Type} [CommRing K] (π : Perm P6) : Prop :=
  ∀ f : P6 → K, ∑ i : Fin 3, f (π (Sum.inl i)) * f (π (Sum.inr i)) =
    ∑ i : Fin 3, f (Sum.inl i) * f (Sum.inr i)

theorem PairIso.inv {K : Type} [CommRing K] {π : Perm P6} (h : PairIso (K := K) π) :
    PairIso (K := K) π⁻¹ := by
  intro f
  have := h (fun x => f (π⁻¹ x))
  simpa using this.symm

theorem pairIso_tau {K : Type} [CommRing K] (i : Fin 3) : PairIso (K := K) (tauP i) := by
  intro f
  fin_cases i <;> simp [tauP, Fin.sum_univ_three, Equiv.swap_apply_def] <;> ring

theorem pairIso_sw {K : Type} [CommRing K] (i j : Fin 3) : PairIso (K := K) (swP i j) := by
  intro f
  fin_cases i <;> fin_cases j <;>
    simp [swP, Fin.sum_univ_three, Equiv.swap_apply_def] <;> ring

@[expose] noncomputable def permGLι (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Perm ι →* GL ι K :=
  MonoidHom.toHomUnits (Matrix.permMatrixHom (n := ι) (R := K))

theorem coe_permGLι {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (σ : Perm ι) :
    ((permGLι ι K σ : GL ι K) : Matrix ι ι K) = σ⁻¹.permMatrix K := rfl

theorem eq_one_of_permGLι_scalar {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {σ : Perm ι} {c : Kˣ} (h : permGLι ι K σ = Matrix.GeneralLinearGroup.scalar ι c) : σ = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K) (σ i) i) h
  simp only [coe_permGLι, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hi] at h1
  simp [Perm.permMatrix, PEquiv.toMatrix_apply] at h1

section Embed

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] noncomputable def embHom (E : P6 ↪ ι) : Perm P6 →* GL ι K :=
  (permGLι ι K).comp (Perm.viaEmbeddingHom E)

@[expose] def Q3 (E : P6 ↪ ι) (v : ι → K) : K :=
  ∑ i : Fin 3, v (E (Sum.inl i)) * v (E (Sum.inr i))

theorem embHom_isometry (Q : (ι → K) → K) (E : P6 ↪ ι)
    (hQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range E → v a = w a) →
      Q v - Q3 E v = Q w - Q3 E w) {π : Perm P6} (hπ : PairIso (K := K) π) (v : ι → K) :
    Q (((embHom E π : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  have hcoe : ((embHom E π : GL ι K) : Matrix ι ι K) =
      ((Perm.viaEmbedding π E)⁻¹).permMatrix K := coe_permGLι _
  rw [hcoe, Matrix.permMatrix_mulVec]
  have hinv : (Perm.viaEmbedding π E)⁻¹ = Perm.viaEmbedding π⁻¹ E := by
    rw [← Perm.viaEmbeddingHom_apply, ← Perm.viaEmbeddingHom_apply, map_inv]
  rw [hinv]
  have h1 := hQ (v ∘ (Perm.viaEmbedding π⁻¹ E)) v (fun a ha => by
    simp [Perm.viaEmbedding_apply_of_notMem _ _ _ ha])
  have h2 : Q3 E (v ∘ (Perm.viaEmbedding π⁻¹ E)) = Q3 E v := by
    simp only [Q3, Function.comp_apply, Perm.viaEmbedding_apply]
    exact hπ.inv (fun x => v (E x))
  rw [h2] at h1
  exact sub_left_inj.1 h1

theorem embHom_mem_closure (Q : (ι → K) → K) (E : P6 ↪ ι)
    (hQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range E → v a = w a) →
      Q v - Q3 E v = Q w - Q3 E w) {π : Perm P6} (hπ : PairIso (K := K) π) :
    embHom E π ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
  Subgroup.subset_closure (embHom_isometry Q E hQ hπ)

theorem embHom_mem_omega (Q : (ι → K) → K) (E : P6 ↪ ι)
    (hQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range E → v a = w a) →
      Q v - Q3 E v = Q w - Q3 E w) {a b : Perm P6} (ha : PairIso (K := K) a)
    (hb : PairIso (K := K) b) : embHom E ⁅a, b⁆ ∈ StatedOmega Q := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (embHom_mem_closure Q E hQ ha)
    (embHom_mem_closure Q E hQ hb)

theorem embHom_ne_scalar (E : P6 ↪ ι) {π : Perm P6} (hπ : π ≠ 1) (u : Kˣ) :
    Matrix.GeneralLinearGroup.scalar ι u ≠ embHom E π := by
  intro hu
  have h := eq_one_of_permGLι_scalar (K := K) hu.symm
  apply hπ
  apply Perm.viaEmbeddingHom_injective E
  rw [map_one]
  exact h

theorem threeTwoWitness_statedProj_omega [Finite K] (Q : (ι → K) → K) (E : P6 ↪ ι)
    (hQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range E → v a = w a) →
      Q v - Q3 E v = Q w - Q3 E w) : ThreeTwoWitness (StatedProj (StatedOmega Q)) := by
  have iso0 : PairIso (K := K) (tauP 0) := pairIso_tau 0
  have iso1 : PairIso (K := K) (tauP 1) := pairIso_tau 1
  have iso2 : PairIso (K := K) (tauP 2) := pairIso_tau 2
  have hd1 : embHom E (tauP 0 * tauP 1) ∈ StatedOmega Q := by
    rw [tauP_comm1]
    exact embHom_mem_omega Q E hQ (pairIso_sw 0 1) iso0
  have hd2 : embHom E (tauP 1 * tauP 2) ∈ StatedOmega Q := by
    rw [tauP_comm2]
    exact embHom_mem_omega Q E hQ (pairIso_sw 1 2) iso1
  have hc : embHom E cycP ∈ StatedOmega Q := by
    rcases cycP_comm with h | h <;> rw [h] <;>
      exact embHom_mem_omega Q E hQ (pairIso_sw _ _) (pairIso_sw _ _)
  refine threeTwoWitness_statedProj_klein (embHom E (tauP 0 * tauP 1))
    (embHom E (tauP 1 * tauP 2)) (embHom E cycP) hd1 hd2 hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, tauP_rel1, map_one]
  · rw [← map_mul, tauP_rel2, map_one]
  · rw [← map_mul, ← map_mul, tauP_rel3]
  · exact embHom_ne_scalar E tauP_ne_one
  · rw [← map_pow, cycP_pow, map_one]
  · exact embHom_ne_scalar E cycP_ne_one
  · rw [← map_inv, ← map_mul, ← map_mul, cycP_rel1]
  · rw [← map_inv, ← map_mul, ← map_mul, cycP_rel2, map_mul]

end Embed

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
