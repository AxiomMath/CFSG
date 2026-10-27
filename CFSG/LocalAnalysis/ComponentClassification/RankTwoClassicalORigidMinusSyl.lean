module

public import CFSG.LieType.BorelTits.OrthogonalEichler
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

section Vectors

variable {K : Type} [Field K] {n : ℕ}

@[expose] def maniso (z : Fin 2 → K) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K
  | .inr (.inr t) => z t
  | _ => 0

@[simp] theorem maniso_inl (z : Fin 2 → K) (i : Fin (n - 1)) : maniso (n := n) z (.inl i) = 0 :=
  rfl

@[simp] theorem maniso_inr_inl (z : Fin 2 → K) (i : Fin (n - 1)) :
    maniso (n := n) z (.inr (.inl i)) = 0 :=
  rfl

@[simp] theorem maniso_inr_inr (z : Fin 2 → K) (t : Fin 2) :
    maniso (n := n) z (.inr (.inr t)) = z t :=
  rfl

theorem maniso_add (z z' : Fin 2 → K) : maniso (n := n) (z + z') = maniso z + maniso z' := by
  funext i
  rcases i with i | i | t <;> simp

theorem statedQuadMinus_maniso (b c : K) (z : Fin 2 → K) :
    StatedQuadMinus n K b c (maniso z) = z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2 := by
  simp [StatedQuadMinus]

theorem statedQuadMinus_maniso_ne_zero {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z : Fin 2 → K} (hz : z ≠ 0) : StatedQuadMinus n K b c (maniso z) ≠ 0 := by
  rw [statedQuadMinus_maniso]
  intro h
  by_cases h1 : z 1 = 0
  · have h0 : z 0 = 0 := by
      rw [h1] at h
      simpa using h
    exact hz (funext fun t => by fin_cases t <;> simp [h0, h1])
  · apply hirr (z 0 / z 1)
    field_simp
    linear_combination h

end Vectors

section Polar

variable {K : Type} [Field K] {n : ℕ} (b c : K)

theorem quadMinusPolar_single_inl (i : Fin (n - 1)) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    quadMinusPolar n K b c (Pi.single (.inl i) 1) v = v (.inr (.inl i)) := by
  simp [quadMinusPolar, Pi.single_apply, Finset.sum_ite_eq']

theorem quadMinusPolar_single_inr_inl (i : Fin (n - 1))
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    quadMinusPolar n K b c (Pi.single (.inr (.inl i)) 1) v = v (.inl i) := by
  simp [quadMinusPolar, Pi.single_apply, Finset.sum_ite_eq']

theorem quadMinusPolar_maniso [CharP K 2] (z : Fin 2 → K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    quadMinusPolar n K b c (maniso z) v =
      b * (z 0 * v (.inr (.inr 1)) + v (.inr (.inr 0)) * z 1) := by
  simp [quadMinusPolar, CharTwo.two_eq_zero]

end Polar

section Eichler

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

omit [CharP K 2] in
theorem exists_mem_statedOmega_eichler_maniso {e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (he : StatedQuadMinus n K b c e = 0) (z : Fin 2 → K)
    (hez : quadMinusPolar n K b c e (maniso z) = 0) :
    ∃ A ∈ StatedOmega (StatedQuadMinus n K b c), ∀ v,
      (A : Matrix _ _ K) *ᵥ v = (quadMinusForm n K b c hirr).eichler e (maniso z) v := by
  set Φ := quadMinusForm n K b c hirr
  by_cases hz : z = 0
  · refine ⟨1, one_mem _, fun v => ?_⟩
    rw [hz, show maniso (n := n) (0 : Fin 2 → K) = 0 from funext fun j => by
      rcases j with j | j | t <;> rfl, Φ.eichler_zero_right, Units.val_one, one_mulVec]
  · obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler_smul' Φ he hez
      (statedQuadMinus_maniso_ne_zero hirr hz) 1
    exact ⟨A, hA, fun v => by rw [hAv, one_smul]⟩

omit [Finite K] [CharP K 2] in
theorem statedQuadMinus_single_inl (i : Fin (n - 1)) :
    StatedQuadMinus n K b c (Pi.single (.inl i) 1) = 0 := by
  simp [StatedQuadMinus, Pi.single_apply]

omit [Finite K] [CharP K 2] in
theorem statedQuadMinus_single_inr_inl (i : Fin (n - 1)) :
    StatedQuadMinus n K b c (Pi.single (.inr (.inl i)) 1) = 0 := by
  simp [StatedQuadMinus, Pi.single_apply]

end Eichler

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

abbrev mx₄ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K := Pi.single (.inl 0) 1

omit [CharP K 2] in
theorem quad_mx₄ : (quadMinusForm 2 K b c hirr).Q mx₄ = 0 := by
  change StatedQuadMinus 2 K b c _ = 0
  simp [StatedQuadMinus, Pi.single_apply]

omit [CharP K 2] in
theorem polar_mx₄_maniso (z : Fin 2 → K) :
    (quadMinusForm 2 K b c hirr).polar.β mx₄ (maniso z) = 0 := by
  change quadMinusPolar 2 K b c _ _ = 0
  rw [quadMinusPolar_single_inl, maniso_inr_inl]

@[expose] noncomputable def eichMat₄ (z : Fin 2 → K) :
    Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K :=
  LinearMap.toMatrix' ((quadMinusForm 2 K b c hirr).eichler mx₄ (maniso z))

omit [CharP K 2] in
theorem eichMat₄_mulVec (z : Fin 2 → K) (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    eichMat₄ hirr z *ᵥ v = (quadMinusForm 2 K b c hirr).eichler mx₄ (maniso z) v :=
  LinearMap.toMatrix'_mulVec _ v

omit [CharP K 2] in
theorem eichMat₄_add (z z' : Fin 2 → K) :
    eichMat₄ hirr z * eichMat₄ hirr z' = eichMat₄ hirr (z + z') := by
  rw [eichMat₄, eichMat₄, eichMat₄, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, (quadMinusForm 2 K b c hirr).eichler_eichler (quad_mx₄ hirr)
    (polar_mx₄_maniso hirr z) (polar_mx₄_maniso hirr z'), maniso_add]

omit [CharP K 2] in
theorem eichMat₄_zero : eichMat₄ hirr (0 : Fin 2 → K) = 1 := by
  rw [eichMat₄, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [show maniso (n := 2) (0 : Fin 2 → K) = 0 from funext fun j => by
      rcases j with j | j | t <;> rfl,
    (quadMinusForm 2 K b c hirr).eichler_zero_right, LinearMap.id_apply]

@[expose] noncomputable def eichGL₄ (z : Fin 2 → K) :
    GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K :=
  ⟨eichMat₄ hirr z, eichMat₄ hirr (-z), by rw [eichMat₄_add, add_neg_cancel, eichMat₄_zero],
    by rw [eichMat₄_add, neg_add_cancel, eichMat₄_zero]⟩

@[expose] noncomputable def eichHom₄ : Multiplicative (Fin 2 → K) →*
    GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K where
  toFun z := eichGL₄ hirr z.toAdd
  map_one' := Units.ext (eichMat₄_zero hirr)
  map_mul' z z' := Units.ext (eichMat₄_add hirr z.toAdd z'.toAdd).symm

omit [CharP K 2] in
theorem eichler_mx₄_apply_inr_inr (w : Fin 2 → K) (t : Fin 2) :
    (quadMinusForm 2 K b c hirr).eichler mx₄ (maniso w)
      (Pi.single (Sum.inr (Sum.inl 0)) 1) (.inr (.inr t)) = w t := by
  rw [QuadForm.eichler_apply]
  change ((Pi.single (Sum.inr (Sum.inl 0)) 1 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) +
    quadMinusPolar 2 K b c mx₄ (Pi.single (Sum.inr (Sum.inl 0)) 1) •
      (maniso w - StatedQuadMinus 2 K b c (maniso w) • mx₄) -
    quadMinusPolar 2 K b c (maniso w) (Pi.single (Sum.inr (Sum.inl 0)) 1) • mx₄ :
      Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) (.inr (.inr t)) = w t
  rw [quadMinusPolar_single_inl]
  simp [maniso]

omit [CharP K 2] in
theorem eichHom₄_injective : Function.Injective (eichHom₄ hirr) := by
  intro z z' h
  have h2 : eichMat₄ hirr (Multiplicative.toAdd z) = eichMat₄ hirr (Multiplicative.toAdd z') :=
    congrArg (fun g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K =>
      (g : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) h
  apply Multiplicative.toAdd.injective
  funext t
  have h3 := congrFun (congrArg (fun M => M *ᵥ
    (Pi.single (Sum.inr (Sum.inl 0)) (1 : K) : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K)) h2)
    (.inr (.inr t))
  simp only [eichMat₄_mulVec, eichler_mx₄_apply_inr_inr] at h3
  exact h3

include hirr in
theorem exists_isPGroup_statedOmega_quadMinus_two :
    ∃ S : Subgroup (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K),
      S ≤ StatedOmega (StatedQuadMinus 2 K b c) ∧ IsPGroup 2 S ∧
        Nat.card S = Nat.card K ^ 2 := by
  refine ⟨(eichHom₄ hirr).range, ?_, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler_maniso (n := 2) hirr
      (statedQuadMinus_single_inl 0) z.toAdd (polar_mx₄_maniso hirr z.toAdd)
    have hAe : A = eichHom₄ hirr z := by
      apply Units.ext
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hAv]
      exact (eichMat₄_mulVec hirr z.toAdd v).symm
    rw [← hAe]
    exact hA
  · rintro ⟨_, z, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one, ← map_mul]
    apply Units.ext
    change eichMat₄ hirr (z * z).toAdd = 1
    rw [toAdd_mul, CharTwo.add_self_eq_zero, eichMat₄_zero]
  · rw [Nat.card_congr (MonoidHom.ofInjective (eichHom₄_injective hirr)).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
    simp

end Sylow

end CFSG.ComponentClassification.RankTwoClassical.ORigid
