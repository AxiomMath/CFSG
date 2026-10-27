module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixData
public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.CharacterTheory.SteinbergBY

open Module Matrix FieldFour AlternatingSix

universe u w

section Restriction

variable {F L G M : Type*} [Field F] [Field L] [Algebra F L] [Group G] [AddCommGroup M]
  [Module L M] [Module F M] [IsScalarTower F L M]

theorem isIrreducible_restrictScalarsRep (τ : Representation L G M) (hτ : τ.IsIrreducible)
    (hsmul : ∀ U : Subrepresentation (restrictScalarsRep F τ), ∀ (c : L) (u : M), u ∈ U →
      c • u ∈ U) :
    (restrictScalarsRep F τ).IsIrreducible := by
  let toL : Subrepresentation (restrictScalarsRep F τ) → Subrepresentation τ := fun U =>
    ⟨{ carrier := U
       add_mem' := fun ha hb => U.toSubmodule.add_mem ha hb
       zero_mem' := U.toSubmodule.zero_mem
       smul_mem' := fun c u hu => hsmul U c u hu },
      fun g _ hu => U.apply_mem_toSubmodule g hu⟩
  have := nontrivial_of_isIrreducible τ
  have hbt : (⊥ : Subrepresentation (restrictScalarsRep F τ)) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    have hvtop : v ∈ (⊤ : Subrepresentation (restrictScalarsRep F τ)) := Submodule.mem_top
    rw [← h] at hvtop
    exact hv ((Submodule.mem_bot F).mp hvtop)
  have : Nontrivial (Subrepresentation (restrictScalarsRep F τ)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  rcases hτ.eq_bot_or_eq_top (toL U) with h | h
  · left
    ext u
    refine ⟨fun hu => ?_, fun hu => (Submodule.mem_bot F).mp hu ▸ U.toSubmodule.zero_mem⟩
    have hu' : u ∈ toL U := hu
    rw [h] at hu'
    exact (Submodule.mem_bot F).mpr ((Submodule.mem_bot L).mp hu')
  · right
    ext u
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    have hu' : u ∈ toL U := by rw [h]; exact Submodule.mem_top
    exact hu'

end Restriction

@[expose] noncomputable def restrictFour
    (N : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour) :
    Representation (ZMod 2) (alternatingGroup (Fin 6)) (Fin 8 → FieldFour) :=
  restrictScalarsRep (ZMod 2) (matrixBaseChange (RingHom.id FieldFour) N)

theorem restrictFour_apply (N : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour)
    (g : alternatingGroup (Fin 6)) (x : Fin 8 → FieldFour) : restrictFour N g x = N g *ᵥ x := by
  change (N g).map (RingHom.id FieldFour) *ᵥ x = _
  rw [RingHom.coe_id, Matrix.map_id]

theorem isIrreducible_restrictFour
    (N : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour)
    (hN : (matrixBaseChange (RingHom.id FieldFour) N).IsIrreducible)
    (s : Finset (alternatingGroup (Fin 6))) (c : FieldFour) (hc : c = ω ∨ c = ω₂)
    (hs : ∑ g ∈ s, N g = c • (1 : Matrix (Fin 8) (Fin 8) FieldFour)) :
    (restrictFour N).IsIrreducible := by
  refine isIrreducible_restrictScalarsRep _ hN fun U d u hu => ?_
  have hcu : c • u ∈ U := by
    have h1 : ∑ g ∈ s, restrictFour N g u = c • u := by
      simp only [restrictFour_apply]
      rw [← Matrix.sum_mulVec, hs, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h1]
    exact Submodule.sum_mem _ fun g _ => U.apply_mem_toSubmodule g hu
  have hω₂ : ω₂ • u ∈ U := by
    rcases hc with rfl | rfl
    · have h2 : ω₂ • u = ω • u + u := by
        have : ω₂ = ω + 1 := by decide
        rw [this, add_smul, one_smul]
      rw [h2]
      exact U.toSubmodule.add_mem hcu hu
    · exact hcu
  have h3 : d • u = (reZ d + imZ d) • u + imZ d • (ω₂ • u) := by
    conv_lhs => rw [eq_ofPrime_add_ofPrime_mul d]
    rw [add_smul, mul_smul, ← algebraMap_smul FieldFour (reZ d + imZ d) u,
      ← algebraMap_smul FieldFour (imZ d) (ω₂ • u)]
    rfl
  rw [h3]
  exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hu) (U.toSubmodule.smul_mem _ hω₂)

theorem isIrreducible_restrictFour_rep8a : (restrictFour rep8a).IsIrreducible :=
  isIrreducible_restrictFour rep8a (isIrreducible_rep8a _) omegaClass ω₂ (Or.inr rfl)
    sum_omegaClass_rep8a

@[expose] def frobVecEquiv : (Fin 8 → FieldFour) ≃ₗ[ZMod 2] (Fin 8 → FieldFour) where
  toFun x i := frob (x i)
  invFun x i := frob (x i)
  map_add' x y := funext fun i => map_add frob (x i) (y i)
  map_smul' a x := funext fun i => by
    change frob (a • x i) = a • frob (x i)
    revert a
    generalize x i = y
    revert y
    decide
  left_inv x := funext fun i => frob_frob (x i)
  right_inv x := funext fun i => frob_frob (x i)

@[expose] noncomputable def restrictFourEquiv : (restrictFour rep8a).Equiv (restrictFour rep8b) :=
  Representation.Equiv.mk frobVecEquiv fun g => by
    refine LinearMap.ext fun x => funext fun i => ?_
    show frob ((restrictFour rep8a g x) i) = (restrictFour rep8b g (fun j => frob (x j))) i
    rw [restrictFour_apply, restrictFour_apply]
    show frob ((rep8a g *ᵥ x) i) = ((rep8a g).map frob *ᵥ fun j => frob (x j)) i
    rw [RingHom.map_mulVec]
    rfl

theorem isIrreducible_restrictFour_rep8b : (restrictFour rep8b).IsIrreducible :=
  isIrreducible_of_equiv restrictFourEquiv isIrreducible_restrictFour_rep8a

theorem reZ_mk (a b : ZMod 2) : reZ ⟨decide (a = 1), decide (b = 1)⟩ = a := by
  revert a b
  decide

theorem imZ_mk (a b : ZMod 2) : imZ ⟨decide (a = 1), decide (b = 1)⟩ = b := by
  revert a b
  decide

theorem mk_reZ_imZ (x : FieldFour) :
    (⟨decide (reZ x = 1), decide (imZ x = 1)⟩ : FieldFour) = x := by
  revert x
  decide

@[expose] def fieldFourCoord : FieldFour ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun x := ![reZ x, imZ x]
  invFun v := ⟨decide (v 0 = 1), decide (v 1 = 1)⟩
  map_add' x y := by
    funext i
    fin_cases i
    · exact reZ_add x y
    · exact imZ_add x y
  map_smul' a x := by
    funext i
    fin_cases i
    · exact reZ_smul a x
    · exact imZ_smul a x
  left_inv x := mk_reZ_imZ x
  right_inv v := by
    funext i
    fin_cases i
    · exact reZ_mk (v 0) (v 1)
    · exact imZ_mk (v 0) (v 1)

@[expose] noncomputable def realEquiv : (Fin 8 → FieldFour) ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  (LinearEquiv.piCongrRight fun _ => fieldFourCoord).trans
    ((LinearEquiv.curry (ZMod 2) (ZMod 2) (Fin 8) (Fin 2)).symm.trans
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
        (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin (8 * 2)).symm))

section Closure

variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

@[expose] noncomputable def a6ClosureRep :
    ∀ i : Fin 5, Representation k (alternatingGroup (Fin 6)) (Fin (![1, 4, 4, 8, 8] i) → k)
  | 0 => matrixBaseChange ((toField k).comp ofPrime) rep1
  | 1 => matrixBaseChange ((toField k).comp ofPrime) rep4a
  | 2 => matrixBaseChange ((toField k).comp ofPrime) rep4b
  | 3 => matrixBaseChange (toField k) rep8a
  | 4 => matrixBaseChange (toField k) rep8b

theorem isIrreducible_a6ClosureRep : ∀ i, (a6ClosureRep k i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep1 _
  · exact isIrreducible_rep4a _
  · exact isIrreducible_rep4b _
  · exact isIrreducible_rep8a _
  · exact isIrreducible_rep8b _

theorem trace_a6ClosureRep_one (g : alternatingGroup (Fin 6)) :
    LinearMap.trace k _ (a6ClosureRep k 1 g) = (toField k) (ofPrime (Matrix.trace (rep4a g))) :=
  trace_matrixBaseChange _ rep4a g

theorem trace_a6ClosureRep_two (g : alternatingGroup (Fin 6)) :
    LinearMap.trace k _ (a6ClosureRep k 2 g) = (toField k) (ofPrime (Matrix.trace (rep4b g))) :=
  trace_matrixBaseChange _ rep4b g

theorem trace_a6ClosureRep_three (g : alternatingGroup (Fin 6)) :
    LinearMap.trace k _ (a6ClosureRep k 3 g) = (toField k) (Matrix.trace (rep8a g)) :=
  trace_matrixBaseChange _ rep8a g

theorem trace_a6ClosureRep_four (g : alternatingGroup (Fin 6)) :
    LinearMap.trace k _ (a6ClosureRep k 4 g) = (toField k) (Matrix.trace (rep8b g)) :=
  trace_matrixBaseChange _ rep8b g

theorem isEmpty_equiv_a6ClosureRep (i j : Fin 5) (hij : i ≠ j) :
    IsEmpty ((a6ClosureRep k i).Equiv (a6ClosureRep k j)) := by
  have h12 : (toField k) (ofPrime (Matrix.trace (rep4a threeCycle))) ≠
      (toField k) (ofPrime (Matrix.trace (rep4b threeCycle))) := by
    rw [trace_rep4a_threeCycle, trace_rep4b_threeCycle, map_one, map_zero, map_one, map_zero]
    exact one_ne_zero
  have h34 : (toField k) (Matrix.trace (rep8a fiveCycle)) ≠
      (toField k) (Matrix.trace (rep8b fiveCycle)) := by
    rw [trace_rep8a_fiveCycle, trace_rep8b_fiveCycle]
    exact fun h => ω_ne_ω₂ ((toField k).injective h).symm
  by_cases hd : (![1, 4, 4, 8, 8] : Fin 5 → ℕ) i = ![1, 4, 4, 8, 8] j
  · have hcases : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isEmpty_equiv_of_trace_ne threeCycle (by
        rw [trace_a6ClosureRep_one, trace_a6ClosureRep_two]; exact h12)
    · exact isEmpty_equiv_of_trace_ne threeCycle (by
        rw [trace_a6ClosureRep_one, trace_a6ClosureRep_two]; exact h12.symm)
    · exact isEmpty_equiv_of_trace_ne fiveCycle (by
        rw [trace_a6ClosureRep_three, trace_a6ClosureRep_four]; exact h34)
    · exact isEmpty_equiv_of_trace_ne fiveCycle (by
        rw [trace_a6ClosureRep_three, trace_a6ClosureRep_four]; exact h34.symm)
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

theorem pow_45_eq_one_of_isPRegular (g : alternatingGroup (Fin 6)) (hg : IsPRegular 2 g) :
    g ^ 45 = 1 := by
  have hcard : Fintype.card (alternatingGroup (Fin 6)) = 360 := by
    have h := two_mul_card_alternatingGroup (α := Fin 6)
    have h6 : (Fintype.card (Fin 6)).factorial = 720 := by rw [Fintype.card_fin]; decide
    rw [Fintype.card_perm, h6] at h
    omega
  have hdvd : orderOf g ∣ 45 * 2 ^ 3 := by
    have h1 : orderOf g ∣ Fintype.card (alternatingGroup (Fin 6)) := orderOf_dvd_card
    rw [hcard] at h1
    exact h1
  have hcop : Nat.Coprime (orderOf g) (2 ^ 3) := Nat.Coprime.pow_right 3 hg
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem card_pRegularClass_alternatingGroup_six :
    Fintype.card (PRegularClass 2 (alternatingGroup (Fin 6))) ≤ 5 := by
  classical
  have hrep : ∀ C : PRegularClass 2 (alternatingGroup (Fin 6)), ∃ j : Fin 5,
      ∃ c : alternatingGroup (Fin 6), ∀ x,
        ((PRegularClass.repr C : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
          ((c : Equiv.Perm (Fin 6)) x) = (c : Equiv.Perm (Fin 6)) classReps[j][x] :=
    fun C => exists_conj_classReps _
      (pow_45_eq_one_of_isPRegular _ (PRegularClass.repr_isPRegular C))
  choose j c hc using hrep
  have hconj : ∀ C : PRegularClass 2 (alternatingGroup (Fin 6)), ∀ y,
      (((c C)⁻¹ * PRegularClass.repr C * c C : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) y =
        classReps[j C][y] := by
    intro C y
    change ((c C : Equiv.Perm (Fin 6))).symm
      (((PRegularClass.repr C : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
        ((c C : Equiv.Perm (Fin 6)) y)) = _
    rw [hc C y, Equiv.symm_apply_apply]
  have hinj : Function.Injective j := by
    intro C C' hCC'
    have heq : (c C)⁻¹ * PRegularClass.repr C * c C =
        (c C')⁻¹ * PRegularClass.repr C' * c C' := by
      apply Subtype.ext
      apply Equiv.ext
      intro y
      rw [hconj C y, hconj C' y]
      simp only [hCC']
    have hIsConj : IsConj (PRegularClass.repr C) (PRegularClass.repr C') := by
      rw [isConj_iff]
      refine ⟨c C' * (c C)⁻¹, ?_⟩
      calc c C' * (c C)⁻¹ * PRegularClass.repr C * (c C' * (c C)⁻¹)⁻¹
          = c C' * ((c C)⁻¹ * PRegularClass.repr C * c C) * (c C')⁻¹ := by group
        _ = c C' * ((c C')⁻¹ * PRegularClass.repr C' * c C') * (c C')⁻¹ := by rw [heq]
        _ = PRegularClass.repr C' := by group
    apply PRegularClass.ext
    have h1 : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
    have h2 : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
    rw [← h1, ← h2]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hIsConj
  have := Fintype.card_le_of_injective j hinj
  rwa [Fintype.card_fin] at this

theorem a6ClosureRep_complete (W : Type w) [AddCommGroup W] [Module k W]
    (σ : Representation k (alternatingGroup (Fin 6)) W) (hσ : σ.IsIrreducible) :
    FiniteDimensional k W ∧ ∃ i, Nonempty (σ.Equiv (a6ClosureRep k i)) := by
  have := isIrreducible_a6ClosureRep k
  have := hσ
  exact exists_equiv_of_card_pRegularClass_le 2 _ (a6ClosureRep k)
    (isEmpty_equiv_a6ClosureRep k)
    (card_pRegularClass_alternatingGroup_six.trans (Fintype.card_fin 5).symm.le) W σ

end Closure

@[expose] noncomputable def a6BinaryRep :
    ∀ i : Fin 4,
      Representation (ZMod 2) (alternatingGroup (Fin 6)) (Fin (![1, 4, 4, 16] i) → ZMod 2)
  | 0 => matrixBaseChange (RingHom.id _) rep1
  | 1 => matrixBaseChange (RingHom.id _) rep4a
  | 2 => matrixBaseChange (RingHom.id _) rep4b
  | 3 => transportRep realEquiv (restrictFour rep8a)

theorem isIrreducible_a6BinaryRep : ∀ i, (a6BinaryRep i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep1 _
  · exact isIrreducible_rep4a _
  · exact isIrreducible_rep4b _
  · exact isIrreducible_of_equiv (transportRepEquiv realEquiv _) isIrreducible_restrictFour_rep8a

theorem isEmpty_equiv_a6BinaryRep (i j : Fin 4) (hij : i ≠ j) :
    IsEmpty ((a6BinaryRep i).Equiv (a6BinaryRep j)) := by
  have h1 : LinearMap.trace (ZMod 2) _ (a6BinaryRep 1 threeCycle) = 1 :=
    (trace_matrixBaseChange (RingHom.id _) rep4a threeCycle).trans
      (by rw [trace_rep4a_threeCycle]; rfl)
  have h2 : LinearMap.trace (ZMod 2) _ (a6BinaryRep 2 threeCycle) = 0 :=
    (trace_matrixBaseChange (RingHom.id _) rep4b threeCycle).trans
      (by rw [trace_rep4b_threeCycle]; rfl)
  by_cases hd : (![1, 4, 4, 16] : Fin 4 → ℕ) i = ![1, 4, 4, 16] j
  · have hcases : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isEmpty_equiv_of_trace_ne threeCycle (by rw [h1, h2]; exact one_ne_zero)
    · exact isEmpty_equiv_of_trace_ne threeCycle (by rw [h1, h2]; exact zero_ne_one)
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

@[expose] noncomputable def realPartMap {m n : ℕ} (T : Matrix (Fin m) (Fin n) FieldFour) :
    (Fin n → FieldFour) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun x a := reZ ((T *ᵥ x) a)
  map_add' x y := by
    funext a
    rw [Matrix.mulVec_add]
    exact reZ_add _ _
  map_smul' c x := by
    funext a
    rw [Matrix.mulVec_smul]
    exact reZ_smul c _

theorem realPartMap_eq_zero {m n : ℕ} (T : Matrix (Fin m) (Fin n) FieldFour)
    (h : realPartMap T = 0) : T = 0 := by
  have hv : ∀ x, T *ᵥ x = 0 := by
    intro x
    funext a
    have h1 := congrFun (LinearMap.congr_fun h x) a
    have h2 := congrFun (LinearMap.congr_fun h (fun i => ω * x i)) a
    change reZ ((T *ᵥ x) a) = 0 at h1
    change reZ ((T *ᵥ fun i => ω * x i) a) = 0 at h2
    have h3 : (T *ᵥ fun i => ω * x i) a = ω * (T *ᵥ x) a := by
      have : (fun i => ω * x i) = ω • x := rfl
      rw [this, Matrix.mulVec_smul]
      rfl
    rw [h3, reZ_ω_mul] at h2
    exact eq_zero_of_reZ_imZ _ h1 h2
  refine Matrix.ext fun a b => ?_
  have := congrFun (hv (Pi.single b 1)) a
  rw [Matrix.mulVec_single_one] at this
  exact this

@[expose] noncomputable def realPartIntertwining {m : ℕ}
    (M : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour)
    (N : alternatingGroup (Fin 6) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (T : Matrix (Fin m) (Fin 8) FieldFour) (hT : ∀ g, T * M g = (N g).map ofPrime * T) :
    (restrictFour M).IntertwiningMap (matrixBaseChange (RingHom.id (ZMod 2)) N) where
  toLinearMap := realPartMap T
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    funext a
    change reZ ((T *ᵥ restrictFour M g x) a) = (((N g).map (RingHom.id (ZMod 2))) *ᵥ
      fun b => reZ ((T *ᵥ x) b)) a
    rw [restrictFour_apply, Matrix.mulVec_mulVec, hT g, ← Matrix.mulVec_mulVec, RingHom.coe_id,
      Matrix.map_id]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← reHom_apply, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [reHom_apply, reZ_ofPrime_mul]

theorem nonempty_equiv_of_intertwining_two {K : Type*} [Field K] {d m : ℕ}
    (M : alternatingGroup (Fin 6) →* Matrix (Fin d) (Fin d) (ZMod 2))
    (N : alternatingGroup (Fin 6) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (hM : (matrixBaseChange (RingHom.id (ZMod 2)) M).IsIrreducible)
    (hN : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible) (ψ : ZMod 2 →+* K)
    (f : (matrixBaseChange ψ M).IntertwiningMap (matrixBaseChange ψ N)) (hf : f ≠ 0) :
    Nonempty ((matrixBaseChange (RingHom.id (ZMod 2)) N).Equiv
      (matrixBaseChange (RingHom.id (ZMod 2)) M)) := by
  have hT0 : LinearMap.toMatrix' f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact LinearMap.toMatrix'.injective (h.trans (map_zero _).symm)
  obtain ⟨T, hT, hTM⟩ := exists_ne_zero_mul_eq_mul_of_map ψ (fun g => M g) (fun g => N g) _ hT0
    (toMatrix'_mul_map_eq ψ M N f)
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (intertwiningMapOfMatrix (RingHom.id (ZMod 2)) M N T hTM)
    (intertwiningMapOfMatrix_ne_zero _ M N T hTM hT)
  exact ⟨e.symm⟩

theorem nonempty_equiv_of_intertwining_four {K : Type*} [Field K] {m : ℕ}
    (M : alternatingGroup (Fin 6) →* Matrix (Fin 8) (Fin 8) FieldFour)
    (N : alternatingGroup (Fin 6) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (hM : (restrictFour M).IsIrreducible)
    (hN : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible) (φ : FieldFour →+* K)
    (f : (matrixBaseChange φ M).IntertwiningMap
      (matrixBaseChange φ
        ((ofPrime.mapMatrix : Matrix (Fin m) (Fin m) (ZMod 2) →+* _).toMonoidHom.comp N)))
    (hf : f ≠ 0) :
    Nonempty ((matrixBaseChange (RingHom.id (ZMod 2)) N).Equiv (restrictFour M)) := by
  have hT0 : LinearMap.toMatrix' f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact LinearMap.toMatrix'.injective (h.trans (map_zero _).symm)
  obtain ⟨T, hT, hTM⟩ := exists_ne_zero_mul_eq_mul_of_map φ (fun g => M g)
    (fun g => (N g).map ofPrime) _ hT0 (toMatrix'_mul_map_eq φ M _ f)
  have hf' : realPartIntertwining M N T hTM ≠ 0 := by
    intro h
    apply hT
    apply realPartMap_eq_zero
    exact congrArg Representation.IntertwiningMap.toLinearMap h
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (realPartIntertwining M N T hTM) hf'
  exact ⟨e.symm⟩

theorem a6BinaryRep_complete (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 6)) W) (hτ : τ.IsIrreducible) :
    FiniteDimensional (ZMod 2) W ∧ ∃ i, Nonempty (τ.Equiv (a6BinaryRep i)) := by
  classical
  have hfin := finiteDimensional_of_isIrreducible τ
  refine ⟨hfin, ?_⟩
  have hnt := nontrivial_of_isIrreducible τ
  let eW := (Module.finBasis (ZMod 2) W).equivFun
  let τ' := transportRep eW τ
  have hτ' : τ'.IsIrreducible := isIrreducible_of_equiv (transportRepEquiv eW τ) hτ
  let N := repMatrix τ'
  have hN : matrixBaseChange (RingHom.id (ZMod 2)) N = τ' := matrixBaseChange_repMatrix τ'
  have hNirr : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible := by rw [hN]; exact hτ'
  have hτN : Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) N)) := by
    rw [hN]
    exact ⟨transportRepEquiv eW τ⟩
  obtain ⟨eτ⟩ := hτN
  let k := AlgebraicClosure (ZMod 2)
  let ψ : ZMod 2 →+* k := (toField k).comp ofPrime
  have hm : 0 < finrank (ZMod 2) W := Module.finrank_pos
  have : Nonempty (Fin (finrank (ZMod 2) W)) := ⟨⟨0, hm⟩⟩
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation (matrixBaseChange ψ N)
  obtain ⟨-, i, ⟨e⟩⟩ := a6ClosureRep_complete k U.toSubmodule U.toRepresentation hUirr
  let incl : U.toRepresentation.IntertwiningMap (matrixBaseChange ψ N) :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let f := incl.comp e.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    obtain ⟨u, huU, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hU0
      ext x
      exact ⟨fun hx => (Submodule.mem_bot k).mpr (hcon x hx),
        fun hx => (Submodule.mem_bot k).mp hx ▸ Submodule.zero_mem _⟩
    intro h0
    apply hu0
    have h1 : f (e ⟨u, huU⟩) = u := by
      change U.toSubmodule.subtype (e.symm (e ⟨u, huU⟩)) = u
      rw [Representation.Equiv.symm_apply_apply]
      rfl
    rw [← h1, h0]
    rfl
  fin_cases i
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_two rep1 N (isIrreducible_rep1 _) hNirr ψ f hf
    exact ⟨0, ⟨eτ.trans e'⟩⟩
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_two rep4a N (isIrreducible_rep4a _) hNirr ψ f hf
    exact ⟨1, ⟨eτ.trans e'⟩⟩
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_two rep4b N (isIrreducible_rep4b _) hNirr ψ f hf
    exact ⟨2, ⟨eτ.trans e'⟩⟩
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_four rep8a N isIrreducible_restrictFour_rep8a
      hNirr (toField k) f hf
    exact ⟨3, ⟨(eτ.trans e').trans (transportRepEquiv realEquiv _)⟩⟩
  · obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_four rep8b N isIrreducible_restrictFour_rep8b
      hNirr (toField k) f hf
    exact ⟨3, ⟨((eτ.trans e').trans restrictFourEquiv.symm).trans (transportRepEquiv realEquiv _)⟩⟩


end CFSG.CharacterTheory.SteinbergBY
