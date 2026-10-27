module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeABasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviWall

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Coord

variable {K : Type} [Field K] {n : ℕ}

omit [Field K] in
theorem ext_plus {v w : Fin (2 * n) → K}
    (h1 : ∀ i, v (plusIndexEquiv n (.inl i)) = w (plusIndexEquiv n (.inl i)))
    (h2 : ∀ i, v (plusIndexEquiv n (.inr i)) = w (plusIndexEquiv n (.inr i))) : v = w := by
  funext c
  obtain ⟨x, rfl⟩ := (plusIndexEquiv n).surjective c
  rcases x with i | i
  · exact h1 i
  · exact h2 i

@[expose] noncomputable def coordLin (a b : Fin n → (Fin (2 * n) → K) →ₗ[K] K) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  LinearMap.pi fun c => Sum.elim a b ((plusIndexEquiv n).symm c)

@[simp] theorem coordLin_inl (a b : Fin n → (Fin (2 * n) → K) →ₗ[K] K) (v : Fin (2 * n) → K)
    (i : Fin n) : coordLin a b v (plusIndexEquiv n (.inl i)) = a i v := by
  simp [coordLin]

@[simp] theorem coordLin_inr (a b : Fin n → (Fin (2 * n) → K) →ₗ[K] K) (v : Fin (2 * n) → K)
    (i : Fin n) : coordLin a b v (plusIndexEquiv n (.inr i)) = b i v := by
  simp [coordLin]

theorem single_inl_apply_inl (i j : Fin n) :
    (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n (.inl j)) =
      if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp
  · rw [ite_eq_right h]
    exact Pi.single_eq_of_ne (fun h' => h (Sum.inl_injective ((plusIndexEquiv n).injective h'))) _

theorem single_inl_apply_inr (i j : Fin n) :
    (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n (.inr j)) =
      0 :=
  Pi.single_eq_of_ne (fun h' => Sum.inr_ne_inl ((plusIndexEquiv n).injective h')) _

theorem single_inr_apply_inl (i j : Fin n) :
    (Pi.single (plusIndexEquiv n (.inr i)) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n (.inl j)) =
      0 :=
  Pi.single_eq_of_ne (fun h' => Sum.inl_ne_inr ((plusIndexEquiv n).injective h')) _

theorem single_inr_apply_inr (i j : Fin n) :
    (Pi.single (plusIndexEquiv n (.inr i)) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n (.inr j)) =
      if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp
  · rw [ite_eq_right h]
    exact Pi.single_eq_of_ne (fun h' => h (Sum.inr_injective ((plusIndexEquiv n).injective h'))) _

theorem polar_coordinateQuadPlus (u v : Fin (2 * n) → K) :
    polar (coordinateQuadPlus n K) u v =
      ∑ i, (u (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)) +
        u (plusIndexEquiv n (.inr i)) * v (plusIndexEquiv n (.inl i))) := by
  rw [polar, coordinateQuadPlus_apply, coordinateQuadPlus_apply, coordinateQuadPlus_apply,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

end Coord

structure LowPairing (n ℓ : ℕ) where
  τ : Fin n → Fin n
  invol : ∀ i, τ (τ i) = i
  lt_iff : ∀ i, (τ i).val < ℓ ↔ i.val < ℓ
  ne_self : ∀ i, i.val < ℓ → τ i ≠ i

@[expose] def LowPairing.std {n r : ℕ} (h : 2 * r ≤ n) : LowPairing n (2 * r) where
  τ i := ⟨if i.val < r then i.val + r else if i.val < 2 * r then i.val - r else i.val, by
    split_ifs <;> omega⟩
  invol i := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  lt_iff i := by
    simp only
    split_ifs <;> omega
  ne_self i hi h := by
    have h' := congrArg Fin.val h
    simp only at h'
    split_ifs at h' <;> omega

variable {K : Type} [Field K] {n ℓ : ℕ} (P : LowPairing n ℓ)

@[expose] noncomputable def lowNil : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  coordLin (fun i => if i.val < ℓ then LinearMap.proj (plusIndexEquiv n (.inr (P.τ i))) else 0)
    fun _ => 0

theorem lowNil_inl (v : Fin (2 * n) → K) (i : Fin n) :
    lowNil P v (plusIndexEquiv n (.inl i)) =
      if i.val < ℓ then v (plusIndexEquiv n (.inr (P.τ i))) else 0 := by
  rw [lowNil, coordLin_inl]
  split_ifs <;> rfl

theorem lowNil_inr (v : Fin (2 * n) → K) (i : Fin n) :
    lowNil P v (plusIndexEquiv n (.inr i)) = 0 := by
  rw [lowNil, coordLin_inr]
  rfl

theorem lowNil_mem_lowSpan (v : Fin (2 * n) → K) : lowNil P v ∈ lowSpan K n ℓ := by
  intro i
  refine ⟨lowNil_inr P v i, fun hi => ?_⟩
  rw [lowNil_inl, ite_eq_right (by omega)]

theorem lowNil_of_mem_lowPerp {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) : lowNil P v = 0 := by
  refine ext_plus (fun i => ?_) fun i => lowNil_inr P v i
  rw [lowNil_inl]
  split_ifs with hi
  · exact hv _ ((P.lt_iff i).mpr hi)
  · rfl

theorem lowNil_lowNil (v : Fin (2 * n) → K) : lowNil P (lowNil P v) = 0 :=
  lowNil_of_mem_lowPerp P (lowSpan_le_lowPerp ℓ (lowNil_mem_lowSpan P v))

theorem range_lowNil : LinearMap.range (lowNil (K := K) P) = lowSpan K n ℓ := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact lowNil_mem_lowSpan P v
  · intro hw
    refine ⟨coordLin (fun _ => 0) (fun i => if i.val < ℓ then
      LinearMap.proj (plusIndexEquiv n (.inl (P.τ i))) else 0) w, ext_plus (fun i => ?_)
        fun i => (lowNil_inr P _ i).trans (hw i).1.symm⟩
    rw [lowNil_inl, coordLin_inr]
    split_ifs with hi hi'
    · simp [P.invol]
    · exact absurd ((P.lt_iff i).mpr hi) hi'
    · exact ((hw i).2 (by omega)).symm

theorem ker_lowNil : LinearMap.ker (lowNil (K := K) P) = lowPerp K n ℓ := by
  ext v
  rw [LinearMap.mem_ker]
  refine ⟨fun hv i hi => ?_, lowNil_of_mem_lowPerp P⟩
  have h := congrFun hv (plusIndexEquiv n (.inl (P.τ i)))
  rw [lowNil_inl, ite_eq_left ((P.lt_iff i).mpr hi), P.invol] at h
  exact h

theorem coordinateQuadPlus_lowSpan {w : Fin (2 * n) → K} (hw : w ∈ lowSpan K n ℓ) :
    coordinateQuadPlus n K w = 0 := by
  rw [coordinateQuadPlus_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [(hw i).1, mul_zero]

theorem polar_lowNil_self [CharP K 2] (v : Fin (2 * n) → K) :
    polar (coordinateQuadPlus n K) v (lowNil P v) = 0 := by
  rw [polar_coordinateQuadPlus]
  simp only [lowNil_inr, lowNil_inl, mul_zero, zero_add]
  refine Finset.sum_ninvolution P.τ (fun i => ?_) (fun i hi => ?_) (fun _ => Finset.mem_univ _)
    P.invol
  · by_cases hi : i.val < ℓ
    · rw [ite_eq_left hi, ite_eq_left ((P.lt_iff i).mpr hi), P.invol, mul_comm]
      exact CharTwo.add_self_eq_zero _
    · have hi' : ¬ (P.τ i).val < ℓ := fun h => hi ((P.lt_iff i).mp h)
      simp [hi, hi']
  · refine P.ne_self i ?_
    by_contra h
    rw [ite_eq_right h, mul_zero] at hi
    exact hi rfl

theorem lowNil_comp_lowNil : (lowNil (K := K) P).comp (lowNil P) = 0 :=
  LinearMap.ext fun v => lowNil_lowNil P v

theorem toMatrix'_lowNil_mul_self [CharP K 2] :
    (1 + LinearMap.toMatrix' (lowNil (K := K) P)) * (1 + LinearMap.toMatrix' (lowNil P)) = 1 := by
  have h0 : LinearMap.toMatrix' (lowNil (K := K) P) * LinearMap.toMatrix' (lowNil P) = 0 := by
    rw [← LinearMap.toMatrix'_comp, lowNil_comp_lowNil, map_zero]
  have h2 : LinearMap.toMatrix' (lowNil (K := K) P) + LinearMap.toMatrix' (lowNil P) = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  simp only [add_mul, mul_add, one_mul, mul_one, h0, add_zero]
  rw [add_assoc, h2, add_zero]

@[expose] noncomputable def lowRepGL [CharP K 2] : GL (Fin (2 * n)) K where
  val := 1 + LinearMap.toMatrix' (lowNil P)
  inv := 1 + LinearMap.toMatrix' (lowNil P)
  val_inv := toMatrix'_lowNil_mul_self P
  inv_val := toMatrix'_lowNil_mul_self P

theorem matrixLinearEquiv_lowRepGL [CharP K 2] (v : Fin (2 * n) → K) :
    matrixLinearEquiv (lowRepGL (K := K) P) v = v + lowNil P v := by
  rw [matrixLinearEquiv_apply]
  change Matrix.mulVec (1 + LinearMap.toMatrix' (lowNil P)) v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, LinearMap.toMatrix'_mulVec]

theorem lowRepGL_mem [CharP K 2] :
    lowRepGL (K := K) P ∈ matrixIsometries (coordinateQuadPlus n K) := by
  rw [mem_matrixIsometries_iff]
  intro v
  rw [matrixLinearEquiv_lowRepGL, QuadraticMap.map_add (coordinateQuadPlus n K),
    coordinateQuadPlus_lowSpan (lowNil_mem_lowSpan P v), polar_lowNil_self, add_zero, add_zero]

@[expose] noncomputable def lowRep [CharP K 2] : matrixIsometries (coordinateQuadPlus n K) :=
  ⟨lowRepGL P, lowRepGL_mem P⟩

theorem lowRep_mul_self [CharP K 2] : lowRep (K := K) P * lowRep P = 1 :=
  Subtype.ext (Units.ext (toMatrix'_lowNil_mul_self P))

theorem sNil_lowRep [CharP K 2] : sNil (lowRep (K := K) P).val = lowNil P := by
  refine LinearMap.ext fun v => ?_
  rw [sNil_apply]
  change matrixLinearEquiv (lowRepGL P) v - v = _
  rw [matrixLinearEquiv_lowRepGL, add_sub_cancel_left]

theorem polar_lowNil_left [CharP K 2] (x y : Fin (2 * n) → K) :
    QuadraticMap.polarBilin (coordinateQuadPlus n K) (lowNil P x) y =
      QuadraticMap.polarBilin (coordinateQuadPlus n K) x (lowNil P y) := by
  have h := polar_sNil_left (lowRep P) (lowRep_mul_self P) x y
  rwa [sNil_lowRep] at h

theorem finrank_lowSpan (hℓ : ℓ ≤ n) : finrank K (lowSpan K n ℓ) = ℓ := by
  classical
  let φ : lowSpan K n ℓ ≃ₗ[K] ({i : Fin n // i.val < ℓ} → K) :=
    { toFun := fun w i => (w : Fin (2 * n) → K) (plusIndexEquiv n (.inl i.1))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun a => ⟨coordLin (fun i => if h : i.val < ℓ then
          a ⟨i, h⟩ • LinearMap.proj (plusIndexEquiv n (.inl i)) else 0) (fun _ => 0)
          (fun c => if c = c then 1 else 0), fun i => ⟨by simp, fun hi => by
            rw [coordLin_inl, dite_eq_right (by omega)]; rfl⟩⟩
      left_inv := fun w => by
        apply Subtype.ext
        refine ext_plus (fun i => ?_) fun i => ?_
        · simp only [coordLin_inl]
          split_ifs with h
          · simp
          · exact ((w.2 i).2 (by omega)).symm
        · simp only [coordLin_inr, LinearMap.zero_apply]
          exact ((w.2 i).1).symm
      right_inv := fun a => by
        funext i
        simp [i.2] }
  rw [φ.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin_lt_of_le hℓ]

@[expose] noncomputable def lowForm (u u' : Fin (2 * n) → K) : K :=
  ∑ i, if i.val < ℓ then u (plusIndexEquiv n (.inl i)) * u' (plusIndexEquiv n (.inl (P.τ i)))
    else 0

theorem polar_lowNil_eq_lowForm (x y : Fin (2 * n) → K) :
    QuadraticMap.polarBilin (coordinateQuadPlus n K) (lowNil P x) y =
      lowForm P (lowNil P x) (lowNil P y) := by
  rw [QuadraticMap.polarBilin_apply_apply, polar_coordinateQuadPlus, lowForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lowNil_inr, zero_mul, add_zero, lowNil_inl, lowNil_inl]
  split_ifs with h1 h2
  · rw [P.invol]
  · exact absurd ((P.lt_iff i).mpr h1) h2
  · rw [zero_mul]

end CFSG.SeitzReduction.OmegaPilot
