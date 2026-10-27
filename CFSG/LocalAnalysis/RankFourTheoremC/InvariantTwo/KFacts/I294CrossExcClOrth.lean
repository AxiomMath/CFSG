module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClGen
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open scoped Matrix

section Diagonal

variable (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]

@[expose] noncomputable def crossExcClDiag : (ι → Kˣ) →* GL ι K :=
  (Units.map (Matrix.diagonalRingHom ι K).toMonoidHom).comp
    (MulEquiv.piUnits.symm : (ι → Kˣ) ≃* (ι → K)ˣ).toMonoidHom

variable {ι K}

theorem coe_crossExcClDiag (d : ι → Kˣ) :
    ((crossExcClDiag ι K d : GL ι K) : Matrix ι ι K) = Matrix.diagonal (fun i => (d i : K)) :=
  rfl

theorem crossExcClDiag_mulVec (d : ι → Kˣ) (v : ι → K) (i : ι) :
    (((crossExcClDiag ι K d : GL ι K) : Matrix ι ι K) *ᵥ v) i = (d i : K) * v i := by
  rw [coe_crossExcClDiag, Matrix.mulVec_diagonal]

theorem crossExcClDiag_injective : Function.Injective (crossExcClDiag ι K) := by
  intro d d' h
  funext i
  apply Units.ext
  have := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) h
  simpa [coe_crossExcClDiag] using this

end Diagonal

section Tori

variable {K : Type} [Field K]

variable (K) in
@[expose] def crossExcClTail (s : ℕ) (ι' : Type) : (Fin s → Kˣ) →* (Fin s ⊕ Fin s ⊕ ι' → Kˣ) where
  toFun t := Sum.elim t (Sum.elim t⁻¹ fun _ => 1)
  map_one' := by
    funext x
    rcases x with i | i | i <;> rfl
  map_mul' t u := by
    funext x
    rcases x with i | i | i <;> simp [mul_comm]

variable (K) in
@[expose] def crossExcClSplit (s : ℕ) : (Fin s → Kˣ) →* (Fin s ⊕ Fin s → Kˣ) where
  toFun t := Sum.elim t t⁻¹
  map_one' := by
    funext x
    rcases x with i | i <;> rfl
  map_mul' t u := by
    funext x
    rcases x with i | i <;> simp [mul_comm]

theorem crossExcClTail_injective (s : ℕ) (ι' : Type) :
    Function.Injective (crossExcClTail K s ι') := by
  intro t u h
  funext i
  simpa [crossExcClTail] using congr_fun h (Sum.inl i)

theorem crossExcClSplit_injective (s : ℕ) : Function.Injective (crossExcClSplit K s) := by
  intro t u h
  funext i
  simpa [crossExcClSplit] using congr_fun h (Sum.inl i)

theorem crossExcCl_unit_mul_inv_mul (u : Kˣ) (x y : K) :
    ((u : K) * x) * (((u⁻¹ : Kˣ) : K) * y) = x * y := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem crossExcCl_diag_quadOdd (n : ℕ) (t : Fin n → Kˣ) (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n K
      (((crossExcClDiag (Fin n ⊕ Fin n ⊕ Unit) K (crossExcClTail K n Unit t) : GL _ K) :
        Matrix _ _ K) *ᵥ v) = StatedQuadOdd n K v := by
  simp only [StatedQuadOdd, crossExcClDiag_mulVec, crossExcClTail, MonoidHom.coe_mk,
    OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr, Pi.inv_apply, Units.val_one, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => crossExcCl_unit_mul_inv_mul _ _ _

theorem crossExcCl_diag_quadPlus (n : ℕ) (t : Fin n → Kˣ) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K
      (((crossExcClDiag (Fin n ⊕ Fin n) K (crossExcClSplit K n t) : GL _ K) : Matrix _ _ K) *ᵥ
        v) = StatedQuadPlus n K v := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, crossExcClDiag_mulVec,
    crossExcClSplit, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr, Pi.inv_apply]
  exact Finset.sum_congr rfl fun i _ => crossExcCl_unit_mul_inv_mul _ _ _

theorem crossExcCl_diag_quadMinus (n : ℕ) (b c : K) (t : Fin (n - 1) → Kˣ)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c
      (((crossExcClDiag (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K
        (crossExcClTail K (n - 1) (Fin 2) t) : GL _ K) : Matrix _ _ K) *ᵥ v) =
      StatedQuadMinus n K b c v := by
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, crossExcClDiag_mulVec,
    crossExcClTail, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr, Pi.inv_apply,
    Units.val_one, one_mul]
  congr 3
  exact Finset.sum_congr rfl fun i _ => crossExcCl_unit_mul_inv_mul _ _ _

end Tori

section Orders

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem crossExcCl_card_isometryCore {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    Nat.card (CFSG.MatrixModel.isometryCore Q₀) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h : CFSG.MatrixModel.isometryCore Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ
  have key : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      (TauCeti.QuadraticMap.orthogonalGroup Q).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) _
  rw [h, key]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem crossExcCl_statedOmega_le (Q₀ : (ι → K) → K) :
    StatedOmega Q₀ ≤ CFSG.MatrixModel.isometryCore Q₀ := by
  have h : StatedOmega Q₀ = ⁅CFSG.MatrixModel.isometryCore Q₀, CFSG.MatrixModel.isometryCore Q₀⁆ :=
    rfl
  rw [h]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem crossExcCl_cast_prod {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ((∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 m, ((q : ℤ) ^ (2 * i) - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  ring

variable [Finite K]

theorem crossExcCl_card_isoOdd (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadOdd n K)) =
      2 * Nat.card K ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * i) - 1) := by
  rw [crossExcCl_card_isometryCore (CFSG.LieType.Universal.Spin.coe_quadOdd n K)]
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [CFSG.ClassicalInvolution.card_orthogonalGroup_quadOdd_of_two_ne_zero h2 n]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, crossExcCl_cast_prod hq]

theorem crossExcCl_card_isoPlus (m : ℕ) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) K)) =
      2 * Nat.card K ^ (m * (m + 1)) * (Nat.card K ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  rw [crossExcCl_card_isometryCore (CFSG.LieType.Universal.Spin.coe_quadPlus (m + 1) K)]
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [(CFSG.ClassicalInvolution.card_singular_and_orthogonalGroup_quadPlus m).2]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), crossExcCl_cast_prod hq]
  push_cast
  ring

theorem crossExcCl_card_isoMinus {b c : K} {m : ℕ}
    (hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1)) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c)) =
      2 * Nat.card K ^ (m * (m + 1)) * (Nat.card K ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  rw [crossExcCl_card_isometryCore (CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c)]
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [hO]
  push_cast [crossExcCl_cast_prod hq]
  ring

end Orders

section Sylow

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem crossExcCl_not_dvd_of_dvd_pred (hp : p.Prime) {q : ℕ} (hq : 1 ≤ q) (hpq : p ∣ q - 1) :
    ¬ p ∣ q := fun h => by
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub h hpq
    rwa [Nat.sub_sub_self hq] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem crossExcCl_not_dvd_two_mul_pow_mul {q a X : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ q) (hX : ¬ p ∣ X) : ¬ p ∣ 2 * q ^ a * X := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact hpq (hp.dvd_of_dvd_pow h)
  · exact hX h

theorem crossExcCl_sylow_isoOdd {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    (hpq : p ∣ Nat.card K - 1) (hn : n < p)
    (S : Sylow p (CFSG.MatrixModel.isometryCore (StatedQuadOdd n K))) :
    IsMulCommutative (S : Subgroup (CFSG.MatrixModel.isometryCore (StatedQuadOdd n K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  have hpK := crossExcCl_not_dvd_of_dvd_pred hp hq hpq
  let τ : (Fin n → Kˣ) →* CFSG.MatrixModel.isometryCore (StatedQuadOdd n K) :=
    ((crossExcClDiag (Fin n ⊕ Fin n ⊕ Unit) K).comp (crossExcClTail K n Unit)).codRestrict _
      fun t => Subgroup.subset_closure (fun v => crossExcCl_diag_quadOdd n t v)
  have hτ : Function.Injective τ := fun a b h =>
    crossExcClTail_injective n Unit (crossExcClDiag_injective (congrArg Subtype.val h))
  refine crossExcCl_sylow_abelian_of_torus τ hτ
    (M := 2 * Nat.card K ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, crossExcClGeom (Nat.card K) (2 * i))
    ?_ ?_ S
  · rw [crossExcCl_card_isoOdd h2 n, crossExcCl_prod_pow_two hq]
    ring
  · exact crossExcCl_not_dvd_two_mul_pow_mul hp hp2 hpK
      (crossExcCl_not_dvd_prod_geom hp hp2 hq hpq hn)

theorem crossExcCl_sylow_isoPlus {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : m + 1 < p)
    (S : Sylow p (CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) K))) :
    IsMulCommutative (S : Subgroup (CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  have hpK := crossExcCl_not_dvd_of_dvd_pred hp hq hpq
  let τ : (Fin (m + 1) → Kˣ) →* CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) K) :=
    ((crossExcClDiag (Fin (m + 1) ⊕ Fin (m + 1)) K).comp (crossExcClSplit K (m + 1))).codRestrict _
      fun t => Subgroup.subset_closure (fun v => crossExcCl_diag_quadPlus (m + 1) t v)
  have hτ : Function.Injective τ := fun a b h =>
    crossExcClSplit_injective (m + 1) (crossExcClDiag_injective (congrArg Subtype.val h))
  refine crossExcCl_sylow_abelian_of_torus τ hτ
    (M := 2 * Nat.card K ^ (m * (m + 1)) * (crossExcClGeom (Nat.card K) (m + 1) *
      ∏ i ∈ Finset.Icc 1 m, crossExcClGeom (Nat.card K) (2 * i))) ?_ ?_ S
  · rw [crossExcCl_card_isoPlus m, ← crossExcClGeom_mul hq (m + 1), crossExcCl_prod_pow_two hq]
    ring
  · refine crossExcCl_not_dvd_two_mul_pow_mul hp hp2 hpK fun h => ?_
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact crossExcClGeom_not_dvd hq hpq (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos m) hm) h
    · exact crossExcCl_not_dvd_prod_geom hp hp2 hq hpq (by omega) h

theorem crossExcCl_sylow_isoMinus {m : ℕ} {b c : K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1))
    (hpq : p ∣ Nat.card K - 1) (hm : m + 1 < p)
    (S : Sylow p (CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c))) :
    IsMulCommutative
      (S : Subgroup (CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  have hpK := crossExcCl_not_dvd_of_dvd_pred hp hq hpq
  let τ : (Fin (m + 1 - 1) → Kˣ) →* CFSG.MatrixModel.isometryCore (StatedQuadMinus (m + 1) K b c) :=
    ((crossExcClDiag (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).comp
      (crossExcClTail K (m + 1 - 1) (Fin 2))).codRestrict _
      fun t => Subgroup.subset_closure (fun v => crossExcCl_diag_quadMinus (m + 1) b c t v)
  have hτ : Function.Injective τ := fun a b h =>
    crossExcClTail_injective (m + 1 - 1) (Fin 2)
      (crossExcClDiag_injective (congrArg Subtype.val h))
  refine crossExcCl_sylow_abelian_of_torus τ hτ
    (M := 2 * Nat.card K ^ (m * (m + 1)) * ((Nat.card K ^ (m + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 m, crossExcClGeom (Nat.card K) (2 * i))) ?_ ?_ S
  · rw [crossExcCl_card_isoMinus hO, crossExcCl_prod_pow_two hq, Nat.add_sub_cancel]
    ring
  · refine crossExcCl_not_dvd_two_mul_pow_mul hp hp2 hpK fun h => ?_
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have hqp : (Nat.card K : ZMod p) = 1 := by
        have h1 := (ZMod.natCast_eq_zero_iff (Nat.card K - 1) p).2 hpq
        rwa [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h1
      have h0 := (ZMod.natCast_eq_zero_iff _ p).2 h
      push_cast [hqp] at h0
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_ofNat]
        simpa [one_add_one_eq_two] using h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        ((ZMod.natCast_eq_zero_iff 2 p).1 h2))
    · exact crossExcCl_not_dvd_prod_geom hp hp2 hq hpq (by omega) h

end Sylow

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] {p : ℕ}

theorem crossExcCl_sylow_statedOmega (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hN : Fintype.card ι / 2 < p) (Q₀ : (ι → K) → K)
    (hI : p ∣ Nat.card K - 1 → ∀ S : Sylow p (CFSG.MatrixModel.isometryCore Q₀),
      IsMulCommutative (S : Subgroup (CFSG.MatrixModel.isometryCore Q₀)))
    (R : Sylow p (StatedProj (StatedOmega Q₀))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedOmega Q₀))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact crossExcCl_sylow_statedProj hp hp2 hpK hN (StatedOmega Q₀)
    (fun hpq S => isMulCommutative_sylow_of_injective
      (Subgroup.inclusion (crossExcCl_statedOmega_le Q₀))
      (Subgroup.inclusion_injective _) (hI hpq) S) R

theorem crossExcCl_sylow_statedOmega_odd {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (h2 : (2 : K) ≠ 0) (hn : n < p)
    (R : Sylow p (StatedProj (StatedOmega (StatedQuadOdd n K)))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K)))) :=
  crossExcCl_sylow_statedOmega hp hp2 hpK
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega) _
    (fun hpq S => crossExcCl_sylow_isoOdd hp hp2 h2 hpq hn S) R

theorem crossExcCl_sylow_statedOmega_plus {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (hm : m + 1 < p)
    (R : Sylow p (StatedProj (StatedOmega (StatedQuadPlus (m + 1) K)))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadPlus (m + 1) K)))) :=
  crossExcCl_sylow_statedOmega hp hp2 hpK
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) _
    (fun hpq S => crossExcCl_sylow_isoPlus hp hp2 hpq hm S) R

theorem crossExcCl_sylow_statedOmega_minus {m : ℕ} {b c : K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K)
    (hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1))
    (hm : m + 1 < p) (R : Sylow p (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c)))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c)))) :=
  crossExcCl_sylow_statedOmega hp hp2 hpK
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) _
    (fun hpq S => crossExcCl_sylow_isoMinus hp hp2 hO hpq hm S) R

end Stated

end CFSG.LocalAnalysis.RankFourTheoremC
