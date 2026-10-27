module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.OutRank
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import all CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Assembly.LowTwoRank

theorem ringEquiv_sq_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (φ : K ≃+* K) : φ ^ 2 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  ext x
  show φ (φ x) = x
  by_cases hx : φ x = x
  · rw [hx, hx]
  have h0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have h1 : x ≠ 1 := fun h => hx (by rw [h, map_one])
  have hy0 : φ x ≠ 0 := fun h => h0 (φ.injective (by rw [h, map_zero]))
  have hy1 : φ x ≠ 1 := fun h => h1 (φ.injective (by rw [h, map_one]))
  have hz0 : φ (φ x) ≠ 0 := fun h => hy0 (φ.injective (by rw [h, map_zero]))
  have hz1 : φ (φ x) ≠ 1 := fun h => hy1 (φ.injective (by rw [h, map_one]))
  have hcard : ({0, 1, x, φ x} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hx)]
    · simp [h1.symm, hy1.symm]
    · simp [zero_ne_one, h0.symm, hy0.symm]
  have huniv : ({0, 1, x, φ x} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (hcard.trans hc.symm)
  have hmem : φ (φ x) ∈ ({0, 1, x, φ x} : Finset K) := huniv ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h hz0
  · exact absurd h hz1
  · exact h
  · exact absurd (φ.injective h) hx

section Descend

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem coe_conjL_pow (u : Y) (hu : u ∈ Subgroup.normalizer (L : Set Y)) (m : ℕ) (ℓ : ↥L) :
    (((conjL u hu ^ m) ℓ : ↥L) : Y) = u ^ m * ℓ * (u ^ m)⁻¹ := by
  induction m generalizing ℓ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_conjL]
    simp only [pow_succ, mul_inv_rev, mul_assoc]

theorem descendAut_pow_apply {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P) (u : Y)
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) (m : ℕ) (ℓ : ↥L) :
    (descendAut e u hu ^ m) (e (QuotientGroup.mk ℓ)) =
      e (QuotientGroup.mk ((conjL u hu ^ m) ℓ)) := by
  induction m generalizing ℓ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, descendAut_apply, ih, pow_succ, MulAut.mul_apply]

theorem descendAut_pow_eq_one {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P) {u : Y}
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) {m : ℕ} (hum : u ^ m = 1) :
    descendAut e u hu ^ m = 1 := by
  ext p
  obtain ⟨q, rfl⟩ := e.surjective p
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descendAut_pow_apply, MulAut.one_apply]
  congr 2
  ext
  rw [coe_conjL_pow, hum]
  simp

end Descend

section Unitary

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K]

theorem exists_unitary_conj_of_normalizer_pow {Y : Type} [Group Y] {L : Subgroup Y}
    {n : ℕ} (hn : 4 ≤ n) [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {u : Y} (hu : u ∈ Subgroup.normalizer (L : Set Y)) {k : ℕ} (huk : u ^ 3 ^ k = 1) :
    ∃ A : GL (Fin n) K,
      (∀ x y : Fin n → K, stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq
        hK le_rfl) n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
          stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
            x y) ∧
      A ^ 3 ^ k ∈ StatedScalars (Fin n) K ∧
      ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
        (g' : GL (Fin n) K) = A * (g : GL (Fin n) K) * A⁻¹ ∧
          u * (ρ g : Y) * u⁻¹ = (ρ g' : Y) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by have := (Prod.mk.inj h).1; omega
  have hperf : Group.IsPerfect (StatedSU n (2 ^ 1) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn3 hnq
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  set β := descendAut e u hu
  let Θ : StatedProj (StatedSU n (2 ^ 1) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (unitaryPSUEquiv h hn1).symm.trans (unitaryPSUEquivPrimeFormOne h n)
  have hΘ : ∀ g : unitarySU 2 1 K n, Θ (QuotientGroup.mk g) =
      (QuotientGroup.mk (⟨g, (unitarySU_eq_gramSU h n).le g.2⟩ : gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : primeFormP h _) := fun g => by
    have h1 : (unitaryPSUEquiv h hn1).symm (QuotientGroup.mk g) = unitaryProj h n g :=
      (MulEquiv.symm_apply_eq _).mpr (unitaryPSUEquiv_unitaryProj h hn1 g).symm
    simp only [Θ, MulEquiv.trans_apply, h1]
    rfl
  set β' := MulAut.congr Θ β with hβ'
  have hβ3 : β ^ 3 ^ k = 1 := descendAut_pow_eq_one e hu huk
  have hβ'3 : β' ^ 3 ^ k = 1 := by rw [← map_pow, hβ3, map_one]
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h isPrimeFormGram_one hn3 hq β'
  have hφ : φ = 1 := by
    have h1 := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq A φ
    rw [← hA] at h1
    refine ringEquiv_eq_one_of_pow_three_pow (by rw [hK]; norm_num) φ (k := k) ?_
    rw [← h1, ← map_pow, hβ'3, map_one]
  subst hφ
  rw [map_one, mul_one] at hA
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn3
    (A := A ^ 3 ^ k) (by rw [map_pow, ← hA, hβ'3])
  set cA := conjSU h A.2 with hcA
  have key : ∀ g : unitarySU 2 1 K n,
      e (QuotientGroup.mk (conjL u hu (ρ g))) = (QuotientGroup.mk (cA g) : StatedProj _) := by
    intro g
    have h1 : e (QuotientGroup.mk (conjL u hu (ρ g))) = β (QuotientGroup.mk g) := by
      rw [← descendAut_apply e u hu, hρe]
    have h2 : Θ (β (QuotientGroup.mk g)) = Θ (QuotientGroup.mk (cA g)) := by
      have h3 : β' (Θ (QuotientGroup.mk g)) = Θ (β (QuotientGroup.mk g)) := by
        rw [hβ', MulAut.congr_apply]
        simp
      rw [← h3, hA, hΘ, hΘ, primeFormConjHom_mk]
      rfl
    rw [h1]
    exact Θ.injective h2
  have hρ : ∀ g, conjL u hu (ρ g) = ρ (cA g) := by
    have := eq_of_inv_mul_mem_center (ρ.comp cA) ((conjL u hu).toMonoidHom.comp ρ) (fun g => by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        inv_mul_eq_one]
      apply e.injective
      change e (QuotientGroup.mk (ρ (cA g))) = e (QuotientGroup.mk (conjL u hu (ρ g)))
      rw [hρe, key]
      rfl)
    exact fun g => (DFunLike.congr_fun this g).symm
  refine ⟨A.1, (mem_primeFormUnitary_one_iff_isometry h A.1).mp A.2, ?_,
    fun g => ⟨cA g, rfl, ?_⟩⟩
  · obtain ⟨c', hc'⟩ : ∃ c' : Kˣ,
        GeneralLinearGroup.scalar (Fin n) c' = ((A ^ 3 ^ k : _) : GL (Fin n) K) :=
      ⟨c, hc.symm⟩
    exact ⟨c', by simpa using hc'⟩
  · exact congrArg Subtype.val (hρ g)

@[expose] noncomputable def conjSUSemi (h : UnitaryFieldData 2 1 K) {n : ℕ} (φ : K ≃+* K)
    {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    unitarySU 2 1 K n →* unitarySU 2 1 K n :=
  MonoidHom.mk' (fun g => ⟨A * glAut φ (g : GL (Fin n) K) * A⁻¹,
    (unitarySU_eq_gramSU h n).ge (conj_mem_gramSU h _ hA
      (glAut_mem_gramSU h isPrimeFormGram_one φ ((unitarySU_eq_gramSU h n).le g.2)))⟩)
    (fun a b => by
      ext
      simp [mul_assoc])

@[simp] theorem coe_conjSUSemi (h : UnitaryFieldData 2 1 K) {n : ℕ} (φ : K ≃+* K)
    {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (g : unitarySU 2 1 K n) :
    ((conjSUSemi h φ hA g : unitarySU 2 1 K n) : GL (Fin n) K) =
      A * glAut φ (g : GL (Fin n) K) * A⁻¹ :=
  rfl

theorem exists_semilinear_conj_of_normalizer {Y : Type} [Group Y] {L : Subgroup Y}
    {n : ℕ} (hn : 4 ≤ n) [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {u : Y} (hu : u ∈ Subgroup.normalizer (L : Set Y)) :
    ∃ (φ : K ≃+* K) (A : GL (Fin n) K), φ ^ 2 = 1 ∧
      (∀ x y : Fin n → K, stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq
        hK le_rfl) n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
          stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
            x y) ∧
      (∀ x y : Fin n → K, stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq
        hK le_rfl) n ((A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (x i)))
          ((A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (y i))) =
        φ (stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
          x y)) ∧
      ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
        (g' : GL (Fin n) K) = A * glAut φ (g : GL (Fin n) K) * A⁻¹ ∧
          u * (ρ g : Y) * u⁻¹ = (ρ g' : Y) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by have := (Prod.mk.inj h).1; omega
  have hperf : Group.IsPerfect (StatedSU n (2 ^ 1) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn3 hnq
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  set β := descendAut e u hu
  let Θ : StatedProj (StatedSU n (2 ^ 1) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (unitaryPSUEquiv h hn1).symm.trans (unitaryPSUEquivPrimeFormOne h n)
  have hΘ : ∀ g : unitarySU 2 1 K n, Θ (QuotientGroup.mk g) =
      (QuotientGroup.mk (⟨g, (unitarySU_eq_gramSU h n).le g.2⟩ : gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : primeFormP h _) := fun g => by
    have h1 : (unitaryPSUEquiv h hn1).symm (QuotientGroup.mk g) = unitaryProj h n g :=
      (MulEquiv.symm_apply_eq _).mpr (unitaryPSUEquiv_unitaryProj h hn1 g).symm
    simp only [Θ, MulEquiv.trans_apply, h1]
    rfl
  set β' := MulAut.congr Θ β with hβ'
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h isPrimeFormGram_one hn3 hq β'
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hiso : ∀ x y : Fin n → K, stdHermForm h n ((A.1 : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((A.1 : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y :=
    (mem_primeFormUnitary_one_iff_isometry h A.1).mp A.2
  set cA := conjSUSemi h φ A.2 with hcA
  have key : ∀ g : unitarySU 2 1 K n,
      e (QuotientGroup.mk (conjL u hu (ρ g))) = (QuotientGroup.mk (cA g) : StatedProj _) := by
    intro g
    have h1 : e (QuotientGroup.mk (conjL u hu (ρ g))) = β (QuotientGroup.mk g) := by
      rw [← descendAut_apply e u hu, hρe]
    have h2 : Θ (β (QuotientGroup.mk g)) = Θ (QuotientGroup.mk (cA g)) := by
      have h3 : β' (Θ (QuotientGroup.mk g)) = Θ (β (QuotientGroup.mk g)) := by
        rw [hβ', MulAut.congr_apply]
        simp
      rw [← h3, hA, hΘ, hΘ, MulAut.mul_apply]
      change primeFormConjHom h _ A (primeFormFieldAut h isPrimeFormGram_one φ
        (QuotientGroup.mk _)) = _
      rw [primeFormFieldAut_mk, primeFormConjHom_mk]
      rfl
    rw [h1]
    exact Θ.injective h2
  have hρ : ∀ g, conjL u hu (ρ g) = ρ (cA g) := by
    have := eq_of_inv_mul_mem_center (ρ.comp cA) ((conjL u hu).toMonoidHom.comp ρ) (fun g => by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        inv_mul_eq_one]
      apply e.injective
      change e (QuotientGroup.mk (ρ (cA g))) = e (QuotientGroup.mk (conjL u hu (ρ g)))
      rw [hρe, key]
      rfl)
    exact fun g => (DFunLike.congr_fun this g).symm
  refine ⟨φ, A.1, ringEquiv_sq_eq_one hK4 φ, hiso, ?_, fun g => ⟨cA g, rfl, ?_⟩⟩
  · intro x y
    rw [hiso]
    simp only [stdHermForm_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_bar_comm h φ]
  · exact congrArg Subtype.val (hρ g)

theorem coe_glAut_eq_map (φ : K ≃+* K) {n : ℕ} (g : GL (Fin n) K) :
    ((glAut φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K).map φ :=
  coe_glAut φ g

end Unitary

end CFSG.HardMathSupport.Curtis.UnitaryLevi
