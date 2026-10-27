module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResF
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open Matrix

section Six

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem le_primeFormD_six (h : UnitaryFieldData 2 1 K)
    {A : Subgroup (MulAut (primeFormP h (idGram K 6)))} (hA : ∀ a ∈ A, a ^ 3 = 1) :
    A ≤ primeFormD h (idGram K 6) := by
  have hne : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  rw [← ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 6)) (by norm_num) hne]
  intro a ha
  rw [MonoidHom.mem_ker]
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality h.prime
      (by norm_num : 1 ≤ 2 * 1) h.card
  have key : ∀ x : K ≃+* K, x ^ 3 = 1 → x = 1 := by
    intro x hx3
    have e : x ^ Nat.card (K ≃+* K) = 1 := pow_card_eq_one'
    rw [hAut, mul_one] at e
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, e, inv_one, mul_one]
  exact key _ (by rw [← map_pow, hA a ha, map_one])

private theorem card_units_four (h : UnitaryFieldData 2 1 K) : Nat.card Kˣ = 3 := by
  have := Nat.card_units K
  rw [h.card] at this
  simpa using this

private theorem units_pow_three_four (h : UnitaryFieldData 2 1 K) (u : Kˣ) : u ^ 3 = 1 := by
  rw [← card_units_four h]
  exact pow_card_eq_one'

private theorem norm_eq_one_four (h : UnitaryFieldData 2 1 K) (u : Kˣ) : h.norm (u : K) = 1 :=
  (pow_succ_eq_one_iff_norm h u).mp (units_pow_three_four h u)

private theorem scalar_mulVec_six (z : Kˣ) (v : Fin 6 → K) :
    ((GeneralLinearGroup.scalar (Fin 6) z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v =
      (z : K) • v := by
  ext i
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
    smul_eq_mul]

private theorem eq_zero_of_mulVec_eq_zero_six (g : GL (Fin 6) K) {v : Fin 6 → K}
    (hv : (g : Matrix (Fin 6) (Fin 6) K) *ᵥ v = 0) : v = 0 := by
  have e : ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) K) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hv, Matrix.mulVec_zero] at e
  exact e.symm

private theorem exists_lift_group_six (h : UnitaryFieldData 2 1 K)
    {A : Subgroup (MulAut (primeFormP h (idGram K 6)))} (hA : IsElemAbelian 3 A)
    (hAD : A ≤ primeFormD h (idGram K 6)) {w : Fin 6 → K} (hw0 : w ≠ 0)
    (hwA : ∀ X : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) X ∈ A →
      ∃ μ : K, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w) :
    ∃ E : Subgroup (primeFormUnitary h (idGram K 6)),
      (∀ X ∈ E, primeFormConjHom h (idGram K 6) X ∈ A) ∧
      (∀ X ∈ E, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w) ∧
      Nat.card E = Nat.card A ∧ (∀ X ∈ E, ∀ Y ∈ E, X * Y = Y * X) ∧ (∀ X ∈ E, X ^ 3 = 1) := by
  classical
  have hne : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  let E : Subgroup (primeFormUnitary h (idGram K 6)) :=
    { carrier := {X | primeFormConjHom h (idGram K 6) X ∈ A ∧
        ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w}
      mul_mem' := fun {X Y} hX hY => ⟨by rw [map_mul]; exact mul_mem hX.1 hY.1, by
        rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hY.2, hX.2]⟩
      one_mem' := ⟨by rw [map_one]; exact one_mem _, by
        rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]⟩
      inv_mem' := fun {X} hX => ⟨by rw [map_inv]; exact inv_mem hX.1, by
        conv_lhs => rw [← hX.2]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]⟩ }
  have hmemE : ∀ X, X ∈ E ↔ primeFormConjHom h (idGram K 6) X ∈ A ∧
      ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = w := fun X => Iff.rfl
  have hinj : ∀ X ∈ E, ∀ Y ∈ E,
      primeFormConjHom h (idGram K 6) X = primeFormConjHom h (idGram K 6) Y → X = Y := by
    intro X hX Y hY hXY
    have h1 : primeFormConjHom h (idGram K 6) (X⁻¹ * Y) = 1 := by
      rw [map_mul, map_inv, hXY, inv_mul_cancel]
    obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 h1
    have hw := ((hmemE _).1 (mul_mem (inv_mem hX) hY)).2
    rw [hz, scalar_mulVec_six] at hw
    have hz1 : z = 1 := by
      have e : ((z : K) - 1) • w = 0 := by rw [sub_smul, hw, one_smul, sub_self]
      exact Units.ext (sub_eq_zero.1 ((smul_eq_zero.1 e).resolve_right hw0))
    have hXY1 : X⁻¹ * Y = 1 := Subtype.ext (by rw [hz, hz1, map_one, Subgroup.coe_one])
    exact (inv_mul_eq_one.1 hXY1)
  have hsurj : ∀ a ∈ A, ∃ X ∈ E, primeFormConjHom h (idGram K 6) X = a := by
    intro a ha
    obtain ⟨X₀, rfl⟩ := hAD ha
    obtain ⟨μ, hμ⟩ := hwA X₀ ha
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hw0 (eq_zero_of_mulVec_eq_zero_six _ hμ)
    refine ⟨scalarU h 6 (Units.mk0 μ hμ0)⁻¹ (norm_eq_one_four h _) * X₀, (hmemE _).2 ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul, conjHom_scalarU (by norm_num) hne, one_mul]
      exact ha
    · rw [Subgroup.coe_mul, coe_scalarU, Units.val_mul, ← Matrix.mulVec_mulVec, hμ,
        Matrix.mulVec_smul, scalar_mulVec_six, smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0,
        mul_inv_cancel₀ hμ0, one_smul]
    · rw [map_mul, conjHom_scalarU (by norm_num) hne, one_mul]
  have hcard : Nat.card E = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun X : E => (⟨primeFormConjHom h (idGram K 6) X, ((hmemE _).1 X.2).1⟩ : A)) ⟨?_, ?_⟩)
    · intro X Y hXY
      exact Subtype.ext (hinj X X.2 Y Y.2 (congrArg Subtype.val hXY))
    · rintro ⟨a, ha⟩
      obtain ⟨X, hX, hXa⟩ := hsurj a ha
      exact ⟨⟨X, hX⟩, Subtype.ext hXa⟩
  refine ⟨E, fun X hX => ((hmemE X).1 hX).1, fun X hX => ((hmemE X).1 hX).2, hcard, ?_, ?_⟩
  · intro X hX Y hY
    apply hinj _ (mul_mem hX hY) _ (mul_mem hY hX)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨_, ((hmemE X).1 hX).1⟩ ⟨_, ((hmemE Y).1 hY).1⟩)
  · intro X hX
    apply hinj _ (pow_mem hX 3) _ (one_mem E)
    rw [map_pow, map_one]
    exact hA.2 _ ((hmemE X).1 hX).1

private theorem exists_orthonormal_eigenbasis_subgroup {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    {n : ℕ} (h3q : 3 ∣ ℓ ^ f + 1) (E : Subgroup (primeFormUnitary h (idGram K n)))
    (hcomm : ∀ X ∈ E, ∀ Y ∈ E, X * Y = Y * X) (h3 : ∀ X ∈ E, X ^ 3 = 1) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (μ : E → Fin n → K), IsOrthonormalFamily h b ∧
      ∀ (X : E) (i : Fin n), (((X : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ b i = μ X i • b i := by
  classical
  haveI : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd h Nat.prime_three h3q
  let g : E → Module.End K (Fin n → K) := fun X =>
    ((toLinU h n (X : primeFormUnitary h (idGram K n)) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
  have hcomm' : ∀ X Y, Commute (g X) (g Y) := fun X Y =>
    (CFSG.RankThree.PartOne.KCUnitaryScalar.commute_toLinU (hcomm X X.2 Y Y.2)).map
      (Units.coeHom _)
  have hpow : ∀ X, g X ^ 3 = 1 := by
    intro X
    have e : (toLinU h n (X : primeFormUnitary h (idGram K n))) ^ 3 = 1 := by
      rw [← map_pow, h3 X X.2, map_one]
    have e2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) e
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using e2
  have hiso : ∀ X v w, idForm h n (g X v) (g X w) = idForm h n v w := fun X v w =>
    (mem_sesqUnitaryGroup.mp (toLinU_mem (X : primeFormUnitary h (idGram K n)))) v w
  obtain ⟨b, μ, hbμ, hbo⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hζ h3q
      (idForm_isSymm h n) (idForm_separatingLeft h n) g hcomm' hpow hiso
  let e : Fin (Module.finrank K (Fin n → K)) ≃ Fin n := finCongr (Module.finrank_fin_fun K)
  refine ⟨b.reindex e, fun X i => μ X (e.symm i), fun i j => ?_, fun X i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact hbμ X _

private theorem idForm_basis_eq_repr {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {b : Module.Basis (Fin n) K (Fin n → K)} (hb : IsOrthonormalFamily h b) (v : Fin n → K)
    (t : Fin n) : idForm h n (b t) v = b.repr v t := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hb t, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem exists_two_coord_ne_zero {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {b : Module.Basis (Fin n) K (Fin n → K)} (hb : IsOrthonormalFamily h b) {w : Fin n → K}
    (hw0 : w ≠ 0) (hwiso : idForm h n w w = 0) :
    ∃ t₀ t₁, t₀ ≠ t₁ ∧ b.repr w t₀ ≠ 0 ∧ b.repr w t₁ ≠ 0 := by
  classical
  obtain ⟨t₀, ht₀⟩ : ∃ t, b.repr w t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw0 (b.repr.map_eq_zero_iff.mp (Finsupp.ext hc))
  by_contra hc
  push Not at hc
  have hw : w = b.repr w t₀ • b t₀ := by
    conv_lhs => rw [← b.sum_repr w]
    rw [Finset.sum_eq_single t₀]
    · intro t _ ht
      rw [hc t₀ t (Ne.symm ht) ht₀, zero_smul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  rw [hw] at hwiso
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hb t₀ t₀, if_true,
    mul_one] at hwiso
  rcases mul_eq_zero.1 hwiso with h0 | h0
  · exact ht₀ (by simpa using h0)
  · exact ht₀ ((map_eq_zero h.bar).1 h0)

private theorem weight_eq_one_of_coord_ne_zero {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {b : Module.Basis (Fin n) K (Fin n → K)} (hb : IsOrthonormalFamily h b)
    {X : GL (Fin n) K} (hXU : X ∈ primeFormUnitary h (idGram K n)) {w : Fin n → K}
    (hXw : (X : Matrix (Fin n) (Fin n) K) *ᵥ w = w) {t : Fin n} {μ : K}
    (hXt : (X : Matrix (Fin n) (Fin n) K) *ᵥ b t = μ • b t) (ht : b.repr w t ≠ 0) : μ = 1 := by
  have e := idForm_mulVec_of_mem_primeFormUnitary hXU (b t) w
  rw [hXt, hXw, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, idForm_basis_eq_repr h hb] at e
  have hbar : h.bar μ = 1 := by
    have e' : (h.bar μ - 1) * b.repr w t = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_right ht)
  exact h.bar.injective (by rw [hbar, map_one])

private theorem exists_perm_zero_one {t₀ t₁ : Fin 6} (ht : t₀ ≠ t₁) :
    ∃ π : Equiv.Perm (Fin 6), π 0 = t₀ ∧ π 1 = t₁ := by
  obtain ⟨u, hu⟩ : ∃ u, u = Equiv.swap 0 t₀ t₁ := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by
    intro h0
    apply ht
    have e := congrArg (Equiv.swap 0 t₀) h0
    rw [hu, Equiv.swap_apply_self, Equiv.swap_apply_left] at e
    exact e.symm
  refine ⟨Equiv.swap 0 t₀ * Equiv.swap 1 u, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hu0.symm,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hu, Equiv.swap_apply_self]

theorem exists_frame_six (h : UnitaryFieldData 2 1 K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {A : Subgroup (MulAut (primeFormP h (idGram K 6)))} (hA : IsElemAbelian 3 A)
    (h81 : 3 ^ 4 ≤ Nat.card A) (hAD : A ≤ primeFormD h (idGram K 6))
    {w : Fin 6 → K} (hw0 : w ≠ 0) (hwiso : idForm h 6 w w = 0)
    (hwA : ∀ X : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) X ∈ A →
      ∃ μ : K, ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w) :
    ∃ X₁ X₂ R : primeFormUnitary h (idGram K 6),
      primeFormConjHom h (idGram K 6) X₁ ∈ A ∧ primeFormConjHom h (idGram K 6) X₂ ∈ A ∧
      (((R * X₁ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ω, 1] ∧
      (((R * X₂ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω] := by
  classical
  obtain ⟨E, hEA, hEw, hEcard, hEcomm, hE3⟩ := exists_lift_group_six h hA hAD hw0 hwA
  obtain ⟨b, μ, hb, hbμ⟩ := exists_orthonormal_eigenbasis_subgroup h (by norm_num) E hEcomm hE3
  obtain ⟨t₀, t₁, ht, ht₀, ht₁⟩ := exists_two_coord_ne_zero h hb hw0 hwiso
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_zero_one ht
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin 6) K (Fin 6 → K), b' = b.reindex π.symm :=
    ⟨_, rfl⟩
  have hb'a : ∀ i, b' i = b (π i) := fun i => by
    rw [hb', Module.Basis.reindex_apply, Equiv.symm_symm]
  have hb'o : IsOrthonormalFamily h b' := by
    have e : (⇑b' : Fin 6 → Fin 6 → K) = ⇑b ∘ π := funext hb'a
    rw [e]
    exact isOrthonormalFamily_comp hb π.injective
  obtain ⟨μ', hμ'⟩ : ∃ μ' : E → Fin 6 → K, μ' = fun X i => μ X (π i) := ⟨_, rfl⟩
  have hμ'e : ∀ (X : E) i, (((X : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) *ᵥ b' i = μ' X i • b' i := fun X i => by
    rw [hb'a, hμ']
    exact hbμ X (π i)
  have hμ'0 : ∀ X : E, μ' X 0 = 1 := fun X => by
    rw [hμ']
    exact weight_eq_one_of_coord_ne_zero h hb (X : primeFormUnitary h (idGram K 6)).2
      (hEw X X.2) (hbμ X (π 0)) (by rw [hπ0]; exact ht₀)
  have hμ'1 : ∀ X : E, μ' X 1 = 1 := fun X => by
    rw [hμ']
    exact weight_eq_one_of_coord_ne_zero h hb (X : primeFormUnitary h (idGram K 6)).2
      (hEw X X.2) (hbμ X (π 1)) (by rw [hπ1]; exact ht₁)
  have hμ'ne : ∀ (X : E) i, μ' X i ≠ 0 := by
    intro X i h0
    have e := hμ'e X i
    rw [h0, zero_smul] at e
    exact b'.ne_zero i (eq_zero_of_mulVec_eq_zero_six _ e)
  let Φ : E → (Fin 4 → Kˣ) := fun X j => Units.mk0 (μ' X j.succ.succ) (hμ'ne X _)
  have hΦ : ∀ X j, ((Φ X j : Kˣ) : K) = μ' X j.succ.succ := fun X j => rfl
  have hΦinj : Function.Injective Φ := by
    intro X Y hXY
    have hw : ∀ i, μ' X i = μ' Y i := by
      intro i
      have hj : ∀ j : Fin 4, μ' X j.succ.succ = μ' Y j.succ.succ := fun j => by
        rw [← hΦ, ← hΦ, hXY]
      induction i using Fin.cases with
      | zero => rw [hμ'0, hμ'0]
      | succ i' =>
        induction i' using Fin.cases with
        | zero => rw [Fin.succ_zero_eq_one, hμ'1, hμ'1]
        | succ j => exact hj j
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    refine b'.ext fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hμ'e X i, hμ'e Y i, hw i]
  have hΦbij : Function.Bijective Φ := by
    refine hΦinj.bijective_of_nat_card_le ?_
    rw [Nat.card_fun, card_units_four h, Nat.card_fin, hEcard]
    exact h81
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  obtain ⟨X₁, hX₁⟩ := hΦbij.2 ![1, 1, Units.mk0 ω hω0, 1]
  obtain ⟨X₂, hX₂⟩ := hΦbij.2 ![1, 1, 1, Units.mk0 ω hω0]
  have hv : ∀ (X : E) (v : Fin 4 → Kˣ), Φ X = v → ∀ j : Fin 4, μ' X j.succ.succ = (v j : K) :=
    fun X v hXv j => by rw [← hΦ, hXv]
  have hw₁ : μ' X₁ = ![1, 1, 1, 1, ω, 1] := by
    funext i
    fin_cases i
    · exact hμ'0 X₁
    · exact hμ'1 X₁
    · exact hv X₁ _ hX₁ 0
    · exact hv X₁ _ hX₁ 1
    · exact hv X₁ _ hX₁ 2
    · exact hv X₁ _ hX₁ 3
  have hw₂ : μ' X₂ = ![1, 1, 1, 1, 1, ω] := by
    funext i
    fin_cases i
    · exact hμ'0 X₂
    · exact hμ'1 X₂
    · exact hv X₂ _ hX₂ 0
    · exact hv X₂ _ hX₂ 1
    · exact hv X₂ _ hX₂ 2
    · exact hv X₂ _ hX₂ 3
  obtain ⟨R, hRU, hR₁, hR₂⟩ := exists_unitary_conj_eq_diagonal_pair h hb'o (hμ'e X₁) (hμ'e X₂)
  obtain ⟨R', hR'⟩ : ∃ R' : primeFormUnitary h (idGram K 6), (R' : GL (Fin 6) K) = R :=
    ⟨⟨R, hRU⟩, rfl⟩
  refine ⟨X₁, X₂, R', hEA _ X₁.2, hEA _ X₂.2, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR', ← hw₁]
    exact hR₁
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR', ← hw₂]
    exact hR₂

private theorem card_closure_pair_eq_nine {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) : Nat.card (Subgroup.closure ({a, b} : Set G)) = 3 ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : Commute a b := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hle : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 9 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.card_closure_pair_le hab (hA.2 a ha)
      (hA.2 b hb)
  have hsubA : Subgroup.closure ({a, b} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have hp : IsPGroup 3 (Subgroup.closure ({a, b} : Set G)) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hA.2 g (hsubA g.2))⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hza : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert a _))
  have h3 : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA.2 a ha) ha1
  have hdvd : 3 ∣ Nat.card (Subgroup.closure ({a, b} : Set G)) :=
    h3 ▸ Subgroup.card_dvd_of_le hza
  have hne3 : Nat.card (Subgroup.closure ({a, b} : Set G)) ≠ 3 := by
    intro hc
    apply hba
    rw [Subgroup.eq_of_le_of_card_ge hza (by rw [hc, h3])]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))
  rw [hn] at hle hdvd hne3 ⊢
  rcases n with _ | _ | _ | n
  · norm_num at hdvd
  · norm_num at hne3
  · rfl
  · exfalso
    have : 3 ^ 3 ≤ 3 ^ (n + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

private theorem exists_scalar_of_conjHom_eq_six (h : UnitaryFieldData 2 1 K)
    {Y Z : primeFormUnitary h (idGram K 6)}
    (hYZ : primeFormConjHom h (idGram K 6) Y = primeFormConjHom h (idGram K 6) Z) :
    ∃ z : Kˣ, (Y : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) z * Z := by
  have hne : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  have h1 : primeFormConjHom h (idGram K 6) (Y * Z⁻¹) = 1 := by
    rw [map_mul, map_inv, hYZ, mul_inv_cancel]
  obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 h1
  refine ⟨z, ?_⟩
  rw [← hz, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]

private theorem diag_entries_of_conjHom_eq_six (h : UnitaryFieldData 2 1 K)
    {Y Z : primeFormUnitary h (idGram K 6)} {d e : Fin 6 → K}
    (hY : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal d)
    (hZ : ((Z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal e)
    (hYZ : primeFormConjHom h (idGram K 6) Y = primeFormConjHom h (idGram K 6) Z) (i j : Fin 6) :
    d i * e j = d j * e i := by
  obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_six h hYZ
  have hm := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hz
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hY, hZ, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal] at hm
  have hi := congrFun (congrFun hm i) i
  have hj := congrFun (congrFun hm j) j
  simp only [Matrix.diagonal_apply_eq] at hi hj
  rw [hi, hj]
  ring

theorem goodSub_primeFormP_six (h : UnitaryFieldData 2 1 K)
    (A : Subgroup (MulAut (primeFormP h (idGram K 6)))) (hA : IsElemAbelian 3 A)
    (h81 : 3 ^ 4 ≤ Nat.card A) (T : Subgroup (primeFormP h (idGram K 6))) (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) (hAT : ∀ α ∈ A, T.map α.toMonoidHom = T) :
    (∃ F ≤ A, Nat.card F = 3 ^ 1 ∧ IsGood 3 F) ∧ (∃ F ≤ A, Nat.card F = 3 ^ 2 ∧ IsGood 3 F) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  have hAD := le_primeFormD_six h (A := A) (fun a ha => hA.2 a ha)
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd h
    Nat.prime_three (by norm_num)
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hω : ζ ^ 2 + ζ + 1 = 0 := by
    have e1 : (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 := by ring
    rw [hζ3, sub_self] at e1
    exact (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 hζ1)
  let Â : Subgroup (primeFormUnitary h (idGram K 6)) := A.comap (primeFormConjHom h (idGram K 6))
  have hmemÂ : ∀ X, X ∈ Â ↔ primeFormConjHom h (idGram K 6) X ∈ A := fun X => Iff.rfl
  obtain ⟨T₂, hT₂2, hT₂, hT₂U, hT₂N⟩ :=
    exists_sylow_two_lift h hT2 hT (Â := Â) (fun X hX => hAT _ ((hmemÂ X).1 hX))
  let ÂG : Subgroup (GL (Fin 6) K) := Â.map (primeFormUnitary h (idGram K 6)).subtype
  have hÂGU : ÂG ≤ primeFormUnitary h (idGram K 6) := Subgroup.map_subtype_le Â
  obtain ⟨W, hW, hWiso, hWÂ⟩ := exists_isotropic_stable h hT₂2 hT₂ hT₂U hÂGU (by
    rintro _ ⟨X, hX, rfl⟩ t ht
    exact hT₂N X hX t ht)
  have hscÂ : ∀ μ : Kˣ, scalarU h 6 μ (norm_eq_one_four h μ) ∈ Â := fun μ => by
    rw [hmemÂ, conjHom_scalarU (by norm_num) hne]
    exact one_mem A
  have hÂ3 : IsPGroup 3 ÂG := by
    rintro ⟨_, X, hX, rfl⟩
    refine ⟨2, ?_⟩
    have h1 : primeFormConjHom h (idGram K 6) (X ^ 3) = 1 := by
      rw [map_pow]
      exact hA.2 _ ((hmemÂ X).1 hX)
    obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 h1
    have e : (X : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) z := by
      rw [← Subgroup.coe_pow, hz]
    apply Subtype.ext
    show (X : GL (Fin 6) K) ^ (3 ^ 2) = 1
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, e, ← map_pow, units_pow_three_four h z,
      map_one]
  have hcard : 81 < Nat.card ÂG := by
    rw [Subgroup.card_map_of_injective (primeFormUnitary h (idGram K 6)).subtype_injective]
    let ψ : Â →* A := MonoidHom.codRestrict ((primeFormConjHom h (idGram K 6)).comp Â.subtype) A
      (fun X => X.2)
    have hψs : Function.Surjective ψ := by
      rintro ⟨a, ha⟩
      obtain ⟨X, rfl⟩ := hAD ha
      exact ⟨⟨X, ha⟩, rfl⟩
    have hker : ψ.ker ≠ ⊥ := by
      intro hbot
      have hmem : (⟨_, hscÂ (Units.mk0 ζ hζ0)⟩ : Â) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext (conjHom_scalarU (by norm_num) hne (Units.mk0 ζ hζ0)
          (norm_eq_one_four h _))
      rw [hbot, Subgroup.mem_bot] at hmem
      have e := congrArg (fun X : Â => (((X : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0) hmem
      simp [coe_scalarU, hζ1] at e
    have h2 : 2 ≤ Nat.card ψ.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hker
    rw [← Subgroup.card_ker_mul_card_of_surjective hψs]
    calc 81 < 2 * 3 ^ 4 := by norm_num
      _ ≤ Nat.card ψ.ker * Nat.card A := Nat.mul_le_mul h2 h81
  obtain ⟨w, hw0, hwW, hwX⟩ := exists_common_eigenvector_six h hÂ3 hÂGU hcard hW hWiso hWÂ
  have hwiso : idForm h 6 w w = 0 := Submodule.mem_orthogonalBilin_iff.mp (hWiso hwW) w hwW
  obtain ⟨X₁, X₂, R, hX₁A, hX₂A, hY₁, hY₂⟩ := exists_frame_six h hω hA h81 hAD hw0 hwiso
    (fun X hX => hwX _ ⟨X, hX, rfl⟩)
  have hconj : ∀ X, primeFormConjHom h (idGram K 6) (R * X * R⁻¹) =
      primeFormConjHom h (idGram K 6) R * primeFormConjHom h (idGram K 6) X *
        (primeFormConjHom h (idGram K 6) R)⁻¹ := fun X => by rw [map_mul, map_mul, map_inv]
  have hY₀ : ((((R * X₁ * R⁻¹) * (R * X₂ * R⁻¹) : primeFormUnitary h (idGram K 6)) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ζ, ζ] := by
    have hfun : (fun i => (![1, 1, 1, 1, ζ, 1] : Fin 6 → K) i *
        (![1, 1, 1, 1, 1, ζ] : Fin 6 → K) i) = ![1, 1, 1, 1, ζ, ζ] := by
      funext i
      fin_cases i <;> simp
    rw [Subgroup.coe_mul, Units.val_mul, hY₁, hY₂, Matrix.diagonal_mul_diagonal, hfun]
  have he₀ : ∀ i : Fin 6, (i : ℕ) < 4 → (![1, 1, 1, 1, ζ, ζ] : Fin 6 → K) i = 1 := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact absurd hi (by decide)
  have he₁ : ∀ i : Fin 6, (i : ℕ) < 4 → (![1, 1, 1, 1, ζ, 1] : Fin 6 → K) i = 1 := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact absurd hi (by decide)
  have he₂ : ∀ i : Fin 6, (i : ℕ) < 4 → (![1, 1, 1, 1, 1, ζ] : Fin 6 → K) i = 1 := by
    intro i hi
    fin_cases i
    all_goals first | rfl | exact absurd hi (by decide)
  have hone : (((1 : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => 1) := by
    rw [Subgroup.coe_one, Units.val_one, Matrix.diagonal_one]
  have ha₁ : primeFormConjHom h (idGram K 6) X₁ ≠ 1 := by
    intro h1
    have e := diag_entries_of_conjHom_eq_six h hY₁ hone
      (by rw [hconj, h1, map_one]; group) 0 4
    simp at e
    exact hζ1 e.symm
  have ha₂ : primeFormConjHom h (idGram K 6) X₂ ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K 6) X₁) := by
    intro hm
    have hfin : IsOfFinOrder (primeFormConjHom h (idGram K 6) X₁) :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hA.2 _ hX₁A⟩
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hm)
    have hck : primeFormConjHom h (idGram K 6) ((R * X₁ * R⁻¹) ^ k) =
        primeFormConjHom h (idGram K 6) (R * X₂ * R⁻¹) := by
      rw [map_pow, hconj, hconj, ← hk, conj_pow]
    have hYk : ((((R * X₁ * R⁻¹) ^ k : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal ((![1, 1, 1, 1, ζ, 1] : Fin 6 → K) ^ k) := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hY₁, Matrix.diagonal_pow]
    have e := diag_entries_of_conjHom_eq_six h hYk hY₂ hck 0 5
    simp at e
    exact hζ1 e
  have hx1 : primeFormConjHom h (idGram K 6) X₁ * primeFormConjHom h (idGram K 6) X₂ ≠ 1 := by
    intro h1
    have e := diag_entries_of_conjHom_eq_six h hY₀ hone
      (by rw [map_mul, hconj, hconj, map_one, eq_inv_of_mul_eq_one_right h1]; group) 0 4
    simp at e
    exact hζ1 e.symm
  have hxA : primeFormConjHom h (idGram K 6) X₁ * primeFormConjHom h (idGram K 6) X₂ ∈ A :=
    mul_mem hX₁A hX₂A
  have hgx : primeFormConjHom h (idGram K 6) R *
      (primeFormConjHom h (idGram K 6) X₁ * primeFormConjHom h (idGram K 6) X₂) *
        (primeFormConjHom h (idGram K 6) R)⁻¹ =
      primeFormConjHom h (idGram K 6) ((R * X₁ * R⁻¹) * (R * X₂ * R⁻¹)) := by
    rw [map_mul, hconj, hconj]
    group
  obtain ⟨x, hxdef⟩ : ∃ x : MulAut (primeFormP h (idGram K 6)),
      x = primeFormConjHom h (idGram K 6) X₁ * primeFormConjHom h (idGram K 6) X₂ := ⟨_, rfl⟩
  rw [← hxdef] at hx1 hxA hgx
  refine ⟨⟨Subgroup.closure ({x, x} : Set (MulAut (primeFormP h (idGram K 6)))), ?_, ?_, ?_⟩,
    ⟨Subgroup.closure ({primeFormConjHom h (idGram K 6) X₁, primeFormConjHom h (idGram K 6) X₂} :
      Set (MulAut (primeFormP h (idGram K 6)))), ?_, ?_, ?_⟩⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl) <;> exact hxA
  · rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (hA.2 _ hxA) hx1
  · apply HDescLinRes.isGood_closure_pair
    apply HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three (primeFormConjHom h (idGram K 6) R)
    rw [hgx, inf_idem]
    exact glaPLayer_ne_bot_six h hω hY₀ le_rfl
      (fun g hg => mk_mem_fixSubgroup_of_block h hY₀ he₀ g hg)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hX₁A
    · exact hX₂A
  · exact card_closure_pair_eq_nine hA hX₁A hX₂A ha₁ ha₂
  · apply HDescLinRes.isGood_closure_pair
    apply HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three (primeFormConjHom h (idGram K 6) R)
    rw [← hconj, ← hconj]
    refine glaPLayer_ne_bot_six h hω hY₀ ?_ ?_
    · intro p hp
      obtain ⟨hp₁, hp₂⟩ := Subgroup.mem_inf.1 hp
      rw [mem_fixSubgroup] at hp₁ hp₂ ⊢
      rw [map_mul, MulAut.mul_apply, hp₂, hp₁]
    · intro g hg
      exact Subgroup.mem_inf.2 ⟨mk_mem_fixSubgroup_of_block h hY₁ he₁ g hg,
        mk_mem_fixSubgroup_of_block h hY₂ he₂ g hg⟩

theorem goodSub_primeFormP_six_of_eq {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    (hf : f = 1) (A : Subgroup (MulAut (primeFormP h (idGram K 6)))) (hA : IsElemAbelian 3 A)
    (h81 : 3 ^ 4 ≤ Nat.card A) (T : Subgroup (primeFormP h (idGram K 6))) (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) (hAT : ∀ α ∈ A, T.map α.toMonoidHom = T) :
    (∃ F ≤ A, Nat.card F = 3 ^ 1 ∧ IsGood 3 F) ∧ (∃ F ≤ A, Nat.card F = 3 ^ 2 ∧ IsGood 3 F) := by
  subst hℓ hf
  exact goodSub_primeFormP_six h A hA h81 T hT2 hT hAT

end Six

section Transport

private def GoodSubPow (S : Type) [Group S] [Finite S] (n k : ℕ) : Prop :=
  ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → 3 ^ n ≤ Nat.card A →
    ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → (∀ α ∈ A, T.map α.toMonoidHom = T) →
      ∃ F ≤ A, Nat.card F = 3 ^ k ∧ IsGood 3 F

private theorem GoodSubPow.of_mulEquiv {S S' : Type} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') {n k : ℕ} (h : GoodSubPow S n k) : GoodSubPow S' n k := by
  intro A' hA' hcard T' hT2 hT hAT
  let c : MulAut S ≃* MulAut S' := MulAut.congr e
  let A : Subgroup (MulAut S) := A'.map (c.symm : MulAut S' →* MulAut S)
  have hAel : IsElemAbelian 3 A := hA'.map _
  have hAcard : 3 ^ n ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective c.symm.injective]
    exact hcard
  let T : Subgroup S := T'.map (e.symm : S' →* S)
  have hT2' : IsPGroup 2 T := hT2.map _
  have hT' : T ≠ ⊥ := fun hbot =>
    hT ((Subgroup.map_eq_bot_iff_of_injective T' e.symm.injective).1 hbot)
  have hAT' : ∀ α ∈ A, T.map α.toMonoidHom = T := by
    rintro _ ⟨α', hα', rfl⟩
    have hcomp : (((c.symm α' : MulAut S) : S ≃* S).toMonoidHom.comp (e.symm : S' →* S)) =
        (e.symm : S' →* S).comp α'.toMonoidHom := by
      ext g
      change e.symm (α' (e (e.symm g))) = e.symm (α' g)
      rw [e.apply_symm_apply]
    change (T'.map (e.symm : S' →* S)).map (c.symm α').toMonoidHom = T'.map (e.symm : S' →* S)
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hAT α' hα']
  obtain ⟨F, hFA, hFk, hFg⟩ := h A hAel hAcard T hT2' hT' hAT'
  refine ⟨F.map (MulAut.congr e).toMonoidHom, ?_, ?_,
    HDescLinRes.isGood_map_mulAutCongr e hFg⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a', ha', rfl⟩ := hFA hf
    show c (c.symm a') ∈ A'
    rw [c.apply_symm_apply]
    exact ha'
  · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact hFk

end Transport

theorem goodSubAtLow_twistedA_five (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (h2 : q.card = 2) :
    HDesc.GoodSubAtLow 3 ⟨.twistedA 5 q, hv⟩ 1 ∧ HDesc.GoodSubAtLow 3 ⟨.twistedA 5 q, hv⟩ 2 := by
  obtain ⟨r, q', K, _, hU, -, hdA, -, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := ⟨.twistedA 5 q, hv⟩) trivial
  injection hdA with hr hqq
  subst hr hqq
  haveI := hU.finite
  have hq2 : q.p ^ q.exponent = 2 ^ 1 := by
    rw [← TauCeti.PrimePower.card_def, h2, pow_one]
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ 1 := hq2 ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have he1 : q.exponent = 1 := by
    rw [hp2] at hq2
    exact Nat.pow_right_injective (le_refl 2) hq2
  haveI : CharP K 2 := by
    haveI := hU.charP
    exact CharP.congr q.p hp2
  have hS1 : GoodSubPow (primeFormP hU (idGram K 6)) 4 1 := fun A hA h81 T hT2 hT hAT =>
    (goodSub_primeFormP_six_of_eq hU hp2 he1 A hA h81 T hT2 hT hAT).1
  have hS2 : GoodSubPow (primeFormP hU (idGram K 6)) 4 2 := fun A hA h81 T hT2 hT hAT =>
    (goodSub_primeFormP_six_of_eq hU hp2 he1 A hA h81 T hT2 hT hAT).2
  refine ⟨fun _ A hA _ hl T hT2 hT hAT =>
      GoodSubPow.of_mulEquiv eP hS1 A hA (hl 4 ⟨by simp [hp2, he1], rfl⟩) T hT2 hT hAT,
    fun _ A hA _ hl T hT2 hT hAT =>
      GoodSubPow.of_mulEquiv eP hS2 A hA (hl 4 ⟨by simp [hp2, he1], rfl⟩) T hT2 hT hAT⟩

theorem unitaryRes_holds : HDesc.UnitaryRes :=
  ⟨unitaryRes_twistedA_two, goodSubAt_twistedA_three, goodSubAtLow_twistedA_five⟩

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

end
