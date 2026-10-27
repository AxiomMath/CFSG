module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalMain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalHeis
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField


public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Chevalley CFSG.RankThree.Classical CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Plane

theorem exists_lift_pair_of_plane (hp : p.Prime)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) (hEl : E ≤ primeFormD h (idGram K n)) :
    ∃ A B : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E ∧
      primeFormConjHom h (idGram K n) B ∈ E ∧ primeFormConjHom h (idGram K n) A ≠ 1 ∧
      primeFormConjHom h (idGram K n) B ∉
        Subgroup.zpowers (primeFormConjHom h (idGram K n) A) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hE1 : E ≠ ⊥ := by
    intro h'
    rw [h', Subgroup.card_bot] at hcard
    exact absurd hcard.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨⟨X, hXE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  obtain ⟨Y, hYE, hYX⟩ : ∃ Y ∈ E, Y ∉ Subgroup.zpowers X := by
    by_contra hall
    push Not at hall
    have hXp : X ^ p = 1 := hE.2 X hXE
    have : Finite (Subgroup.zpowers X) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hXp⟩)).ne'
    have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers X from hall)
    rw [Nat.card_zpowers] at h1
    have h2 := h1.trans (orderOf_le_of_pow_eq_one hp.pos hXp)
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨A, hA⟩ := hEl hXE
  obtain ⟨B, hB⟩ := hEl hYE
  refine ⟨A, B, hA ▸ hXE, hB ▸ hYE, ?_, ?_⟩
  · rw [hA]
    exact fun h' => hx1 (Subtype.ext h')
  · rw [hA, hB]
    exact hYX


end Plane

section Twisted

theorem exists_scalar_of_commute_conj (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {α : MulAut (primeFormP h (idGram K n))} {Y : primeFormUnitary h (idGram K n)}
    (hα : α * primeFormConjHom h (idGram K n) Y = primeFormConjHom h (idGram K n) Y * α) :
    ∃ d : Kˣ, idAct' h n hn hne α ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := conj_primeFormConjHom' hn hne α Y
  have h2 : α * primeFormConjHom h (idGram K n) Y * α⁻¹ = primeFormConjHom h (idGram K n) Y := by
    rw [hα, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : primeFormConjHom h (idGram K n) (Y⁻¹ * idActU' h n hn hne α Y) = 1 := by
    rw [map_mul, map_inv, ← h1, h2, inv_mul_cancel]
  obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h3
  refine ⟨d, ?_⟩
  have h4 : ((idActU' h n hn hne α Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      (Y : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) d := by
    have : ((Y⁻¹ * idActU' h n hn hne α Y : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) d := hd
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this, mul_inv_cancel_left]
  rw [← coe_idActU' hn hne, h4]
  rfl

theorem idAct'_psi_apply (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K) (Y : Matrix (Fin n) (Fin n) K) :
    idAct' h n hn hne (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) Y =
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y.map τ *
        (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [idAct'_primeFormPsi, idMatAction_mk]


end Twisted

section Field

theorem eq_one_of_fixes_cube_root (h : UnitaryFieldData 2 3 K) {τ : K ≃+* K} {c : Kˣ}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hτc : τ (c : K) = c)
    (hcop : Nat.Coprime 3 (orderOf τ)) : τ = 1 := by
  have := h.finite
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (K := K)
    Nat.prime_two (by omega : 1 ≤ 2 * 3) (by simpa using h.card) τ
  have hm6 : orderOf τ ≤ 6 := Nat.le_of_dvd (by omega) hdvd
  have hm : orderOf τ = 1 ∨ orderOf τ = 2 := by
    generalize orderOf τ = m at hdvd hm6 hcop hcard
    interval_cases m <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd hcop; decide)
  rcases hm with hm | hm
  · exact orderOf_eq_one_iff.mp hm
  · exfalso
    rw [hm] at hcard
    have hcfix : (c : K) ∈ fixSubfield τ := hτc
    have hne0 : (⟨(c : K), hcfix⟩ : fixSubfield τ) ≠ 0 := fun h0 => c.ne_zero (by
      simpa using congrArg Subtype.val h0)
    let u : (fixSubfield τ)ˣ := Units.mk0 ⟨(c : K), hcfix⟩ hne0
    have hu3 : u ^ 3 = 1 := by
      apply Units.ext
      apply Subtype.ext
      simp only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, Units.val_one,
        OneMemClass.coe_one]
      change (c : K) ^ 3 = 1
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    have hu1 : u ≠ 1 := by
      intro h1
      apply hc1
      apply Units.ext
      have := congrArg (fun z : (fixSubfield τ)ˣ => ((z : fixSubfield τ) : K)) h1
      simpa [u] using this
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have h3 := orderOf_dvd_natCard u
    rw [hord, Nat.card_units, hcard] at h3
    norm_num at h3

theorem smul_matrix_cancel {m : ℕ} [NeZero m] {M : Matrix (Fin m) (Fin m) K} (hM : IsUnit M)
    {x y : K} (hxy : x • M = y • M) : x = y := by
  have h1 : (x - y) • M = 0 := by rw [sub_smul, hxy, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exfalso
    obtain ⟨u, rfl⟩ := hM
    have := congrArg (fun N : Matrix (Fin m) (Fin m) K => N * ((u⁻¹ : (Matrix (Fin m) (Fin m) K)ˣ) :
      Matrix (Fin m) (Fin m) K)) h2
    simp only [Units.mul_inv, zero_mul] at this
    exact one_ne_zero this


theorem scalar_coe_eq_smul_one {m : ℕ} (d : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin m) d : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (d : K) • (1 : Matrix (Fin m) (Fin m) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem pow_three_eq_one_of_conj {A Y : GL (Fin 3) K} {d a : Kˣ}
    (hA3 : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) a)
    (hYA : Y * A * Y⁻¹ = A * GeneralLinearGroup.scalar (Fin 3) d) : d ^ 3 = 1 := by
  have h1 : (Y * A * Y⁻¹) ^ 3 = GeneralLinearGroup.scalar (Fin 3) a := by
    rw [conj_pow, hA3, ← GeneralLinearGroup.scalar_commute a Y, mul_assoc, mul_inv_cancel,
      mul_one]
  have hc : Commute A (GeneralLinearGroup.scalar (Fin 3) d) :=
    (GeneralLinearGroup.scalar_commute d A).symm
  have h2 : (Y * A * Y⁻¹) ^ 3 = A ^ 3 * GeneralLinearGroup.scalar (Fin 3) (d ^ 3) := by
    rw [hYA, hc.mul_pow, map_pow]
  rw [hA3] at h2
  have h3 : GeneralLinearGroup.scalar (Fin 3) (d ^ 3) = (1 : GL (Fin 3) K) := by
    have := h1.symm.trans h2
    exact (mul_eq_left.mp this.symm)
  have h4 : GeneralLinearGroup.scalar (Fin 3) (d ^ 3) = GeneralLinearGroup.scalar (Fin 3) 1 := by
    rw [h3, map_one]
  exact glScalar_injective (by norm_num) h4


end Field

section Heis

theorem eq_one_of_commute_heisenberg (h : UnitaryFieldData 2 3 K)
    {A B : primeFormUnitary h (idGram K 3)} {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hAB : (A : GL (Fin 3) K) * B = B * A * GeneralLinearGroup.scalar (Fin 3) c)
    (hA3 : primeFormConjHom h (idGram K 3) A ^ 3 = 1)
    (hB3 : primeFormConjHom h (idGram K 3) B ^ 3 = 1)
    (hρ : primeFormConjHom h (idGram K 3) A * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) A)
    {g : MulAut (primeFormP h (idGram K 3))}
    (hgA : g * primeFormConjHom h (idGram K 3) A = primeFormConjHom h (idGram K 3) A * g)
    (hgB : g * primeFormConjHom h (idGram K 3) B = primeFormConjHom h (idGram K 3) B * g)
    (hcop : Nat.Coprime 3 (orderOf g)) : g = 1 := by
  classical
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by decide
  have := h.finite
  obtain ⟨⟨M', τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne g
  set Ψ := primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 3)) ⟨M', τ⟩ with hΨ
  obtain ⟨dA, hdA⟩ := exists_scalar_of_commute_conj hn hne hgA
  obtain ⟨dB, hdB⟩ := exists_scalar_of_commute_conj hn hne hgB
  have hτc : τ (c : K) = c := by
    have hmA : idAct' h 3 hn hne Ψ ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (dA : K) • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hdA, scalar_coe_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
    have hmB : idAct' h 3 hn hne Ψ ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (dB : K) • ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hdB, scalar_coe_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
    have hmc : idAct' h 3 hn hne Ψ ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) =
        (τ (c : K)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [idAct'_psi_apply]
      have e1 : ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)).map τ =
          (τ (c : K)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      have e2 : ((M' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((M' : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, e2]
    have hAB' : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hAB
      simp only [Units.val_mul, scalar_coe_eq_smul_one] at this
      exact this
    have hφ := congrArg (idAct' h 3 hn hne Ψ) hAB'
    rw [map_mul, map_mul, map_mul, hmA, hmB, hmc] at hφ
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hφ
    rw [hAB'] at hφ
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul] at hφ
    have hunit : IsUnit (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      have := Units.isUnit ((B : GL (Fin 3) K) * (A : GL (Fin 3) K))
      rwa [Units.val_mul] at this
    have key := smul_matrix_cancel hunit hφ
    have hd : (dA : K) * dB ≠ 0 := mul_ne_zero dA.ne_zero dB.ne_zero
    exact (mul_left_cancel₀ hd (by linear_combination key)).symm
  have hFΨ : primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3)) hn hne Ψ = τ :=
    primeFormFieldFactor_psi h (isPrimeFormGram_idGram (K := K) (n := 3)) hn hne ⟨M', τ⟩
  have hcopτ : Nat.Coprime 3 (orderOf τ) := by
    have hd := orderOf_map_dvd (primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := 3))
      hn hne) Ψ
    rw [hFΨ] at hd
    exact Nat.Coprime.coprime_dvd_right hd hcop
  have hτ1 : τ = RingEquiv.refl K := eq_one_of_fixes_cube_root h hc3 hc1 hτc hcopτ
  subst hτ1
  have hΨ' : Ψ = primeFormConjHom h (idGram K 3) M' := by rw [hΨ]; exact psi_refl_eq M'
  rw [hΨ'] at hdA hdB hgA hgB hcop ⊢
  rw [idAct'_primeFormConjHom hn hne] at hdA hdB
  have hYA : (M' : GL (Fin 3) K) * (A : GL (Fin 3) K) * (M' : GL (Fin 3) K)⁻¹ =
      (A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) dA := Units.ext (by
    simpa using hdA)
  have hYB : (M' : GL (Fin 3) K) * (B : GL (Fin 3) K) * (M' : GL (Fin 3) K)⁻¹ =
      (B : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) dB := Units.ext (by
    simpa using hdB)
  have hcube : ∀ {X : primeFormUnitary h (idGram K 3)},
      primeFormConjHom h (idGram K 3) X ^ 3 = 1 →
        ∃ a : Kˣ, (X : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) a := by
    intro X hX
    have h1 : primeFormConjHom h (idGram K 3) (X ^ 3) = 1 := by rw [map_pow]; exact hX
    obtain ⟨a, -, ha⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
    exact ⟨a, by simpa using ha⟩
  obtain ⟨a, ha⟩ := hcube hA3
  obtain ⟨b, hb⟩ := hcube hB3
  obtain ⟨i, j, m, hY⟩ := heisenberg_normalizer hc3 hc1 hAB (pow_three_eq_one_of_conj ha hYA)
    (pow_three_eq_one_of_conj hb hYB) hYA hYB
  obtain ⟨Z, hZ⟩ : ∃ Z : primeFormUnitary h (idGram K 3), Z = (A ^ i * B ^ j)⁻¹ * M' :=
    ⟨_, rfl⟩
  have hZm : (Z : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) m := by
    rw [hZ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_pow, hY]
    group
  have hZn : h.norm (m : K) = 1 := by
    refine norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num : 1 ≤ 3) 1 ?_
    rw [← hZm]
    exact Z.2
  have hρZ : primeFormConjHom h (idGram K 3) Z = 1 :=
    (primeFormConjHom_eq_one_iff_of_ne hn hne Z).mpr
      ⟨m, (pow_succ_eq_one_iff_norm h m).mpr hZn, hZm⟩
  have hρM : primeFormConjHom h (idGram K 3) M' =
      primeFormConjHom h (idGram K 3) A ^ i * primeFormConjHom h (idGram K 3) B ^ j := by
    have hMX : M' = (A ^ i * B ^ j) * Z := by rw [hZ, mul_inv_cancel_left]
    rw [hMX, map_mul, hρZ, mul_one, map_mul, map_pow, map_pow]
  have hmem : primeFormConjHom h (idGram K 3) M' ∈ Subgroup.closure
      {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} := by
    rw [hρM]
    have hAm : primeFormConjHom h (idGram K 3) A ∈ Subgroup.closure
        {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hBm : primeFormConjHom h (idGram K 3) B ∈ Subgroup.closure
        {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact mul_mem (pow_mem hAm i) (pow_mem hBm j)
  have hg3 := (closure_pair_comm_and_pow_eq_one hρ hA3 hB3).2 _ hmem
  have hord : orderOf (primeFormConjHom h (idGram K 3) M') ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm hord)


end Heis

section Main

theorem cube_eq_one_of_commutator {A B : GL (Fin 3) K} {a c : Kˣ}
    (ha : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) a)
    (hAB : A * B = B * A * GeneralLinearGroup.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have h1 : A ^ 3 * B * (A ^ 3)⁻¹ = B * GeneralLinearGroup.scalar (Fin 3) (c ^ 3) :=
    HeisAux.W_pow_left (HeisAux.WAB hAB) 3
  rw [ha, GeneralLinearGroup.scalar_commute a B, mul_assoc, mul_inv_cancel, mul_one] at h1
  have h2 : GeneralLinearGroup.scalar (Fin 3) (c ^ 3) = (1 : GL (Fin 3) K) :=
    mul_eq_left.mp h1.symm
  exact glScalar_injective (by norm_num) (h2.trans (map_one _).symm)

theorem diagUnitaryBalanceOuter_holds : DiagUnitaryBalanceOuter := by
  classical
  intro ℓ f K _ h hq p hp hp2 hpℓ hpq hp3 hq0 D hD hcard hDl H hH hDH
  have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  subst hp3'
  obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0
  subst hℓ2
  have hn : 3 ≤ 3 := le_rfl
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_idGram
  have := h.finite
  obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
  have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
  have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
  have hσ1 : primeFormFieldFactor h hC hn hq x ≠ 1 := fun h1 => hxl (by
    rw [← ker_primeFormFieldFactor h hC hn hq]
    exact h1)
  have hσ : orderOf (primeFormFieldFactor h hC hn hq x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
  have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
  have hf : f = 3 := by omega
  subst hf
  have hq3 : 3 < 2 ^ 3 := by norm_num
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨E, hED, hEl, hE, hEcard⟩ := exists_plane_of_hom_cyclic hp
    (primeFormD h (idGram K 3)) hD hcard
    ((primeFormFieldFactor h hC hn hq).comp D.subtype) fun y hy => by
      rw [← ker_primeFormFieldFactor h hC hn hq]
      exact hy
  obtain ⟨A, B, hAE, hBE, hA1, hBA⟩ := exists_lift_pair_of_plane hp hE hEcard hEl
  have hAD := hED hAE
  have hBD := hED hBE
  have hAp : primeFormConjHom h (idGram K 3) A ^ 3 = 1 := hD.2 _ hAD
  have hBp : primeFormConjHom h (idGram K 3) B ^ 3 = 1 := hD.2 _ hBD
  have hρ : primeFormConjHom h (idGram K 3) A * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) A :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hAD⟩ ⟨_, hBD⟩)
  have hED' : Subgroup.closure {primeFormConjHom h (idGram K 3) A,
      primeFormConjHom h (idGram K 3) B} ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAD
    · exact hBD
  have hcom : primeFormConjHom h (idGram K 3) (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ]
    group
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp hcom
  have hAB : (A : GL (Fin 3) K) * B = B * A * GeneralLinearGroup.scalar (Fin 3) c := by
    have h1 : (A : GL (Fin 3) K) * B * (A : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by simpa using hc
    calc (A : GL (Fin 3) K) * B = GeneralLinearGroup.scalar (Fin 3) c * (B * A) := by
          rw [← h1]; group
      _ = B * A * GeneralLinearGroup.scalar (Fin 3) c :=
          GeneralLinearGroup.scalar_commute c _
  by_cases hc1 : c = 1
  ·
    subst hc1
    have hABc : A * B = B * A := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
    have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hq hq3 hp hp2 hpq hABc hAp hBp hA1 hBA hH
    exact le_bot_iff.1 ((localDeltaIn_antitone H hED').trans hbot.le)
  ·
    obtain ⟨a, -, ha⟩ : ∃ a : Kˣ, h.norm (a : K) = 1 ∧
        (A : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) a := by
      have h1 : primeFormConjHom h (idGram K 3) (A ^ 3) = 1 := by rw [map_pow]; exact hAp
      obtain ⟨a, ha, hA'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp h1
      exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hA'⟩
    have hc3 := cube_eq_one_of_commutator ha hAB
    refine eq_bot_iff.2 fun g hg => ?_
    rw [Subgroup.mem_bot]
    exact eq_one_of_commute_heisenberg h hc3 hc1 hAB hAp hBp hρ
      (commute_of_mem_localDeltaIn hg hAD) (commute_of_mem_localDeltaIn hg hBD)
      (coprime_orderOf_of_mem_localDeltaIn hp hg hAD hA1)

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
