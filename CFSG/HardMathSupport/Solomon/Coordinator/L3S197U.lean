module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUTransport
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.Coordinator CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem seitz_model_primeForm (h : UnitaryFieldData ℓ f K) (hq : 2 < ℓ ^ f) (hq8 : ℓ ^ f ≠ 8)
    (hmod : ℓ ^ f % 3 = 2) {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) (hne : localDeltaIn 3 H D ≠ ⊥) :
    D ≤ primeFormD h (idGram K 3) ∧
      (∀ Y : primeFormUnitary h (idGram K 3),
        (∀ d ∈ D, primeFormConjHom h (idGram K 3) Y * d =
          d * primeFormConjHom h (idGram K 3) Y) →
          primeFormConjHom h (idGram K 3) Y ∈ D) ∧
      ∃ A B : primeFormUnitary h (idGram K 3), primeFormConjHom h (idGram K 3) A ∈ D ∧
        primeFormConjHom h (idGram K 3) B ∈ D ∧ A * B ≠ B * A := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn : 3 ≤ 3 := le_rfl
  have hne2 : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  have := h.finite
  have hℓ := h.prime
  have hpq : 3 ∣ ℓ ^ f + 1 := by omega
  have hq3 : 3 < ℓ ^ f := by omega
  have hDl : D ≤ primeFormD h (idGram K 3) := by
    by_contra hDl
    by_cases hq0 : ℓ ^ (f / 3) = 2
    · have hℓ2 : ℓ = 2 := by
        have := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0
        exact this.1
      subst hℓ2
      have hf1 : f / 3 = 1 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0).2
      have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
      obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
      have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
      have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
      have hσ1 : primeFormFieldFactor h hC hn hne2 x ≠ 1 := fun h1 => hxl (by
        rw [← ker_primeFormFieldFactor h hC hn hne2]
        exact h1)
      have hσ : orderOf (primeFormFieldFactor h hC hn hne2 x) = 3 :=
        orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
      obtain ⟨-, -, -, -, -, M, hM⟩ :=
        unitary_prime_semilinear_field_descent' h hn hne2 hp hp2 x hxp _ rfl hσ
      have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
      have hf3 : f = 3 := by omega
      subst hf3
      exact hq8 (by norm_num)
    · exact hne (localDeltaIn_eq_bot_of_not_le_primeFormD_three h hne2 (by omega) hD hDl hH)
  obtain ⟨A, B, hAE, hBE, hA1, hBA⟩ := exists_lift_pair_of_plane hp hD hcard hDl
  have hAp : primeFormConjHom h (idGram K 3) A ^ 3 = 1 := hD.2 _ hAE
  have hBp : primeFormConjHom h (idGram K 3) B ^ 3 = 1 := hD.2 _ hBE
  have hρ : primeFormConjHom h (idGram K 3) A * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) A :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hAE⟩ ⟨_, hBE⟩)
  have hED' : Subgroup.closure {primeFormConjHom h (idGram K 3) A,
      primeFormConjHom h (idGram K 3) B} ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAE
    · exact hBE
  have hcom : primeFormConjHom h (idGram K 3) (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ]
    group
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne2 _).mp hcom
  have hAB : (A : GL (Fin 3) K) * B = B * A * GeneralLinearGroup.scalar (Fin 3) c := by
    have h1 : (A : GL (Fin 3) K) * B * (A : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by simpa using hc
    calc (A : GL (Fin 3) K) * B = GeneralLinearGroup.scalar (Fin 3) c * (B * A) := by
          rw [← h1]; group
      _ = B * A * GeneralLinearGroup.scalar (Fin 3) c :=
          GeneralLinearGroup.scalar_commute c _
  have hnc : A * B ≠ B * A := by
    intro hABc
    have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hne2 hq3 hp hp2 hpq hABc hAp hBp hA1 hBA
      hH
    exact hne (le_bot_iff.1 ((localDeltaIn_antitone H hED').trans hbot.le))
  have hc1 : c ≠ 1 := by
    intro hc1
    subst hc1
    apply hnc
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
  refine ⟨hDl, ?_, A, B, hAE, hBE, hnc⟩
  intro Y hYc
  obtain ⟨a, -, ha⟩ : ∃ a : Kˣ, h.norm (a : K) = 1 ∧
      (A : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) a := by
    have h1 : primeFormConjHom h (idGram K 3) (A ^ 3) = 1 := by rw [map_pow]; exact hAp
    obtain ⟨a, ha, hA'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne2 _).mp h1
    exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hA'⟩
  obtain ⟨b, -, hb⟩ : ∃ b : Kˣ, h.norm (b : K) = 1 ∧
      (B : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) b := by
    have h1 : primeFormConjHom h (idGram K 3) (B ^ 3) = 1 := by rw [map_pow]; exact hBp
    obtain ⟨b, hb, hB'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne2 _).mp h1
    exact ⟨b, (pow_succ_eq_one_iff_norm h b).mp hb, by simpa using hB'⟩
  have hc3 := cube_eq_one_of_commutator ha hAB
  have hgA : primeFormConjHom h (idGram K 3) Y * primeFormConjHom h (idGram K 3) A =
      primeFormConjHom h (idGram K 3) A * primeFormConjHom h (idGram K 3) Y := hYc _ hAE
  have hgB : primeFormConjHom h (idGram K 3) Y * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) Y := hYc _ hBE
  have hnorm : ∀ {X : primeFormUnitary h (idGram K 3)},
      primeFormConjHom h (idGram K 3) Y * primeFormConjHom h (idGram K 3) X =
        primeFormConjHom h (idGram K 3) X * primeFormConjHom h (idGram K 3) Y →
      ∃ d : Kˣ, (Y : GL (Fin 3) K) * X * (Y : GL (Fin 3) K)⁻¹ =
        X * GeneralLinearGroup.scalar (Fin 3) d := by
    intro X hX
    have h1 : primeFormConjHom h (idGram K 3) (Y * X * Y⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hX]
      group
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne2 _).mp h1
    refine ⟨d, ?_⟩
    have h2 : (Y : GL (Fin 3) K) * X * (Y : GL (Fin 3) K)⁻¹ * (X : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) d := by simpa using hd
    calc (Y : GL (Fin 3) K) * X * (Y : GL (Fin 3) K)⁻¹
        = GeneralLinearGroup.scalar (Fin 3) d * X := by rw [← h2]; group
      _ = X * GeneralLinearGroup.scalar (Fin 3) d := GeneralLinearGroup.scalar_commute d _
  obtain ⟨dA, hdA⟩ := hnorm hgA
  obtain ⟨dB, hdB⟩ := hnorm hgB
  obtain ⟨i, j, m, hYm⟩ := heisenberg_normalizer hc3 hc1 hAB (pow_three_eq_one_of_conj ha hdA)
    (pow_three_eq_one_of_conj hb hdB) hdA hdB
  obtain ⟨Z, hZ⟩ : ∃ Z : primeFormUnitary h (idGram K 3), Z = (A ^ i * B ^ j)⁻¹ * Y :=
    ⟨_, rfl⟩
  have hZm : (Z : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) m := by
    rw [hZ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_pow, hYm]
    group
  have hZn : h.norm (m : K) = 1 := by
    refine norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num : 1 ≤ 3) 1 ?_
    rw [← hZm]
    exact Z.2
  have hρZ : primeFormConjHom h (idGram K 3) Z = 1 :=
    (primeFormConjHom_eq_one_iff_of_ne hn hne2 Z).mpr
      ⟨m, (pow_succ_eq_one_iff_norm h m).mpr hZn, hZm⟩
  have hρM : primeFormConjHom h (idGram K 3) Y =
      primeFormConjHom h (idGram K 3) A ^ i * primeFormConjHom h (idGram K 3) B ^ j := by
    have hMX : Y = (A ^ i * B ^ j) * Z := by rw [hZ, mul_inv_cancel_left]
    rw [hMX, map_mul, hρZ, mul_one, map_mul, map_pow, map_pow]
  rw [hρM]
  exact mul_mem (pow_mem hAE i) (pow_mem hBE j)

theorem mem_unitaryIsom3_of_mem_primeFormUnitary (h : UnitaryFieldData ℓ f K) {A : GL (Fin 3) K}
    (hA : A ∈ primeFormUnitary h (idGram K 3)) : A ∈ unitaryIsom3 h := by
  have hA' : ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (idGram K 3) *
      (A : Matrix (Fin 3) (Fin 3) K) = idGram K 3 := hA
  rw [show idGram K 3 = 1 from rfl, Matrix.mul_one] at hA'
  exact hA'

theorem seitz_model_U (h : UnitaryFieldData ℓ f K) (hq : 2 < ℓ ^ f) (hq8 : ℓ ^ f ≠ 8)
    (hmod : ℓ ^ f % 3 = 2) {D H : Subgroup (MulAut (unitaryPSU h 3))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hH : innerAut (unitaryPSU h 3) ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) :
    D ≤ (psuConj h).range ∧
      (∀ A : unitaryIsom3 h, (∀ d ∈ D, psuConj h A * d = d * psuConj h A) → psuConj h A ∈ D) ∧
      ∃ A B : unitaryIsom3 h, psuConj h A ∈ D ∧ psuConj h B ∈ D ∧ A * B ≠ B * A := by
  set φ : MulAut (unitaryPSU h 3) ≃* MulAut (primeFormP h (idGram K 3)) :=
    MulAut.congr (psuToPrimeForm h) with hφ
  have hcard9 : Nat.card D = 3 ^ 2 := by rw [hcard]; norm_num
  have hD' : IsElemAbelian 3 (D.map φ.toMonoidHom) :=
    (isEkIn_map_mulEquiv 3 2 φ (A := ⊤) (D := D) ⟨le_top, hD, hcard9⟩).2.1
  have hcard' : Nat.card (D.map φ.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hcard9]
  have hH' : innerAut (primeFormP h (idGram K 3)) ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj ((psuToPrimeForm h).symm x), hH ⟨_, rfl⟩, ?_⟩
    change MulAut.congr (psuToPrimeForm h) (MulAut.conj ((psuToPrimeForm h).symm x)) =
      MulAut.conj x
    rw [congr_conj_apply, MulEquiv.apply_symm_apply]
  have hne' : localDeltaIn 3 (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) ≠ ⊥ := by
    rw [localDeltaIn_map_mulEquiv]
    intro hb
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 hb)
  obtain ⟨hDl, hM2, A, B, hA, hB, hAB⟩ := seitz_model_primeForm h hq hq8 hmod hD' hcard' hH' hne'
  have hpre : ∀ d : MulAut (unitaryPSU h 3), d ∈ D → ∀ Y : primeFormUnitary h (idGram K 3),
      φ d = primeFormConjHom h (idGram K 3) Y →
        d = psuConj h ⟨Y, mem_unitaryIsom3_of_mem_primeFormUnitary h Y.2⟩ := by
    intro d _ Y hdY
    apply φ.injective
    rw [hdY]
    exact (congr_psuConj h ⟨Y, mem_unitaryIsom3_of_mem_primeFormUnitary h Y.2⟩).symm
  have hmemD : ∀ (Y : primeFormUnitary h (idGram K 3)),
      primeFormConjHom h (idGram K 3) Y ∈ D.map φ.toMonoidHom →
        psuConj h ⟨Y, mem_unitaryIsom3_of_mem_primeFormUnitary h Y.2⟩ ∈ D := by
    intro Y hY
    obtain ⟨d, hd, hdY⟩ := hY
    have := hpre d hd Y hdY
    rw [← this]
    exact hd
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨Y, hY⟩ := hDl ⟨d, hd, rfl⟩
    exact ⟨⟨Y, mem_unitaryIsom3_of_mem_primeFormUnitary h Y.2⟩, (hpre d hd Y hY.symm).symm⟩
  · intro A' hcomm
    have hcA : ∀ d' ∈ D.map φ.toMonoidHom, primeFormConjHom h (idGram K 3)
        ⟨A', mem_primeFormUnitary_of_mem_unitaryIsom3 h A'.2⟩ * d' =
        d' * primeFormConjHom h (idGram K 3)
          ⟨A', mem_primeFormUnitary_of_mem_unitaryIsom3 h A'.2⟩ := by
      rintro _ ⟨d, hd, rfl⟩
      have := hcomm d hd
      have h2 := congrArg φ this
      rw [map_mul, map_mul, hφ, congr_psuConj] at h2
      exact h2
    have h3 := hmemD ⟨A', mem_primeFormUnitary_of_mem_unitaryIsom3 h A'.2⟩ (hM2 _ hcA)
    have e : (⟨A'.1, mem_unitaryIsom3_of_mem_primeFormUnitary h
        (mem_primeFormUnitary_of_mem_unitaryIsom3 h A'.2)⟩ : unitaryIsom3 h) = A' :=
      Subtype.ext rfl
    rw [e] at h3
    exact h3
  · have hA2 : A.1 ∈ unitaryIsom3 h := mem_unitaryIsom3_of_mem_primeFormUnitary h A.2
    have hB2 : B.1 ∈ unitaryIsom3 h := mem_unitaryIsom3_of_mem_primeFormUnitary h B.2
    refine ⟨⟨A.1, hA2⟩, ⟨B.1, hB2⟩, hmemD A hA, hmemD B hB, ?_⟩
    intro hAB'
    apply hAB
    apply Subtype.ext
    have h1 := congrArg (fun z : unitaryIsom3 h => (z : GL (Fin 3) K)) hAB'
    exact h1

end CFSG.HardMathSupport.Solomon.Coordinator
