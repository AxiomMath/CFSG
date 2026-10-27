module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem primeFormConj_eq_one_of_pgu_plane (h : UnitaryFieldData ℓ f K) (hq3 : 3 < ℓ ^ f)
    (hpq : 3 ∣ ℓ ^ f + 1) {D : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2) (hDl : D ≤ primeFormD h (idGram K 3))
    {H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) (Y : primeFormUnitary h (idGram K 3))
    (hY : primeFormConjHom h (idGram K 3) Y ∈ localDeltaIn 3 H D) :
    primeFormConjHom h (idGram K 3) Y = 1 := by
  classical
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have := h.finite
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
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp hcom
  have hAB : (A : GL (Fin 3) K) * B = B * A * GeneralLinearGroup.scalar (Fin 3) c := by
    have h1 : (A : GL (Fin 3) K) * B * (A : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by simpa using hc
    calc (A : GL (Fin 3) K) * B = GeneralLinearGroup.scalar (Fin 3) c * (B * A) := by
          rw [← h1]; group
      _ = B * A * GeneralLinearGroup.scalar (Fin 3) c :=
          GeneralLinearGroup.scalar_commute c _
  by_cases hc1 : c = 1
  · subst hc1
    have hABc : A * B = B * A := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
    have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hq hq3 hp hp2 hpq hABc hAp hBp hA1 hBA
      hH
    have h0 : localDeltaIn 3 H D = ⊥ :=
      le_bot_iff.1 ((localDeltaIn_antitone H hED').trans hbot.le)
    rw [h0] at hY
    exact Subgroup.mem_bot.1 hY
  · obtain ⟨a, -, ha⟩ : ∃ a : Kˣ, h.norm (a : K) = 1 ∧
        (A : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) a := by
      have h1 : primeFormConjHom h (idGram K 3) (A ^ 3) = 1 := by rw [map_pow]; exact hAp
      obtain ⟨a, ha, hA'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp h1
      exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hA'⟩
    obtain ⟨b, -, hb⟩ : ∃ b : Kˣ, h.norm (b : K) = 1 ∧
        (B : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) b := by
      have h1 : primeFormConjHom h (idGram K 3) (B ^ 3) = 1 := by rw [map_pow]; exact hBp
      obtain ⟨b, hb, hB'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp h1
      exact ⟨b, (pow_succ_eq_one_iff_norm h b).mp hb, by simpa using hB'⟩
    have hc3 := cube_eq_one_of_commutator ha hAB
    have hgA := commute_of_mem_localDeltaIn hY hAE
    have hgB := commute_of_mem_localDeltaIn hY hBE
    have hcop := coprime_orderOf_of_mem_localDeltaIn hp hY hAE hA1
    have hnorm : ∀ {X : primeFormUnitary h (idGram K 3)},
        primeFormConjHom h (idGram K 3) Y * primeFormConjHom h (idGram K 3) X =
          primeFormConjHom h (idGram K 3) X * primeFormConjHom h (idGram K 3) Y →
        ∃ d : Kˣ, (Y : GL (Fin 3) K) * X * (Y : GL (Fin 3) K)⁻¹ =
          X * GeneralLinearGroup.scalar (Fin 3) d := by
      intro X hX
      have h1 : primeFormConjHom h (idGram K 3) (Y * X * Y⁻¹ * X⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hX]
        group
      obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq _).mp h1
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
      (primeFormConjHom_eq_one_iff_of_ne hn hq Z).mpr
        ⟨m, (pow_succ_eq_one_iff_norm h m).mpr hZn, hZm⟩
    have hρM : primeFormConjHom h (idGram K 3) Y =
        primeFormConjHom h (idGram K 3) A ^ i * primeFormConjHom h (idGram K 3) B ^ j := by
      have hMX : Y = (A ^ i * B ^ j) * Z := by rw [hZ, mul_inv_cancel_left]
      rw [hMX, map_mul, hρZ, mul_one, map_mul, map_pow, map_pow]
    have hmem : primeFormConjHom h (idGram K 3) Y ∈ Subgroup.closure
        {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} := by
      rw [hρM]
      have hAm : primeFormConjHom h (idGram K 3) A ∈ Subgroup.closure
          {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hBm : primeFormConjHom h (idGram K 3) B ∈ Subgroup.closure
          {primeFormConjHom h (idGram K 3) A, primeFormConjHom h (idGram K 3) B} :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      exact mul_mem (pow_mem hAm i) (pow_mem hBm j)
    have hg3 := (closure_pair_comm_and_pow_eq_one hρ hAp hBp).2 _ hmem
    have hord : orderOf (primeFormConjHom h (idGram K 3) Y) ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm hord)

end CFSG.HardMathSupport.Solomon.Coordinator
