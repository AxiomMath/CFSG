module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DPoly
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryPair CFSG.RankThree.PartOne.KCLinPlane
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCUnitaryGt
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Tau

theorem ringEquiv_eq_one_of_fix (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {τ : K ≃+* K}
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hτ : τ c = c) : τ = 1 := by
  have hroot : ∀ a : K, a ≠ 0 → a ≠ 1 → a ^ 2 + a + 1 = 0 := by
    intro a ha0 ha1
    have h3 := pow_three_eq_one h hq ha0
    have : (a - 1) * (a ^ 2 + a + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) ha1
    · exact h1
  have hcr := hroot c hc0 hc1
  ext a
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases ha1 : a = 1
  · simp [ha1]
  have har := hroot a ha0 ha1
  have hfac : (a - c) * (a + c + 1) = 0 := by linear_combination har - hcr
  change τ a = a
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rw [sub_eq_zero.mp h1]
    exact hτ
  · have e : a = -c - 1 := by linear_combination h1
    rw [e, map_sub, map_neg, hτ, map_one]

theorem tau_apply_eq_of_commute_pow (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)
    {M R : primeFormUnitary h (idGram K n)} {τ : K ≃+* K} {c : Kˣ}
    (hR : (R : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hcomm : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) R =
      primeFormConjHom h (idGram K n) R *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    τ (c : K) = c := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨d, hd⟩ := exists_scalar_of_commute_conj hn hne hcomm
  set α := primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ with hα
  have hR3 : ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_pow_eq_pow_val, hR, scalar_coe_eq_smul_one]
  have hD3 : ((GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, unit_pow_three_eq_one h hq d, map_one,
      Units.val_one]
  have hcm : Commute ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ((GeneralLinearGroup.scalar (Fin n) d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg Units.val (GeneralLinearGroup.scalar_commute d (R : GL (Fin n) K)).symm
  have e1 : idAct' h n hn hne α (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3) =
      ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [map_pow, hd, hcm.mul_pow, hR3, hD3]
  have e2 : idAct' h n hn hne α ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) =
      (τ (c : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hα, idAct'_psi_apply]
    have hmap : ((c : K) • (1 : Matrix (Fin n) (Fin n) K)).map τ =
        (τ (c : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  rw [hR3, e2, Matrix.mul_one] at e1
  exact smul_matrix_cancel (isUnit_one) e1

end Tau

section Block

theorem rtype_poly (hn : 4 ≤ n) (hq : ℓ ^ f = 2) {Q S : primeFormUnitary h (idGram K n)}
    (hQS : Q * S = S * Q) {c : Kˣ}
    (hQ : (Q : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ d : Kˣ, d ^ 3 ≠ c) (hS : S ^ 3 = 1)
    (hSnsc : ∀ d : Kˣ, (S : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) d)
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) {M : primeFormUnitary h (idGram K n)}
    (hg : primeFormConjHom h (idGram K n) M ∈ localDeltaIn 3 H E)
    (hQE : primeFormConjHom h (idGram K n) Q ∈ E)
    (hQ1 : primeFormConjHom h (idGram K n) Q ≠ 1) (hMQ : M * Q = Q * M) :
    ∃ r : K[X], ∀ v : Fin n → K, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (aeval (Matrix.toLin' ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r) v := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hn0 : 0 < n := by omega
  have hp0 : (3 : ℕ) ≠ 0 := by norm_num
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ 3).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp3).mp this).symm
  obtain ⟨ω, hω⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp3 hpq
  have hirr : Irreducible (X ^ 3 - C (c : K)) := by
    refine X_pow_sub_C_irreducible_of_prime hp3 fun b hb => ?_
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0] at hb
      exact c.ne_zero hb.symm
    exact hc (Units.mk0 b hb0) (Units.ext (by simpa using hb))
  have hSgl : (S : GL (Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hS
    simpa using this
  have hSs : (S : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hSgl, map_one]
  have hQSgl : (Q : GL (Fin n) K) * (S : GL (Fin n) K) = (S : GL (Fin n) K) * Q :=
    congrArg Subtype.val hQS
  have H0S := primaryData_of_pow_eq_scalar hp3 hpℓ hSs
  have H0Q := primaryData_of_pow_eq_scalar hp3 hpℓ hQ
  have hsqS := H0S.squarefree
  obtain ⟨a, ha, a', ha', haa'⟩ := exists_ne_mem_primaryFactors' hn0 hp0 hpK hω hSgl hSnsc
  have hh := mem_primaryFactors_X_pow_sub_C hn0 hp0 hirr hQ
  have hQone : ∀ b ∈ primaryFactors (Matrix.toLin' ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      b = X ^ 3 - C (c : K) := by
    intro b hb
    have hirr' := irreducible_of_mem_primaryFactors hb
    have hdvd : b ∣ X ^ 3 - C (c : K) := (mem_primaryFactors.mp hb).2.2.trans
      (minpoly.dvd K _ (aeval_X_pow_sub_C_eq_zero hQ))
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hb)
      (monic_X_pow_sub_C _ hp0) (associated_of_dvd_dvd hdvd (hirr'.dvd_symm hirr hdvd))
  have hselfQ : dualPoly h.bar (X ^ 3 - C (c : K)) = X ^ 3 - C (c : K) :=
    hQone _ (dualPoly_mem_primaryFactors H0Q hh)
  obtain ⟨-, -, -, -, -, hmultQ⟩ :=
    exists_mixing_mem_blockImage hn0 hp0 hQSgl hirr hQ hsqS ha ha' haa'
  have hgoodQ : IsGoodBlock h (toLinU h n Q) ⟨X ^ 3 - C (c : K), hh⟩ := by
    refine ⟨hmultQ, fun _ => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    rw [natDegree_X_pow_sub_C]
    have h8 : ℓ ^ (f * 3) = 8 := by rw [pow_mul, hq]; norm_num
    omega
  have hJpQ : 3 ∣ Nat.card ((gBlock h Q (X ^ 3 - C (c : K))).map
      (primeFormConjHom h (idGram K n))) := by
    refine dvd_card_map_of_mul_dvd hn3 hne ?_
    have hd := dvd_card_specialBlock_selfDual H0Q ⟨X ^ 3 - C (c : K), hh⟩ hselfQ
      (p := 3 * (ℓ ^ f + 1)) (j := 2) le_rfl hmultQ (by
        rw [natDegree_X_pow_sub_C]
        simpa using mul_dvd_pow_sq_sub_one (q := ℓ ^ f) hp3 hpq)
    have hcard : Nat.card (gBlock h Q (X ^ 3 - C (c : K))) =
        Nat.card (specialBlock (idForm h n) (toLinU h n Q) (X ^ 3 - C (c : K))) := by
      rw [← map_toLinU_gBlock]
      exact (Subgroup.card_map_of_injective toLinU_injective).symm
    rw [hcard]
    exact hd
  have hcommQ := commute_of_mem_localDeltaIn_gBlock hp3 hn3 hne hq2 H0Q
    ⟨X ^ 3 - C (c : K), hh⟩ hgoodQ hH hg hQE hQ1 hJpQ
  have hFQ : Group.IsPerfect (gBlock h Q (X ^ 3 - C (c : K))) :=
    (isQuasisimple_gBlock hq2 H0Q ⟨X ^ 3 - C (c : K), hh⟩ hgoodQ).1
  have hβ : ∀ Y ∈ gBlock h Q (X ^ 3 - C (c : K)),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, RingEquiv.refl K⟩ *
        primeFormConjHom h (idGram K n) Y = primeFormConjHom h (idGram K n) Y *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, RingEquiv.refl K⟩ := by
    intro Y hY
    rw [psi_refl_eq]
    exact hcommQ Y hY
  have hblock : ∀ Y ∈ gBlock h Q (X ^ 3 - C (c : K)), M * Y = Y * M := by
    intro Y hY
    have := matrix_comm_of_perfect hn3 hne hFQ M (RingEquiv.refl K) hβ Y hY
    rw [hmat_refl] at this
    exact Subtype.ext (Units.ext this)
  obtain ⟨c', hc'⟩ := exists_eScalar_of_commute_gBlock hq2 H0Q ⟨X ^ 3 - C (c : K), hh⟩ hgoodQ M
    hMQ hblock
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective c'
  refine ⟨r, fun v => ?_⟩
  have h1 := hc' ⟨v, mem_primaryComponent_X_pow_sub_C hQ v⟩
  rw [coe_mk_smul_primaryComponent] at h1
  rw [← toLinU_apply_eq]
  exact h1

end Block

section Main

theorem localDeltaIn_eq_bot_of_unitary_nonsplit_two (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {R S : primeFormUnitary h (idGram K n)} (hRS : R * S = S * R) {c : Kˣ}
    (hR : (R : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ d : Kˣ, d ^ 3 ≠ c) (hS : S ^ 3 = 1)
    (hS1 : primeFormConjHom h (idGram K n) S ≠ 1)
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hRE : primeFormConjHom h (idGram K n) R ∈ E) (hSE : primeFormConjHom h (idGram K n) S ∈ E) :
    localDeltaIn 3 H E = ⊥ := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hn0 : 0 < n := by omega
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hp0 : (3 : ℕ) ≠ 0 := by norm_num
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ 3).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp3).mp this).symm
  obtain ⟨ω, hω⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp3 hpq
  have hc1 : c ≠ 1 := fun h1 => hc 1 (by rw [one_pow, h1])
  have hRSgl : (R : GL (Fin n) K) * (S : GL (Fin n) K) = (S : GL (Fin n) K) * R :=
    congrArg Subtype.val hRS
  have hSgl : (S : GL (Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hS
    simpa using this
  have hSnsc : ∀ d : Kˣ, (S : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) d := by
    intro d hd
    apply hS1
    exact (primeFormConjHom_eq_one_iff_of_ne hn3 hne S).mpr
      ⟨d, (pow_succ_eq_one_iff_norm h d).mpr (norm_eq_one_of_unit h hq d), hd⟩
  have hρR1 : primeFormConjHom h (idGram K n) R ≠ 1 := by
    intro h1
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne R).mp h1
    apply hc d
    apply glScalar_injective hn0 (F := K)
    rw [map_pow, ← hd, hR]
  obtain ⟨R1, hR1def⟩ : ∃ R1 : primeFormUnitary h (idGram K n), R1 = R * S := ⟨_, rfl⟩
  have hR1gl : (R1 : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    have : (R1 : GL (Fin n) K) = (R : GL (Fin n) K) * (S : GL (Fin n) K) := by rw [hR1def]; rfl
    rw [this, (show Commute (R : GL (Fin n) K) (S : GL (Fin n) K) from hRSgl).mul_pow, hR, hSgl,
      mul_one]
  have hρR1' : primeFormConjHom h (idGram K n) R1 ≠ 1 := by
    intro h1
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne R1).mp h1
    apply hc1
    apply glScalar_injective hn0 (F := K)
    rw [← hR1gl, hd, ← map_pow, unit_pow_three_eq_one h hq d, map_one]
  have hR1E : primeFormConjHom h (idGram K n) R1 ∈ E := by
    rw [hR1def, map_mul]
    exact E.mul_mem hRE hSE
  have hR1S : R1 * S = S * R1 := by
    rw [hR1def, ← mul_assoc, ← hRS]
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn3 hne g
  have hτ : τ = RingEquiv.refl K := by
    have := tau_apply_eq_of_commute_pow hn3 hne hq hR (commute_of_mem_localDeltaIn hg hRE)
    exact ringEquiv_eq_one_of_fix h hq c.ne_zero (fun h1 => hc1 (Units.ext h1)) this
  subst hτ
  rw [psi_refl_eq] at hg
  have hcop : Nat.Coprime 3 (orderOf (primeFormConjHom h (idGram K n) M)) :=
    coprime_orderOf_of_mem_localDeltaIn hp3 hg hRE hρR1
  have hMR : M * R = R * M :=
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg hRE)
  have hMR1 : M * R1 = R1 * M :=
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg hR1E)
  obtain ⟨r0, hr0⟩ := rtype_poly hn hq hRS hR hc hS hSnsc hH hg hRE hρR1 hMR
  obtain ⟨r1, hr1⟩ := rtype_poly hn hq (Q := R1) (S := S) hR1S hR1gl hc hS hSnsc hH hg hR1E
    hρR1' hMR1
  have hSs : (S : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hSgl, map_one]
  have H0S := primaryData_of_pow_eq_scalar hp3 hpℓ hSs
  have hsqS := H0S.squarefree
  obtain ⟨a, ha, a', ha', haa'⟩ := exists_ne_mem_primaryFactors' hn0 hp0 hpK hω hSgl hSnsc
  obtain ⟨ν₁, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp0 hω hSgl ha
  obtain ⟨ν₂, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp0 hω hSgl ha'
  have hν : ν₁ ≠ ν₂ := fun e => haa' (by rw [e])
  obtain ⟨w₁, hw₁m, hw₁0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsqS ha)
  obtain ⟨w₂, hw₂m, hw₂0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsqS ha')
  have e₁ : Matrix.toLin' ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w₁ = ν₁ • w₁ :=
    mem_primaryComponent_X_sub_C.mp hw₁m
  have e₂ : Matrix.toLin' ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w₂ = ν₂ • w₂ :=
    mem_primaryComponent_X_sub_C.mp hw₂m
  have hν1p : ν₁ ^ 3 = 1 := eigenvalue_pow_eq_one hS hw₁0 e₁
  have hν2p : ν₂ ^ 3 = 1 := eigenvalue_pow_eq_one hS hw₂0 e₂
  have hν2 : ν₁ ^ 2 ≠ ν₂ ^ 2 := by
    intro e
    apply hν
    calc ν₁ = ν₁ * ν₁ ^ 3 := by rw [hν1p, mul_one]
      _ = (ν₁ ^ 2) ^ 2 := by ring
      _ = (ν₂ ^ 2) ^ 2 := by rw [e]
      _ = ν₂ * ν₂ ^ 3 := by ring
      _ = ν₂ := by rw [hν2p, mul_one]
  have hirr : Irreducible (X ^ 3 - C (c : K)) := by
    refine X_pow_sub_C_irreducible_of_prime hp3 fun b hb => ?_
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0] at hb
      exact c.ne_zero hb.symm
    exact hc (Units.mk0 b hb0) (Units.ext (by simpa using hb))
  have hmulT : Matrix.toLin' ((R1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.toLin' ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hR1def, Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl
  have hab : aeval (Matrix.toLin' ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r0 =
      aeval (Matrix.toLin' ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.toLin' ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r1 := by
    refine LinearMap.ext fun v => ?_
    rw [← hr0 v, hr1 v, hmulT]
  obtain ⟨b₀, hb⟩ := aeval_eq_const
    (Matrix.toLin' ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (Matrix.toLin' ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (commute_toLin'_of_mul_comm hRSgl) hirr (monic_X_pow_sub_C _ hp0) (natDegree_X_pow_sub_C)
    (aeval_X_pow_sub_C_eq_zero hR) (by rw [← hmulT]; exact aeval_X_pow_sub_C_eq_zero hR1gl)
    hν hν2 hw₁0 hw₂0 e₁ e₂ r0 r1 hab
  have hall : ∀ v : Fin n → K, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = b₀ • v := by
    intro v
    rw [hr1 v, hmulT, hb]
    simp
  exact psi_eq_one_of_scalar hn3 hne M b₀ hall

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
