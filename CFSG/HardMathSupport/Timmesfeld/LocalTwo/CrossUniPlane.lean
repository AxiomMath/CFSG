module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

@[expose] def UniHeisPlane (h : UnitaryFieldData ℓ f K) (n p : ℕ) : Prop :=
  ∀ (A B : primeFormUnitary h (idGram K n)) (c : Kˣ), c ≠ 1 → c ^ p = 1 →
    (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c →
    primeFormConjHom h (idGram K n) A ^ p = 1 → primeFormConjHom h (idGram K n) B ^ p = 1 →
    primeFormConjHom h (idGram K n) A ≠ 1 →
    primeFormConjHom h (idGram K n) B ∉ Subgroup.zpowers (primeFormConjHom h (idGram K n) A) →
    ∀ H : Subgroup (MulAut (primeFormP h (idGram K n))),
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ≤ H →
      Subgroup.closure {primeFormConjHom h (idGram K n) A, primeFormConjHom h (idGram K n) B} ≤
        Subgroup.normalizer (H : Set (MulAut (primeFormP h (idGram K n)))) →
      localDeltaIn p H (Subgroup.closure {primeFormConjHom h (idGram K n) A,
        primeFormConjHom h (idGram K n) B}) = ⊥

@[expose] def UniHeisenbergPlaneBalance : Prop :=
  ∀ (ℓ f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ≤ n →
    ¬(n = 3 ∧ ℓ ^ f = 2) → ∀ p : ℕ, p.Prime → 5 < p → p ≠ ℓ → p ∣ ℓ ^ f + 1 → p ∣ n →
      n ≠ p → UniHeisPlane h n p

section Lifts

variable {A B : primeFormUnitary h (idGram K n)}

theorem scalar_pow_conj {m : ℕ} (a : GL (Fin m) K) (b : GL (Fin m) K) (c : Kˣ)
    (hab : a * b = b * a * GeneralLinearGroup.scalar (Fin m) c) (k : ℕ) :
    a ^ k * b = b * a ^ k * GeneralLinearGroup.scalar (Fin m) (c ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a ^ (k + 1) * b = a * (a ^ k * b) := by rw [pow_succ', mul_assoc]
      _ = a * (b * a ^ k * GeneralLinearGroup.scalar (Fin m) (c ^ k)) := by rw [ih]
      _ = (a * b) * a ^ k * GeneralLinearGroup.scalar (Fin m) (c ^ k) := by simp only [mul_assoc]
      _ = b * a * GeneralLinearGroup.scalar (Fin m) c * a ^ k *
            GeneralLinearGroup.scalar (Fin m) (c ^ k) := by rw [hab]
      _ = b * a * a ^ k * GeneralLinearGroup.scalar (Fin m) c *
            GeneralLinearGroup.scalar (Fin m) (c ^ k) := by
          rw [mul_assoc (b * a), GeneralLinearGroup.scalar_commute c (a ^ k), ← mul_assoc]
      _ = b * a ^ (k + 1) * GeneralLinearGroup.scalar (Fin m) (c ^ (k + 1)) := by
          rw [mul_assoc (b * a * a ^ k), ← map_mul, ← pow_succ' c k, pow_succ' a k,
            mul_assoc b a (a ^ k)]

theorem det_scalar_comm_eq {m : ℕ} (a b : GL (Fin m) K) (c : Kˣ)
    (hab : a * b = b * a * GeneralLinearGroup.scalar (Fin m) c) : c ^ m = 1 := by
  have h1 := congrArg GeneralLinearGroup.det hab
  rw [map_mul, map_mul, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
  rw [mul_comm (GeneralLinearGroup.det b)] at h1
  exact mul_eq_left.mp h1.symm

theorem exists_plane_lifts_unitary [Finite K] (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDl : D ≤ primeFormD h (idGram K n)) :
    ∃ (A B : primeFormUnitary h (idGram K n)) (c : Kˣ),
      primeFormConjHom h (idGram K n) A ∈ D ∧ primeFormConjHom h (idGram K n) B ∈ D ∧
      primeFormConjHom h (idGram K n) A ≠ 1 ∧
      primeFormConjHom h (idGram K n) B ∉ Subgroup.zpowers (primeFormConjHom h (idGram K n) A) ∧
      (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c ∧
      c ^ p = 1 ∧ c ^ n = 1 ∧ c ^ (ℓ ^ f + 1) = 1 := by
  classical
  obtain ⟨A, B, hAD, hBD, hA1, hBA⟩ := exists_lift_pair_of_plane hp hD hcard hDl
  have hρ : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) A :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hAD⟩ ⟨_, hBD⟩)
  have hcom : primeFormConjHom h (idGram K n) (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ]
    group
  obtain ⟨c, hcq, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp hcom
  have hAB : (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c := by
    have h1 : (A : GL (Fin n) K) * B * (A : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) c := by simpa using hc
    calc (A : GL (Fin n) K) * B = GeneralLinearGroup.scalar (Fin n) c * (B * A) := by
          rw [← h1]; group
      _ = B * A * GeneralLinearGroup.scalar (Fin n) c :=
          GeneralLinearGroup.scalar_commute c _
  have hAp : primeFormConjHom h (idGram K n) (A ^ p) = 1 := by
    rw [map_pow]; exact hD.2 _ hAD
  obtain ⟨a, -, ha⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp hAp
  have ha' : (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a := by simpa using ha
  refine ⟨A, B, c, hAD, hBD, hA1, hBA, hAB, ?_, det_scalar_comm_eq _ _ c hAB, hcq⟩
  have h1 := scalar_pow_conj (A : GL (Fin n) K) B c hAB p
  rw [ha', GeneralLinearGroup.scalar_commute a (B : GL (Fin n) K)] at h1
  have h2 : GeneralLinearGroup.scalar (Fin n) (c ^ p) = (1 : GL (Fin n) K) :=
    mul_eq_left.mp h1.symm
  exact glScalar_injective (by omega) (h2.trans (map_one _).symm)

theorem localDeltaIn_eq_bot_of_le_primeFormD_plane (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp5 : 5 < p) (hpℓ : p ≠ ℓ)
    (hHeis : p ∣ ℓ ^ f + 1 → p ∣ n → UniHeisPlane h n p)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDl : D ≤ primeFormD h (idGram K n))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hDH : D ≤ Subgroup.normalizer (H : Set (MulAut (primeFormP h (idGram K n))))) :
    localDeltaIn p H D = ⊥ := by
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  by_cases hpg : p ∣ Nat.gcd n (ℓ ^ f + 1)
  · have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
    have hq3 : 3 < ℓ ^ f := by
      have := Nat.le_of_dvd (by omega) hpq
      omega
    obtain ⟨A, B, c, hAD, hBD, hA1, hBA, hAB, hcp, -, -⟩ :=
      exists_plane_lifts_unitary hn hne hp hD hcard hDl
    have hED : Subgroup.closure {primeFormConjHom h (idGram K n) A,
        primeFormConjHom h (idGram K n) B} ≤ D := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hAD
      · exact hBD
    have hAp : primeFormConjHom h (idGram K n) A ^ p = 1 := hD.2 _ hAD
    have hBp : primeFormConjHom h (idGram K n) B ^ p = 1 := hD.2 _ hBD
    by_cases hc1 : c = 1
    · subst hc1
      have hABc : A * B = B * A := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
      have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hABc hAp hBp hA1
        hBA hH
      exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)
    · have hbot := hHeis hpq hpn A B c hc1 hcp hAB hAp hBp hA1 hBA H hH (hED.trans hDH)
      exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)
  · have hDin : D ≤ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range := fun d hd =>
      mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin n) K) hp hpg (hDl hd) (hD.2 d hd)
    have hEel : CFSG.IsElementaryAbelian p D :=
      { toIsMulCommutative := hD.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hD.2 x x.2) }
    exact localDeltaIn_eq_bot_primeFormP h hn hne hp hp2 hpℓ hpg
      (fun ⟨h3, h4⟩ => by omega) D hDin hEel hcard hH

end Lifts

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
