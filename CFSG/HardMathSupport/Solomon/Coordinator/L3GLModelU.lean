module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUMain
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLMatrix
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.Coordinator CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical

variable {ℓ f : ℕ} {K : Type} [Field K]

local notation "S" => Matrix.GeneralLinearGroup.scalar (Fin 3)

theorem exists_heisenberg_pair_of_localDeltaIn_ne_bot_U (h : UnitaryFieldData ℓ f K)
    (hq : 2 < ℓ ^ f) (hq8 : ℓ ^ f ≠ 8) (hpq : 3 ∣ ℓ ^ f + 1)
    {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hH : innerAut (primeFormP h (idGram K 3)) ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) :
    ∃ (A B : primeFormUnitary h (idGram K 3)) (c : Kˣ),
      primeFormConjHom h (idGram K 3) A ∈ D ∧ primeFormConjHom h (idGram K 3) B ∈ D ∧ c ≠ 1 ∧
      (A : GL (Fin 3) K) * B = B * A * S c := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn : 3 ≤ 3 := le_rfl
  have hq2 : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  have := h.finite
  have hℓ := h.prime
  have hq3 : 3 < ℓ ^ f := by
    by_contra hle
    have h3 : ℓ ^ f = 3 := by omega
    rw [h3] at hpq
    omega
  have hl3 : ℓ ≠ 3 := by
    intro hl3
    subst hl3
    apply hne
    have hpg : ¬ (3 : ℕ) ∣ Nat.gcd 3 (3 ^ f + 1) := by
      intro hd
      have h1 : 3 ∣ 3 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
      have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
      omega
    obtain ⟨x, hxD, hx1, hxl⟩ := exists_ne_one_mem_primeFormD h hq2 hD hcard
    have hxo : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
    have hxi : x ∈ innerAut (primeFormP h (idGram K 3)) :=
      mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin 3) K) hp hpg hxl (hD.2 x hxD)
    have h0 := gLAPPrimeCoreOf_eq_bot_primeFormP_char h le_rfl (by omega) hp2 hxi hxo hH
    refine eq_bot_iff.2 fun y hy => ?_
    have := le_core_of_mem_localDeltaIn hy hxD hx1
    rw [h0] at this
    exact this
  have hDl : D ≤ primeFormD h (idGram K 3) := by
    by_contra hDl
    by_cases hq0 : ℓ ^ (f / 3) = 2
    · have hℓ2 : ℓ = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0).1
      subst hℓ2
      have hf1 : f / 3 = 1 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0).2
      have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
      obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
      have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
      have hσ1 : primeFormFieldFactor h hC hn hq2 x ≠ 1 := fun h1 => hxl (by
        rw [← ker_primeFormFieldFactor h hC hn hq2]
        exact h1)
      have hσ : orderOf (primeFormFieldFactor h hC hn hq2 x) = 3 :=
        orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
      have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
      have hf3 : f = 3 := by omega
      subst hf3
      exact hq8 (by norm_num)
    · exact hne (localDeltaIn_eq_bot_of_not_le_primeFormD_three h hq2 (by omega) hD hDl hH)
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
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq2 _).mp hcom
  have hAB : (A : GL (Fin 3) K) * B = B * A * S c := by
    have h1 : (A : GL (Fin 3) K) * B * (A : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K)⁻¹ = S c := by
      simpa using hc
    calc (A : GL (Fin 3) K) * B = S c * (B * A) := by rw [← h1]; group
      _ = B * A * S c := Matrix.GeneralLinearGroup.scalar_commute c _
  refine ⟨A, B, c, hAE, hBE, ?_, hAB⟩
  rintro rfl
  have hABc : A * B = B * A := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
  have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hq2 hq3 hp hp2 hpq hABc hAp hBp hA1 hBA hH
  exact hne (le_bot_iff.1 ((localDeltaIn_antitone H hED').trans hbot.le))

theorem l3gl_cube_of_localDeltaIn_ne_bot_U (h : UnitaryFieldData ℓ f K) (hq : 2 < ℓ ^ f)
    (hq8 : ℓ ^ f ≠ 8) (hpq : 3 ∣ ℓ ^ f + 1)
    {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hH : innerAut (primeFormP h (idGram K 3)) ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) (s : gramSU h (idGram K 3))
    (hs : ∀ d ∈ D, d * MulAut.conj (s : primeFormP h (idGram K 3)) =
      MulAut.conj (s : primeFormP h (idGram K 3)) * d) :
    (s : GL (Fin 3) K) ^ 3 = 1 := by
  have hn : 3 ≤ 3 := le_rfl
  have hq2 : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  obtain ⟨A, B, c, hAE, hBE, hc1, hAB⟩ :=
    exists_heisenberg_pair_of_localDeltaIn_ne_bot_U h hq hq8 hpq hD hcard hH hne
  let Y : primeFormUnitary h (idGram K 3) := ⟨(s : GL (Fin 3) K), s.2.1⟩
  have hconj : primeFormConjHom h (idGram K 3) Y =
      MulAut.conj (s : primeFormP h (idGram K 3)) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => exact (primeFormConjHom_mk h _ Y g).trans rfl
  have key : ∀ X : primeFormUnitary h (idGram K 3), primeFormConjHom h (idGram K 3) X ∈ D →
      ∃ d : Kˣ, (s : GL (Fin 3) K) * X * (s : GL (Fin 3) K)⁻¹ = X * S d := by
    intro X hX
    have hcomm : primeFormConjHom h (idGram K 3) Y * primeFormConjHom h (idGram K 3) X =
        primeFormConjHom h (idGram K 3) X * primeFormConjHom h (idGram K 3) Y := by
      have := hs _ hX
      rw [hconj]
      exact this.symm
    have h1 : primeFormConjHom h (idGram K 3) (Y * X * Y⁻¹ * X⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hq2 _).mp h1
    refine ⟨d, ?_⟩
    have h2 : (s : GL (Fin 3) K) * X * (s : GL (Fin 3) K)⁻¹ * (X : GL (Fin 3) K)⁻¹ = S d := by
      simpa [Y] using hd
    calc (s : GL (Fin 3) K) * X * (s : GL (Fin 3) K)⁻¹
        = S d * X := by rw [← h2]; group
      _ = X * S d := Matrix.GeneralLinearGroup.scalar_commute d _
  obtain ⟨dA, hdA⟩ := key A hAE
  obtain ⟨dB, hdB⟩ := key B hBE
  exact l3gl_heis_cube hc1 hAB hdA hdB s.2.2

end CFSG.HardMathSupport.Solomon.Coordinator
