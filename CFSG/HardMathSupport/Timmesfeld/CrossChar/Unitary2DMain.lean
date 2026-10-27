module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DHeis
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DAbel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Family

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Delta

variable {h : UnitaryFieldData ℓ f K}

theorem exists_pow_eq_of_ne_one (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {c : Kˣ}
    (hc1 : c ≠ 1) (d : Kˣ) : ∃ m : ℕ, c ^ m = d := by
  have := h.finite
  have hoc : orderOf c = 3 := orderOf_eq_prime (unit_pow_three_eq_one h hq c) hc1
  have htop : Subgroup.zpowers c = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, hoc, card_units_eq_three h hq])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top d)
  refine ⟨(k % 3).toNat, ?_⟩
  rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  have := zpow_mod_orderOf c k
  rwa [hoc, Nat.cast_ofNat] at this

theorem localDeltaIn_eq_bot_two_pgu (hq : ℓ ^ f = 2) (hn : 6 ≤ n)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27) (hDl : D ≤ primeFormD h (idGram K n))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hn0 : 0 < n := by omega
  have hscal : ∀ Y : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) Y ∈ D →
      ∃ c : Kˣ, (Y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    intro Y hY
    have h1 : primeFormConjHom h (idGram K n) (Y ^ 3) = 1 := by rw [map_pow, hD.2 _ hY]
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).1 h1
    exact ⟨c, by rw [← hc, Subgroup.coe_pow]⟩
  by_cases hN : ∃ A : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ D ∧
      A ^ 3 ≠ 1
  ·
    obtain ⟨A, hA, hA3⟩ := hN
    obtain ⟨c, hc⟩ := hscal A hA
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hA3
      apply Subtype.ext
      rw [Subgroup.coe_pow, hc, map_one, Subgroup.coe_one]
    have hcube : ∀ d : Kˣ, d ^ 3 ≠ c := fun d hd => hc1 (by rw [← hd, unit_pow_three_eq_one h hq])
    obtain ⟨B, hB, hBA, hAB⟩ := exists_commuting_lift hn3 hne hq hD hcard hDl A hA
    obtain ⟨d, hd⟩ := hscal B hB
    obtain ⟨m, hm⟩ := exists_pow_eq_of_ne_one h hq hc1 d⁻¹
    set S : primeFormUnitary h (idGram K n) := B * A ^ m with hS
    have hAS : A * S = S * A := by
      rw [hS, ← mul_assoc, hAB, mul_assoc, mul_assoc, (Commute.self_pow A m).eq]
    have hS3 : S ^ 3 = 1 := by
      apply Subtype.ext
      have hBA' : Commute (B : GL (Fin n) K) ((A : GL (Fin n) K) ^ m) :=
        (Commute.pow_right (congrArg Subtype.val hAB).symm m)
      rw [Subgroup.coe_pow, hS, Subgroup.coe_mul, Subgroup.coe_pow, hBA'.mul_pow, hd, ← pow_mul,
        mul_comm m 3, pow_mul, hc, ← map_pow, ← map_mul, hm, mul_inv_cancel, map_one,
        Subgroup.coe_one]
    have hSD : primeFormConjHom h (idGram K n) S ∈ D := by
      rw [hS, map_mul, map_pow]
      exact D.mul_mem hB (D.pow_mem hA m)
    have hS1 : primeFormConjHom h (idGram K n) S ≠ 1 := by
      intro h1
      apply hBA
      rw [hS, map_mul, map_pow, mul_eq_one_iff_eq_inv] at h1
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m)
    exact localDeltaIn_eq_bot_of_unitary_nonsplit_two (by omega) hq hAS hc hcube hS3 hS1 hH hA hSD
  push Not at hN
  by_cases hC : ∃ A B : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ D ∧
      primeFormConjHom h (idGram K n) B ∈ D ∧ A * B ≠ B * A
  · obtain ⟨A, B, hA, hB, hAB⟩ := hC
    exact localDeltaIn_eq_bot_of_heis (by omega) hq hD hcard hDl hN hA hB hAB hH
  push Not at hC
  exact localDeltaIn_eq_bot_of_abel hn hq hD hcard hDl hN hC hH

end Delta

section Family

theorem le_primeFormD_three_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hD : IsElemAbelian 3 D) : D ≤ primeFormD h (idGram K n) := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  subst hℓ
  have : CharP K 2 := h.charP
  have hK : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul', hq]
    norm_num
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  intro x hx
  rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker]
  exact ringEquiv_eq_one_of_pow_three hK (by rw [← map_pow, hD.2 x hx, map_one])

theorem isLocallyBalancedAbs_primeFormP_two_pgu (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn : 6 ≤ n) : IsLocallyBalancedAbs 3 3 (primeFormP h (idGram K n)) := by
  intro D hD hcard H hH _
  exact localDeltaIn_eq_bot_two_pgu hq hn hD (by rw [hcard]; norm_num)
    (le_primeFormD_three_two h hq (by omega) (fun h' => by omega) hD) hH

theorem crossCharFamAt_twistedA_threeTwo_diag :
    CrossCharFamAt .twistedA regimeTwistedAThreeTwoDiag := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, rfl, h2, h3r⟩
  change d = _ at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq2 : q.p ^ q.exponent = 2 := hcard ▸ h2
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  have h6 : 6 ≤ r + 1 := by
    rcases h3r with h3 | h3
    · obtain ⟨k, hk⟩ := h3
      have : r + 1 ≠ 3 := fun h' => hq' ⟨h', hq2⟩
      omega
    · exact absurd ⟨by omega, hq2⟩ hq'
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : Cat ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_primeFormP_two_pgu h hq2 h6)

theorem crossCharFamAt_twistedA_threeTwo : CrossCharFamAt .twistedA regimeTwistedAThreeTwo :=
  crossCharFamAt_twistedA_threeTwo_of_rest
    (crossCharFamAt_twistedA_threeTwo_of_rest_diag crossCharFamAt_twistedA_threeTwo_diag)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
