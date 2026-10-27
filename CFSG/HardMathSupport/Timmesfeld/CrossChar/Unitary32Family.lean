module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem le_innerAut_primeFormP_three_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (h3n : ¬ 3 ∣ n)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian 3 D) :
    D ≤ innerAut (primeFormP h (idGram K n)) := by
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
  have hxD : x ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker]
    exact ringEquiv_eq_one_of_pow_three hK (by rw [← map_pow, hD.2 x hx, map_one])
  have hpg : ¬ 3 ∣ Nat.gcd n (2 ^ f + 1) := fun hd => h3n (hd.trans (Nat.gcd_dvd_left _ _))
  exact mem_inner_of_pow_eq_one_unitary h 1 Nat.prime_three hpg hxD (hD.2 x hx)

theorem isLocallyBalancedAbs_primeFormP_three_two (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f = 2) (hn : 7 ≤ n) (h3n : ¬ 3 ∣ n) :
    IsLocallyBalancedAbs 3 3 (primeFormP h (idGram K n)) := by
  intro D hD hcard H hH _
  exact localDeltaIn_eq_bot_three_two h hq hn h3n D hD (by rw [hcard]; norm_num)
    (le_innerAut_primeFormP_three_two h hq (by omega) (fun h' => by omega) h3n hD) hH

@[expose] def regimeTwistedAThreeTwoBig (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p = 3 ∧ q.card = 2 ∧
    ¬ 3 ∣ r + 1 ∧ 7 ≤ r + 1

theorem crossCharFamAt_twistedA_threeTwo_big :
    CrossCharFamAt .twistedA regimeTwistedAThreeTwoBig := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, rfl, h2, h3n, h7⟩
  change d = _ at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq2 : q.p ^ q.exponent = 2 := hcard ▸ h2
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : Cat ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_primeFormP_three_two h hq2 h7 h3n)

@[expose] def regimeTwistedAThreeTwoRest (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p = 3 ∧ q.card = 2 ∧
    (3 ∣ r + 1 ∨ r + 1 ≤ 6)

theorem crossCharFamAt_twistedA_threeTwo_of_rest
    (hrest : CrossCharFamAt .twistedA regimeTwistedAThreeTwoRest) :
    CrossCharFamAt .twistedA regimeTwistedAThreeTwo := by
  intro idx hk p hp hp2 hc ⟨r, q, hd, h3, h2⟩
  by_cases hbig : ¬ 3 ∣ r + 1 ∧ 7 ≤ r + 1
  · exact crossCharFamAt_twistedA_threeTwo_big idx hk p hp hp2 hc
      ⟨r, q, hd, h3, h2, hbig.1, hbig.2⟩
  · refine hrest idx hk p hp hp2 hc ⟨r, q, hd, h3, h2, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hbig ⟨hcon.1, by omega⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
