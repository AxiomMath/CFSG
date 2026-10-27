module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitary
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Main27
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Core
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag

theorem natChar_ne_three_A {p : ℕ} (hp3 : p ≠ 3) (r : ℕ) (q' : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q').Valid) (hidx : IsChevIndexOfChar p (.A r q')) :
    q'.p ≠ 3 := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · have hr1 : r = 1 := by
      have := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      omega
    subst hr1
    have hdup := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
    simp only [IsChevIndexOfChar] at hidx
    rcases hidx with h | ⟨h2, h9⟩ | ⟨h3, h8⟩
    · rw [h]; exact hp3
    · exfalso
      apply hdup
      rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      left
      exact ⟨rfl, Or.inr (Or.inr h9)⟩
    · exact absurd h3 hp3
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
    simp only [IsChevIndexOfChar, lieIndexChar] at hidx
    rw [hidx]; exact hp3

theorem natChar_ne_three_twistedA {p : ℕ} (hp3 : p ≠ 3) (r : ℕ) (q' : TauCeti.PrimePower)
    (hidx : IsChevIndexOfChar p (.twistedA r q')) : q'.p ≠ 3 ∨ (r = 2 ∧ q'.card = 3) := by
  by_cases hr : r = 2
  · subst hr
    simp only [IsChevIndexOfChar] at hidx
    rcases hidx with h | ⟨h2, h3⟩
    · left; rw [h]; exact hp3
    · right; exact ⟨rfl, h3⟩
  · left
    have : IsChevIndexOfChar p (.twistedA r q') ↔ q'.p = p := by
      rcases r with _ | _ | _ | r
      all_goals first | exact absurd rfl hr | simp [IsChevIndexOfChar, lieIndexChar]
    rw [this.mp hidx]; exact hp3

variable {S : Type} [Group S] [Finite S] {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S}
  {q : ℕ}

theorem linear_case (hZ : Subgroup.center S = ⊥) {p : ℕ} (hp3 : p ≠ 3) (r : ℕ)
    (q' : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q').Valid)
    (hidx : IsChevIndexOfChar p (.A r q'))
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q', hv⟩).Group))
    (c : I1433SCfg Q x J q) : False := by
  have hq3 := natChar_ne_three_A hp3 r q' hv hidx
  have : Fact q'.p.Prime := ⟨q'.prime_p⟩
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q'.p q'.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q' hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have h3 : (3 : GaloisField q'.p q'.exponent) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : GaloisField q'.p q'.exponent) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (GaloisField q'.p q'.exponent) q'.p] at h0'
    exact hq3 ((Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_three).1 h0')
  have hZ' : Subgroup.center (LinearFlag.projectiveSL (r + 1) (GaloisField q'.p q'.exponent)) =
      ⊥ := by
    rw [← Subgroup.map_center_eq e', hZ, Subgroup.map_bot]
  obtain ⟨a, b, J', hcore⟩ := c.coreCfg_of_mulEquiv e'
  exact linear_core (by omega) h3 hZ' hcore

theorem six_o_four_eight_lt_card_of_sl3EpsOfChar {p : ℕ} {Y : Type} [Group Y]
    (h : SL3EpsOfChar p Y) : 6048 < Nat.card Y := by
  rcases h with ⟨K, _, _, hK, h1, ⟨e⟩⟩ | ⟨K, _, _, q, hK, hcard, h2, hq2, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three]
    set k := Nat.card K with hk
    have hk2 : 2 ≤ k := Finite.one_lt_card
    have hk4 : 4 ≤ k := by omega
    have e1 : 16 ≤ k ^ 2 := by nlinarith
    have e2 : 64 ≤ k ^ 3 := by nlinarith
    calc 6048 < 64 * (15 * 63) := by norm_num
      _ ≤ k ^ 3 * ((k ^ 2 - 1) * (k ^ 3 - 1)) :=
        Nat.mul_le_mul e2 (Nat.mul_le_mul (by omega) (by omega))
  · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hcard]
    have hq5 : 5 ≤ q := by omega
    have e1 : 25 ≤ q ^ 2 := by nlinarith
    have e2 : 125 ≤ q ^ 3 := by nlinarith
    calc 6048 < 125 * 24 * 126 := by norm_num
      _ ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul e2 (by omega)) (by omega)

theorem unitary_three_three_false (r : ℕ) (q' : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q').Valid) (hr : r = 2) (hq : q'.card = 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q', hv⟩).Group))
    (c : I1433SCfg Q x J q) : False := by
  subst hr
  obtain ⟨e⟩ := he
  have : Fact q'.p.Prime := ⟨q'.prime_p⟩
  have hS : Nat.card S = 6048 := by
    obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q' hv e
    have hq3 : q'.p ^ q'.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq
    have hp3 : (q'.p ^ q'.exponent).Prime := by rw [hq3]; exact Nat.prime_three
    have h1 := CFSG.Open.StatedAPI.card_statedProj_statedSU_three_of_prime hp3 hK
    rw [Nat.card_congr eT.toEquiv, h1, hq3]
    norm_num
  have hJbar := isQuasisimple_quotient_of_glaPComponent c.comp
  have hSL3 : IsSL3Eps (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    refine ⟨?_, c.sl3.2⟩
    rcases c.sl3.1 with ⟨F, hF, hfin, -, ⟨e⟩⟩ | ⟨F, hF, hfin, hcard, ⟨e⟩⟩
    · exact Or.inl ⟨F, hF, hfin, ⟨e⟩⟩
    · exact Or.inr ⟨F, hF, hfin, q, hcard, ⟨e⟩⟩
  obtain ⟨p, hp, hp3, hpc⟩ := i253_exists_char (i253_any_of_isSL3Eps hJbar hSL3)
  have h1 := six_o_four_eight_lt_card_of_sl3EpsOfChar hpc
  have h2 : Nat.card (↥J ⧸ GLAPPrimeCore 3 ↥J) ≤ Nat.card J :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := GLAPPrimeCore 3 ↥J))
  have h3 : Nat.card J ≤ Nat.card S := Subgroup.card_le_card_group J
  omega

theorem unitary_case (hZ : Subgroup.center S = ⊥) {p : ℕ} (hp3 : p ≠ 3) (r : ℕ)
    (q' : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA r q').Valid)
    (hidx : IsChevIndexOfChar p (.twistedA r q'))
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q', hv⟩).Group))
    (c : I1433SCfg Q x J q) : False := by
  rcases natChar_ne_three_twistedA hp3 r q' hidx with hq3 | ⟨hr, hq⟩
  · have : Fact q'.p.Prime := ⟨q'.prime_p⟩
    obtain ⟨e⟩ := he
    obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q' hv e
    have h : UnitaryFieldData q'.p q'.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
    let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    have hq' : ¬(r + 1 = 3 ∧ q'.p ^ q'.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
    have hZ' : Subgroup.center (primeFormP h (idGram K (r + 1))) = ⊥ := by
      rw [← Subgroup.map_center_eq e', hZ, Subgroup.map_bot]
    obtain ⟨a, b, J', hcore⟩ := c.coreCfg_of_mulEquiv e'
    exact unitary_core h hn3 hq' hq3 hZ' hcore
  · exact unitary_three_three_false r q' hv hr hq he c

theorem nonD4LieContraS_linearUnitary : NonD4LieContraS .linearUnitary := by
  intro S _ _ hs hna p hp hp3 idx hF hidx he hD Q x J q c
  haveI := hs
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q' => exact linear_case hZ hp3 r q' hv hidx he c
  | twistedA r q' => exact unitary_case hZ hp3 r q' hv hidx he c
  | _ => simp [lieFamily] at hF

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
