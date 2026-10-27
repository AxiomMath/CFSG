module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsAssembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsUni

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

section Transport

variable {p : ℕ}

theorem data_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (hU : UpperP p S')
    (hL : Nonempty (LowerData p S')) : UpperP p S ∧ Nonempty (LowerData p S) := by
  refine ⟨?_, ?_⟩
  · refine UpperP.of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective ?_ hU
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · obtain ⟨D⟩ := hL
    refine ⟨{ X := fun k => e.symm (D.X k)
              Sw := fun k => e.symm (D.Sw k)
              T := e.symm D.T
              comm := fun i j => (D.comm i j).map e.symm
              pow := fun i => by rw [← map_pow, D.pow, map_one]
              sw_self := fun k => by
                rw [← map_mul, ← map_inv, ← map_mul, D.sw_self, map_inv]
              sw_other := fun j k hjk => by
                rw [← map_mul, ← map_inv, ← map_mul, D.sw_other j k hjk, map_mul, map_inv]
              T_ne := fun h => D.T_ne (e.symm.injective (by rw [h, map_one]))
              T_two := by
                obtain ⟨n, hn⟩ := D.T_two
                exact ⟨n, by rw [← map_pow, hn, map_one]⟩
              T_comm := fun i => (D.T_comm i).map e.symm
              T_sw := fun k => (D.T_sw k).map e.symm
              card := ?_ }⟩
    have hmap : (Subgroup.closure (Set.range D.X)).map e.symm.toMonoidHom =
        Subgroup.closure (Set.range fun k => e.symm (D.X k)) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    have := D.card
    rw [← hmap, Subgroup.card_map_of_injective e.symm.injective]
    exact this

end Transport

section Models

variable {p : ℕ}

theorem data_lin {S : Type} [Group S] (hp : p.Prime) (hp7 : 7 ≤ p) {F : Type} [Field F] [Finite F]
    (hpF : p ∣ Nat.card F - 1) {n : ℕ} (hn : n = p) (e : S ≃* projectiveSL n F) :
    UpperP p S ∧ Nonempty (LowerData p S) := by
  have e' : S ≃* projectiveSL p F := by subst hn; exact e
  have hpF' : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    have hc : 1 ≤ Nat.card F := Nat.card_pos
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpF'
  refine data_of_mulEquiv e' ?_ (linLowerData hp hp7 hpF)
  exact upperP_of_model hp hpK (linUpperModel hp (by omega) (by omega) hpF)

theorem data_uni {S : Type} [Group S] {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ ℓ ^ f + 1) {n : ℕ} (hn : n = p)
    (e : S ≃* primeFormP h (idGram K n)) :
    UpperP p S ∧ Nonempty (LowerData p S) := by
  have e' : S ≃* primeFormP h (idGram K p) := by subst hn; exact e
  have : Fact p.Prime := ⟨hp⟩
  have hpℓ : p ≠ ℓ := by
    intro hℓ
    subst hℓ
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have := (Nat.dvd_add_right h1).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := h.charP
    have h1 : ℓ ∣ p := (CharP.cast_eq_zero_iff K ℓ p).1 h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).1 h1).symm
  refine data_of_mulEquiv e' ?_ (uniLowerData h hp hp7 hpq)
  exact upperP_of_model hp hpK (uniUpperModel h hp hp7 hpq)

end Models

theorem localTwoBalanceLpEpsGtFive_proved : LocalTwoBalanceLpEpsGtFive := by
  intro G _ _ hG p hp hp5 X hX B hBX hB hrank h2 L hL idx hidx he
  obtain ⟨e⟩ := he
  have hp7 : 7 ≤ p := by
    by_contra h6
    have : p = 6 := by omega
    subst this
    norm_num at hp
  suffices hdata : UpperP p (barOf p L ⧸ Subgroup.center (barOf p L)) ∧
      Nonempty (LowerData p (barOf p L ⧸ Subgroup.center (barOf p L))) from
    isCompLocallyBalanced_of_data hp hp7 hBX hB hrank hL hdata.1 hdata.2
  obtain ⟨d, hv⟩ := idx
  change IsLpEpsIndex p d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hcardF : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
      rw [GaloisField.card _ _ Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    have hpF : p ∣ Nat.card (GaloisField Q.p Q.exponent) - 1 := by
      rw [hcardF]
      have h1n : 1 ≤ Q.card := by
        have := Nat.mod_le Q.card p
        omega
      refine (Nat.modEq_iff_dvd' h1n).1 ?_
      unfold Nat.ModEq
      rw [hQ, Nat.mod_eq_of_lt hp.one_lt]
    exact data_lin hp hp7 hpF (n := p - 1 + 1) (by omega)
      (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (p - 1) Q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (p - 1 + 1) _)))
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (p - 1) Q hv e
    obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData Q.p Q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h
      (isPrimeFormGram_idGram (n := p - 1 + 1) (K := K))
    have hpq : p ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    exact data_uni h hp hp7 hpq (n := p - 1 + 1) (by omega)
      ((eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
