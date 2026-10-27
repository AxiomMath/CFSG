module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinCat
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived inner_map_congr
  mem_innAutDerived_congr)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U

theorem A2'_excluded (q : TauCeti.PrimePower) (h : 3 ∣ q.card + 1) (hq3 : 3 ≤ q.card) :
    k2Lie 3 (TauCeti.LieTypeIndex.twistedA 2 q) ∨ k3Lie (TauCeti.LieTypeIndex.twistedA 2 q) := by
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hp := q.prime_p
  by_cases h2 : q.p = 2
  · left
    have hodd : Odd q.exponent := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨k, hk⟩ := hev
      rw [hq, h2, hk] at h
      have h4 : ∀ j : ℕ, 4 ^ j % 3 = 1 := by
        intro j
        rw [Nat.pow_mod]
        norm_num
      have h2k : 2 ^ (k + k) = 4 ^ k := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [h2k] at h
      have := h4 k
      omega
    have hgt : 1 < q.exponent := by
      by_contra hle
      have he1 : q.exponent = 1 := by
        have := q.exponent_pos
        omega
      rw [hq, h2, he1] at hq3
      norm_num at hq3
    exact ⟨rfl, h2, hodd, hgt⟩
  · right
    have hodd : Odd q.card := by
      rw [hq]
      rcases hp.eq_two_or_odd' with h' | h'
      · exact absurd h' h2
      · exact h'.pow
    obtain ⟨j, hj⟩ := hodd
    show q.card % 6 = 5
    omega

theorem kd264Y1OutUni_core (r : ℕ) (q : TauCeti.PrimePower) (ℓ f : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = q.p)
    (hf : f = q.exponent) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSU (r + 1) (ℓ ^ f) (GaloisField ℓ (2 * f))))
    (hn : 2 ≤ r) (hqne : ¬ (r + 1 = 3 ∧ q.p ^ q.exponent = 2))
    (hnot2 : r = 2 → ¬ 3 ∣ q.p ^ q.exponent + 1)
    (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) :
    ∀ a ∈ innAutDerived S, a ^ 3 = 1 → a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  subst hℓ hf
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  set K : Type := GaloisField q.p (2 * q.exponent) with hKdef
  have hK : Nat.card K = q.p ^ (2 * q.exponent) :=
    GaloisField.card q.p (2 * q.exponent) (by have := q.exponent_pos; omega)
  let h : UnitaryFieldData q.p q.exponent K := ⟨q.prime_p, q.exponent_pos, hK⟩
  intro a ha ha3
  by_cases hdiv : 3 ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1)
  ·
    exfalso
    have h3r : 3 ∣ r + 1 := dvd_trans hdiv (Nat.gcd_dvd_left _ _)
    have h3q : 3 ∣ q.p ^ q.exponent + 1 := dvd_trans hdiv (Nat.gcd_dvd_right _ _)
    rcases Nat.lt_or_ge (r + 1) 6 with hsmall | hbig
    · have hr2 : r = 2 := by omega
      exact hnot2 hr2 h3q
    · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_card_81_unitary h h3q (m := r + 1) hbig
      have hEs := isElemAbelian_three_map e.symm hE
      have hcs : Nat.card (E.map e.symm.toMonoidHom) = 3 ^ 4 := by
        rw [Subgroup.card_map_of_injective e.symm.injective, hc]
      have h4 := le_pRank_of_elemAbelian_card (p := 3) (by norm_num) le_top hEs hcs
      omega
  ·
    have hn3 : 3 ≤ r + 1 := by omega
    have hr1 : 1 ≤ r + 1 := by omega
    have haP : MulAut.congr e a ∈
        innAutDerived (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent) K)) :=
      (mem_innAutDerived_congr e).2 ha
    have hpowP : (MulAut.congr e a) ^ 3 = 1 := by
      rw [← map_pow, ha3, map_one]
    have ha1 : MulAut.congr (uTransport h hr1) (MulAut.congr e a) ∈
        innAutDerived (primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) :=
      (mem_innAutDerived_congr (uTransport h hr1)).2 haP
    have ha13 : (MulAut.congr (uTransport h hr1) (MulAut.congr e a)) ^ 3 = 1 := by
      rw [← map_pow, hpowP, map_one]
    obtain ⟨A, c, hc1, hA3, hβ⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived
        h uGram_one hn3 hqne ha1 ha13
    have hin1 : MulAut.congr (uTransport h hr1) (MulAut.congr e a) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) := by
      rw [hβ]
      exact primeFormConjHom_mem_inner_of_det h hn3 hdiv A c hc1 hA3
    rw [← inner_map_congr (uTransport h hr1)] at hin1
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin1
    have hb' : b = MulAut.congr e a := (MulAut.congr (uTransport h hr1)).injective hba
    rw [hb'] at hb
    rw [← inner_map_congr e] at hb
    obtain ⟨b2, hb2, hb2a⟩ := Subgroup.mem_map.mp hb
    have hb2' : b2 = a := (MulAut.congr e).injective hb2a
    rw [hb2'] at hb2
    exact hb2

theorem kd264Y1OutUni_holds : ∀ (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group],
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = TauCeti.LieTypeIndex.twistedA r q) →
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ 3 →
    ∀ a ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, a ^ 3 = 1 →
      a ∈ inner (TauCeti.CFSGIndex.lie d).Group := by
  rintro ⟨e, hv⟩ hfin ⟨r, q, hd⟩ _hR hk2 hk3 hpR
  simp only at hd
  subst hd
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hqcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hqne : ¬ (r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨hr3, h2⟩
    have hr2 : r = 2 := by omega
    have h3 := hr.2 hr2
    rw [hqcard, h2] at h3
    omega
  have hnot2 : r = 2 → ¬ 3 ∣ q.p ^ q.exponent + 1 := by
    intro hr2 h3
    rw [← hqcard] at h3
    have hq3 : 3 ≤ q.card := hr.2 hr2
    subst hr2
    rcases A2'_excluded q h3 hq3 with h' | h'
    · exact hk2 h'
    · exact hk3 h'
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  exact kd264Y1OutUni_core r q _ _ hc hf
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv) hr.1 hqne hnot2 hpR

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
