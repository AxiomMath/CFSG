module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieOrder
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor lieSylowExponent
  lieSylowExponent_pos lie_bounds lie_casework LieOrderFormulasInput)

namespace SFM1

section Orders

private theorem prime_eq_two_of_pow_eq_two {p f : ℕ} (hp : p.Prime) (hf : f ≠ 0)
    (h : p ^ f = 2) : p = 2 := by
  have hdvd : p ∣ 2 := by rw [← h]; exact dvd_pow_self p hf
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd

private theorem card_mul_of_classical {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (hO : LieOrderFormulasInput) (ht : t ∈ CFSG.Blueprint.classicalTags)
    (h : CFSG.Models.LieModel S t n p f) :
    Nat.card S * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (hO S t n p f h.1 (CFSG.Models.LieModel.toBlueprint ht h)).2.1

private theorem card_u52_of_lieModel {S : Type} [Group S] {p f : ℕ} (hO : LieOrderFormulasInput)
    (h : CFSG.Models.LieModel S .PSU 5 p f) (hq : p ^ f = 2) : Nat.card S = 13685760 := by
  have hord := card_mul_of_classical hO (by decide) h
  rw [hq] at hord
  have h1 : lieOrderDivisor .PSU 5 2 = 1 := by decide
  have h2 : lieOrderNumerator .PSU 5 2 = 13685760 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem card_u42_of_lieModel {S : Type} [Group S] {p f : ℕ} (hO : LieOrderFormulasInput)
    (h : CFSG.Models.LieModel S .PSU (3 + 1) p f) (hq : p ^ f = 2) : Nat.card S = 25920 := by
  have hord := card_mul_of_classical hO (by decide) h
  rw [hq] at hord
  have h1 : lieOrderDivisor .PSU (3 + 1) 2 = 1 := by decide
  have h2 : lieOrderNumerator .PSU (3 + 1) 2 = 25920 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem card_sp62_of_lieModel {S : Type} [Group S] {p f : ℕ} (hO : LieOrderFormulasInput)
    (h : CFSG.Models.LieModel S .PSp 3 p f) (hq : p ^ f = 2) : Nat.card S = 1451520 := by
  have hord := card_mul_of_classical hO (by decide) h
  rw [hq] at hord
  have h1 : lieOrderDivisor .PSp 3 2 = 1 := by decide
  have h2 : lieOrderNumerator .PSp 3 2 = 1451520 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem card_l28_of_lieModel {S : Type} [Group S] {p f : ℕ} (hO : LieOrderFormulasInput)
    (h : CFSG.Models.LieModel S .PSL (1 + 1) p f) (hq : p ^ f = 8) : Nat.card S = 504 := by
  have hord := card_mul_of_classical hO (by decide) h
  rw [hq] at hord
  have h1 : lieOrderDivisor .PSL (1 + 1) 8 = 1 := by decide
  have h2 : lieOrderNumerator .PSL (1 + 1) 8 = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem card_eq_char_pow_twistedA (k : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA k q).Valid) :
    TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA k q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA k q, hv⟩ = q.p ^ q.exponent := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA k q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA k q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA k q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA k q
  rw [hc, hf]

private theorem prime_dvd_u52 {p : ℕ} (hp : p.Prime) (h : p ∣ 13685760) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11 := by
  obtain ⟨x, hx, rfl⟩ := CFSG.ComponentClassification.GS82PumpInputs.prime_mem_of_dvd_prod hp
    (l := [(2, 10), (3, 5), (5, 1), (11, 1)]) (by decide) (by simpa using h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

private theorem lieModel_odd_card_ne_u52 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : CFSG.Blueprint.LieModel X t n p f) : Nat.card X ≠ 13685760 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 13685760 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 13685760 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_u52 hp hpd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

private theorem card_of_isU5two (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (h : catalogIs S S9.isU5two) : Nat.card S = 13685760 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU5two, onLie] at hi
  | alternating n hn => simp [S9.isU5two, onLie] at hi
  | sporadic s => simp [S9.isU5two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA k q =>
      rcases k with _ | _ | _ | _ | _ | k <;> simp [S9.isU5two, onLie] at hi
      have hm := CFSG.Models.lieModel_twistedA 4 q hv e
      exact card_u52_of_lieModel hO hm ((card_eq_char_pow_twistedA 4 q hv).trans hi)
    | _ => simp [S9.isU5two, onLie] at hi

private theorem card_of_isSp6two (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (h : catalogIs S S9.isSp6two) : Nat.card S = 1451520 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isSp6two, onLie] at hi
  | alternating n hn => simp [S9.isSp6two, onLie] at hi
  | sporadic s => simp [S9.isSp6two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | B k q =>
      rcases k with _ | _ | _ | _ | k <;> simp [S9.isSp6two, onLie] at hi
      have hq : q.p ^ q.exponent = 2 := hi
      rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
      · exact card_sp62_of_lieModel hO hm hq
      · exfalso
        have hp : q.p = 2 :=
          prime_eq_two_of_pow_eq_two q.prime_p (by have := q.exponent_pos; omega) hq
        exact hm.1.2.2.2 hp
    | _ => simp [S9.isSp6two, onLie] at hi

private theorem card_of_ambiguous (hO : LieOrderFormulasInput) {r : ℕ} (hr2 : r ≠ 2)
    {S : Type} [Group S] {j : TauCeti.CFSGIndex} (hj : ambiguousChev r j) (f : S ≃* j.Group) :
    Nat.card S = 60 ∨ Nat.card S = 360 ∨ Nat.card S = 504 ∨ Nat.card S = 25920 := by
  cases j with
  | cyclic p hp => exact (show False from hj).elim
  | sporadic s => exact (show False from hj).elim
  | alternating n hn =>
    have f' : S ≃* alternatingGroup (Fin n) := f
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hc : Nat.card S = n.factorial / 2 := by
      rw [Nat.card_congr f'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have hj' : (n = 5 ∧ (r = 2 ∨ r = 5)) ∨ (n = 6 ∧ (r = 2 ∨ r = 3)) ∨ (n = 8 ∧ r = 2) := hj
    rcases hj' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hr⟩
    · exact Or.inl (hc.trans (by decide))
    · exact Or.inr (Or.inl (hc.trans (by decide)))
    · exact absurd hr hr2
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A k q =>
      cases k with
      | zero => exact (show False from hj).elim
      | succ k =>
        cases k with
        | zero =>
          have hj' : (q.card = 7 ∧ r = 2) ∨ (q.card = 8 ∧ r = 3) := hj
          rcases hj' with ⟨-, hr⟩ | ⟨hq8, -⟩
          · exact absurd hr hr2
          · have hq : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans hq8
            exact Or.inr (Or.inr (Or.inl
              (card_l28_of_lieModel hO (CFSG.Models.lieModel_A 1 q hv f) hq)))
        | succ k => exact (show False from hj).elim
    | twistedA k q =>
      cases k with
      | zero => exact (show False from hj).elim
      | succ k =>
        cases k with
        | zero => exact (show False from hj).elim
        | succ k =>
          cases k with
          | zero =>
            have hj' : q.card = 3 ∧ r = 2 := hj
            exact absurd hj'.2 hr2
          | succ k =>
            cases k with
            | zero =>
              have hj' : q.card = 2 ∧ r = 3 := hj
              exact Or.inr (Or.inr (Or.inr
                (card_u42_of_lieModel hO (CFSG.Models.lieModel_twistedA 3 q hv f)
                  ((card_eq_char_pow_twistedA 3 q hv).trans
                    ((TauCeti.PrimePower.card_def q).symm.trans hj'.1)))))
            | succ k => exact (show False from hj).elim
    | _ => exact (show False from hj).elim

end Orders

end SFM1

section Main


theorem K14NotChevOdd_holds : K14NotChevOdd := by
  intro S _ hcat r hr hr2 hchev
  have hO : LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hN : Nat.card S = 13685760 ∨ Nat.card S = 1451520 := by
    rcases hcat with h | h
    · exact Or.inl (SFM1.card_of_isU5two hO h)
    · exact Or.inr (SFM1.card_of_isSp6two hO h)
  rcases hchev with ⟨j, hj, ⟨f⟩⟩ | ⟨j, hj, ⟨f⟩⟩
  ·
    cases j with
    | cyclic p hp => exact (show False from hj).elim
    | alternating n hn => exact (show False from hj).elim
    | sporadic s => exact (show False from hj).elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have hd : d.characteristic = r := hj
      have hd2 : (⟨d, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic ≠ 2 := by
        change d.characteristic ≠ 2
        rw [hd]
        exact hr2
      obtain ⟨t, n, g, hX⟩ :=
        CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd ⟨d, hv⟩ hd2 f
      have hX' : CFSG.Blueprint.LieModel S t n r g := by
        rw [← hd]
        exact hX
      have hadm := hX'.admissible
      rcases hN with h | h
      · exact SFM1.lieModel_odd_card_ne_u52 hO hr2 hadm hX' h
      · exact CFSG.ComponentClassification.GS82PumpInputs.lieModel_odd_card_ne_sp62 hO hr2 hadm hX' h
  ·
    have h4 := SFM1.card_of_ambiguous hO hr2 hj f
    omega

end Main

end CFSG.LocalAnalysis.GLTheoremA

end
