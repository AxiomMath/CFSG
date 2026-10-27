module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.K128.G2Syl

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Odd


theorem pRank_le_one_adjointG2_odd (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : ¬ p ∣ Nat.card K)
    (hdvd : p ∣ Nat.card (adjointGroup .G2 K)) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) :
    CFSG.pRank p (adjointGroup .G2 K) ≤ 1 := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hy : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [card_adjointGroup_G2] at hdvd
  have h6 : p ∣ Nat.card K ^ 6 - 1 := by
    unfold ordG2 at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpQ
      · exact h
    · exact absurd h hnd
  have hfac : Nat.card K ^ 6 - 1 =
      (Nat.card K ^ 2 - 1) * ((Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1) := by
    have := CFSG.RankThree.PartOne.K128.pow3_sub_one (Nat.card K ^ 2) hy
    rwa [← pow_mul] at this
  rw [hfac] at h6
  have hΦ : p ∣ (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 :=
    ((Nat.Prime.dvd_mul hp).1 h6).resolve_left hnd
  have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hΦfac : (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 =
      (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 - Nat.card K + 1) := by
    zify [hle]
    ring
  rw [hΦfac] at hΦ
  rcases (Nat.Prime.dvd_mul hp).1 hΦ with h | h
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK 1
      (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hp (by omega) h
    exact CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_pSubgroups hp hcyc
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK
      (-1) (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hle]; ring) hp
      (by omega) h
    exact CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_pSubgroups hp hcyc

end Odd

section Inner


theorem extSeitzAtInnerFor_G2_oddQPlus {q : TauCeti.PrimePower} (hq : q.p ≠ 2)
    (hq11 : 11 ≤ q.card) : CTP.ExtSeitzAtInnerFor (.G2 q) fun p => ¬ p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := CTP.exists_adjointG2_model hiso
  have hXq : Nat.card X = q.card := by rw [hX, PrimePower.card_def]
  have : IsSimpleGroup (adjointGroup .G2 X) := MulEquiv.isSimpleGroup e.symm
  have hXodd : Odd (Nat.card X) := by
    rw [hX]
    exact (q.prime_p.odd_of_ne_two hq).pow
  have h11 : 11 ≤ Nat.card X := by rw [hXq]; exact hq11
  refine CTP.closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  by_cases hpq : p ∣ Nat.card X + 1
  · exact CFSG.RankThree.PartOne.SEITZ11.G2Seven.closure_cenGen_adjointG2_odd_qplus_eq_top X hXodd
      h11 hp hp5 hpq E₁ hE₁p hcard₁
  · exfalso
    have hq1 : 1 ≤ Nat.card X := Nat.card_pos
    have hnd : ¬ p ∣ Nat.card X ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hq1]
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hP (by rwa [← hXq])
      · exact hpq h
    have hpQ : ¬ p ∣ Nat.card X := by
      intro h
      rw [hX] at h
      have h1 : p ∣ q.p := hp.dvd_of_dvd_pow h
      have h2 : p = q.p := (Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 h1
      exact hpd (h2.trans (LieTypeIndex.characteristic_G2 q).symm)
    have : Finite (ModGL .G2 X) := finite_modGL
    have hdvd : p ∣ Nat.card (adjointGroup .G2 X) := by
      have h1 := Subgroup.card_subgroup_dvd_card E₁
      rw [hcard₁] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have h1 := pRank_le_one_adjointG2_odd X hXodd hp hp5 hpQ hdvd hnd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
    omega

end Inner

end CFSG.LieType.SeitzGeneration
