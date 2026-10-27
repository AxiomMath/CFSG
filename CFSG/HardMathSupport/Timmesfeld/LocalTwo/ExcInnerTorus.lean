module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.RankThree.PartOne.K128.G2Syl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.K133H

theorem orderOf_eq_one_of_dvd_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) :
    orderOf ((q : ℕ) : ZMod p) = 1 := by
  rw [orderOf_eq_one_iff]
  have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem dvd_sub_one_of_orderOf_eq_one {p q : ℕ} (hq : 1 ≤ q) (h : orderOf ((q : ℕ) : ZMod p) = 1) :
    p ∣ q - 1 := by
  have := (dvd_pow_sub_one_iff_orderOf (d := 1) hq h).2 dvd_rfl
  simpa using this

theorem factorization_eq_of_mul_eq {p N g M : ℕ} (hN : N ≠ 0) (hg0 : g ≠ 0)
    (hg : ¬ p ∣ g) (h : N * g = M) : N.factorization p = M.factorization p := by
  rw [← h, Nat.factorization_mul hN hg0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hg, add_zero]

theorem not_dvd_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hd : p ∣ q - 1) :
    ¬ p ∣ q := by
  intro h
  have h1 : p ∣ q - (q - 1) := Nat.dvd_sub h hd
  rw [show q - (q - 1) = 1 by omega] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem not_dvd_degreesE_E6 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    ∀ d ∈ degreesE Tag.E6, ¬ p ∣ d := by
  intro d hd hdvd
  have hd' : d ∈ [2, 5, 6, 8, 9, 12] := hd
  have hd0 : 0 < d := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hd12 : d ≤ 12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hle : p ≤ 12 := (Nat.le_of_dvd hd0 hdvd).trans hd12
  have key : ∀ p ∈ Finset.Icc 7 12, p.Prime → ∀ d ∈ [2, 5, 6, 8, 9, 12], ¬ p ∣ d := by decide
  exact key p (Finset.mem_Icc.2 ⟨h7, hle⟩) hp d hd' hdvd

theorem not_dvd_degreesE_E7 {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) :
    ∀ d ∈ degreesE Tag.E7, ¬ p ∣ d := by
  intro d hd hdvd
  have hd' : d ∈ [2, 6, 8, 10, 12, 14, 18] := hd
  have hd0 : 0 < d := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hd18 : d ≤ 18 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hle : p ≤ 18 := (Nat.le_of_dvd hd0 hdvd).trans hd18
  have key : ∀ p ∈ Finset.Icc 11 18, p.Prime → ∀ d ∈ [2, 6, 8, 10, 12, 14, 18], ¬ p ∣ d := by
    decide
  exact key p (Finset.mem_Icc.2 ⟨h11, hle⟩) hp d hd' hdvd

theorem not_dvd_degreesE_E8 {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) :
    ∀ d ∈ degreesE Tag.E8, ¬ p ∣ d := by
  intro d hd hdvd
  have hd' : d ∈ [2, 8, 12, 14, 18, 20, 24, 30] := hd
  have hd0 : 0 < d := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hd30 : d ≤ 30 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'; omega
  have hle : p ≤ 30 := (Nat.le_of_dvd hd0 hdvd).trans hd30
  have key : ∀ p ∈ Finset.Icc 11 30, p.Prime → ∀ d ∈ [2, 8, 12, 14, 18, 20, 24, 30], ¬ p ∣ d := by
    decide
  exact key p (Finset.mem_Icc.2 ⟨h11, hle⟩) hp d hd' hdvd

section Toral

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false


theorem localDeltaIn_eq_bot_of_conj_into_torus {τ : Tag} [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hconj : ∀ {A : Subgroup (ModGL τ K)}, A ≤ adjointGroup τ K → (∀ x ∈ A, x ^ p = 1) →
      ∃ g ∈ adjointGroup τ K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup τ K)
    {H : Subgroup (MulAut (adjointGroup τ K))} (hH : innerAut (adjointGroup τ K) ≤ H)
    {D : Subgroup (MulAut (adjointGroup τ K))} (hDin : D ≤ innerAut (adjointGroup τ K))
    (hpow : ∀ x ∈ D, x ^ p = 1) (hcard : p < Nat.card D) : localDeltaIn p H D = ⊥ := by
  obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd hp hp2 hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))
  have hpow₀ : ∀ x ∈ D₀.map (adjointGroup τ K).subtype, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj y) ^ p = 1 := hpow _ hy
    have hyp : y ^ p = 1 := hinj (by rw [map_pow, hy', map_one])
    rw [← map_pow, hyp, map_one]
  obtain ⟨g, hg, hgT⟩ := hconj (Subgroup.map_subtype_le D₀) hpow₀
  exact localDeltaIn_eq_bot_of_conj_toral hp htp ht hH hDin hpow hcard ⟨g, hg⟩
    fun x hx => hgT ⟨x, ⟨x, hx, rfl⟩, rfl⟩

theorem exists_conj_into_torus_of_factorization {τ : Tag} [Finite K] {p : ℕ} (hp : p.Prime)
    (hord : (Nat.card (adjointGroup τ K)).factorization p =
      (Nat.card (torusGroup τ K)).factorization p)
    {A : Subgroup (ModGL τ K)} (hAC : A ≤ adjointGroup τ K) (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup τ K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup τ K := by
  have : Fact p.Prime := ⟨hp⟩
  exact exists_conj_le_of_sylow (p := p) torusGroup_le_adjointGroup' hAC hpow hord

theorem exists_conj_into_torus_G2 [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (ModGL .G2 K)} (hAC : A ≤ adjointGroup .G2 K)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup .G2 K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup .G2 K := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card K := not_dvd_of_dvd_sub_one hp hQ hpq
  have hdQ : p ∣ Nat.card K ^ 2 - 1 := by
    rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ (by omega)]
    exact Dvd.dvd.mul_right hpq _
  have hnQ1 : ¬ p ∣ Nat.card K + 1 := by
    intro h
    have h1 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h hpq
    rw [show (Nat.card K + 1) - (Nat.card K - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hvp : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K - 1).factorization p := by
    rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ (by omega),
      Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnQ1, add_zero]
  refine exists_conj_into_torus_of_factorization hp ?_ hAC hpow
  rw [card_adjointGroup_G2, card_torusGroup_G2,
    CFSG.RankThree.PartOne.K128.factorization_ordG2 hp hp5 hQ hpK hdQ, hvp,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem factorization_card_adjointGroup_E_of_dvd_sub_one {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) (hdeg : ∀ d ∈ degreesE τ, ¬ p ∣ d) :
    (Nat.card (adjointGroup τ K)).factorization p =
      (degreesE τ).length * (Nat.card K - 1).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card K := not_dvd_of_dvd_sub_one hp hq2 hpq
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 1 :=
    orderOf_eq_one_of_dvd_sub_one (by omega) hpq
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with rfl | rfl | rfl <;> decide
  have h1 := ordProj_card_adjointGroup_E hτ hp hp3 hpK
  rw [prod_ordProj_pow_sub_one hp (by omega) hpK hq2 he (degreesE τ)
    (fun d hd _ => ⟨(hcard d hd).ne', by simpa using hdeg d hd⟩)] at h1
  have hfilt : ((degreesE τ).filter fun d => 1 ∣ d).length = (degreesE τ).length := by
    rw [List.filter_eq_self.2 (fun d _ => by simp)]
  rw [hfilt, pow_one, ← pow_mul, mul_comm] at h1
  exact Nat.pow_right_injective hp.two_le h1

theorem factorization_card_torusGroup_E6 [Finite K] {p : ℕ} (hp3 : 3 < p) :
    (Nat.card (torusGroup .E6 K)).factorization p = 6 * (Nat.card K - 1).factorization p := by
  have h := card_torusGroup_E6 (K := K)
  have hg : ¬ p ∣ (Nat.card K - 1).gcd 3 := fun hd =>
    absurd (Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_right _ _))) (by omega)
  rw [factorization_eq_of_mul_eq Nat.card_pos.ne' (Nat.gcd_pos_of_pos_right _ (by norm_num)).ne'
    hg h, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem factorization_card_torusGroup_E7 [Finite K] {p : ℕ} (hp3 : 3 < p) :
    (Nat.card (torusGroup .E7 K)).factorization p = 7 * (Nat.card K - 1).factorization p := by
  have h := card_torusGroup_E7 (K := K)
  have hg : ¬ p ∣ (Nat.card K - 1).gcd 2 := fun hd =>
    absurd (Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_right _ _))) (by omega)
  rw [factorization_eq_of_mul_eq Nat.card_pos.ne' (Nat.gcd_pos_of_pos_right _ (by norm_num)).ne'
    hg h, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem factorization_card_torusGroup_E8 [Finite K] {p : ℕ} :
    (Nat.card (torusGroup .E8 K)).factorization p = 8 * (Nat.card K - 1).factorization p := by
  rw [card_torusGroup_E8, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem exists_conj_into_torus_E6 [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (ModGL .E6 K)} (hAC : A ≤ adjointGroup .E6 K)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup .E6 K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup .E6 K := by
  refine exists_conj_into_torus_of_factorization hp ?_ hAC hpow
  rw [factorization_card_adjointGroup_E_of_dvd_sub_one (Or.inl rfl) hp (by omega) hpq
    (not_dvd_degreesE_E6 hp hp7), factorization_card_torusGroup_E6 (by omega)]
  rfl

theorem exists_conj_into_torus_E7 [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (ModGL .E7 K)} (hAC : A ≤ adjointGroup .E7 K)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup .E7 K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup .E7 K := by
  refine exists_conj_into_torus_of_factorization hp ?_ hAC hpow
  rw [factorization_card_adjointGroup_E_of_dvd_sub_one (Or.inr (Or.inl rfl)) hp (by omega) hpq
    (not_dvd_degreesE_E7 hp hp11), factorization_card_torusGroup_E7 (by omega)]
  rfl

theorem exists_conj_into_torus_E8 [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (ModGL .E8 K)} (hAC : A ≤ adjointGroup .E8 K)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup .E8 K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup .E8 K := by
  refine exists_conj_into_torus_of_factorization hp ?_ hAC hpow
  rw [factorization_card_adjointGroup_E_of_dvd_sub_one (Or.inr (Or.inr rfl)) hp (by omega) hpq
    (not_dvd_degreesE_E8 hp hp11), factorization_card_torusGroup_E8]
  rfl

theorem innerPlanes_adjointG2_of_dvd_sub_one [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : InnerPlaneBalance p (adjointGroup .G2 K) := by
  intro E hEin hE hcard H hH
  refine localDeltaIn_eq_bot_of_conj_into_torus hp (by omega) hpq
    (fun hA hpow => exists_conj_into_torus_G2 hp hp5 hpq hA hpow) hH hEin hE.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

theorem innerPlanes_adjointF4_of_dvd_sub_one' [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : InnerPlaneBalance p (adjointGroup .F4 K) :=
  fun E hEin hE hcard H hH =>
    innerPlanes_adjointF4_of_dvd_sub_one K hp hp5 hpq E hEin hE hcard H hH

theorem innerPlanes_adjointE6_of_dvd_sub_one [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : InnerPlaneBalance p (adjointGroup .E6 K) := by
  intro E hEin hE hcard H hH
  refine localDeltaIn_eq_bot_of_conj_into_torus hp (by omega) hpq
    (fun hA hpow => exists_conj_into_torus_E6 hp hp7 hpq hA hpow) hH hEin hE.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

theorem innerPlanes_adjointE7_of_dvd_sub_one [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : InnerPlaneBalance p (adjointGroup .E7 K) := by
  intro E hEin hE hcard H hH
  refine localDeltaIn_eq_bot_of_conj_into_torus hp (by omega) hpq
    (fun hA hpow => exists_conj_into_torus_E7 hp hp11 hpq hA hpow) hH hEin hE.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

theorem innerPlanes_adjointE8_of_dvd_sub_one [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : InnerPlaneBalance p (adjointGroup .E8 K) := by
  intro E hEin hE hcard H hH
  refine localDeltaIn_eq_bot_of_conj_into_torus hp (by omega) hpq
    (fun hA hpow => exists_conj_into_torus_E8 hp hp11 hpq hA hpow) hH hEin hE.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end Toral

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
