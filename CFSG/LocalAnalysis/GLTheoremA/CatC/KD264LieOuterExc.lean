module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamF4
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamG2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.TauCetiBridge
open scoped Pointwise

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem dvd_pow_six_sub_one_of_dvd_card_adjointG2 {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hcard : p ∣ Nat.card (adjointGroup Tag.G2 K)) :
    p ∣ Nat.card K ^ 6 - 1 := by
  have hord : p ∣ CFSG.Open.ordG2 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
    exact hcard
  unfold CFSG.Open.ordG2 at hord
  rcases (Nat.Prime.dvd_mul hp).1 hord with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow hp h) hpK
    · exact h
  · have ha : 1 ≤ Nat.card K := Nat.card_pos
    have hz : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
      have h1 : (((Nat.card K) ^ 2 - 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ p).2 h
      rw [Nat.cast_sub (Nat.one_le_pow 2 (Nat.card K) ha), Nat.cast_pow, Nat.cast_one] at h1
      exact sub_eq_zero.1 h1
    have hz6 : ((Nat.card K : ℕ) : ZMod p) ^ 6 = 1 := by
      calc ((Nat.card K : ℕ) : ZMod p) ^ 6 =
          (((Nat.card K : ℕ) : ZMod p) ^ 2) ^ 3 := by ring
        _ = 1 := by rw [hz]; ring
    have h2 : (((Nat.card K) ^ 6 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow 6 (Nat.card K) ha), Nat.cast_pow, Nat.cast_one, hz6,
        sub_self]
    exact (ZMod.natCast_eq_zero_iff _ p).1 h2

private theorem fieldCoreAt_adjointG2_of_dvd_card {q : TauCeti.PrimePower} {K : Type}
    [Field K] [Finite K] (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    (hKchar : CharP K q.p) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.G2 K)) :
    ∀ x : MulAut (adjointGroup Tag.G2 K), x ^ p = 1 → x ∉ innAutDerived (adjointGroup Tag.G2 K) →
      FieldCoreAt p x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hd6 := dvd_pow_six_sub_one_of_dvd_card_adjointG2 hp hpK hcard
  have ha : 1 ≤ Nat.card K := Nat.card_pos
  have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 6 - 1 := by
    intro σ hσp
    exact dvd_pow_sub_one_of_cast_eq ha Nat.card_pos
      (card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp).symm hd6
  have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ))) :=
    fun σ hσp => not_coprime_card_adjointG2_of_dvd_pow_six (fixSubfield σ) hp (hdf σ hσp)
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : adjointGroup Tag.G2 K →*
      MulAut (adjointGroup Tag.G2 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h2 : q.p = 2
  · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
    have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hf2 : 2 ≤ q.exponent := by
      by_contra hlt
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [TauCeti.PrimePower.card_def, h2, h1] at hq3
      omega
    by_cases hq8 : p = 3 ∧ q.exponent = 3
    · obtain ⟨rfl, hf3⟩ := hq8
      exact g2EightFieldCore K (by rw [hK2, hf3]; norm_num) x hxord hxinner
    · by_cases hp7 : 7 ≤ p
      · exact fieldCoreAt_G2_even_of_dvd_pow_six hf2 K hK2 hp hp7 hdf hxord hxinner
      · have hp35 : p = 3 ∨ p = 5 := by
          have hp3 : 3 ≤ p := by
            have := hp.two_le
            omega
          have hp6 : p ≤ 6 := by omega
          interval_cases p
          · exact Or.inl rfl
          · exact absurd hp (by norm_num)
          · exact Or.inr rfl
          · exact absurd hp (by norm_num)
        have hk3 : ∀ σ : K ≃+* K, orderOf σ = p → 3 ≤ Nat.card (fixSubfield σ) := by
          intro σ hσp
          obtain ⟨hdvdf, hcardσ⟩ := SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK2 σ
          rw [hσp] at hdvdf hcardσ
          obtain ⟨m, hm⟩ := hdvdf
          have hm0 : 0 < m := by
            rcases Nat.eq_zero_or_pos m with rfl | h
            · rw [mul_zero] at hm
              omega
            · exact h
          rw [hm, Nat.mul_div_cancel_left _ hp.pos] at hcardσ
          have hm1 : m ≠ 1 := by
            rintro rfl
            have h63 := hdf σ hσp
            rw [hcardσ] at h63
            norm_num at h63
            rcases hp35 with rfl | rfl
            · exact hq8 ⟨rfl, by omega⟩
            · exact absurd h63 (by norm_num)
          rw [hcardσ]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact fieldCoreAt_G2_even hf2 K hK2 hp hk3 hdvd hxord hxinner
  · by_cases h3 : q.p = 3
    · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK', h3]
      have hchar : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := by
        rw [show CFSG.LieType.Ree.ReeTag.G2.prime = 3 from rfl, ← h3]
        exact hKchar
      exact fieldCoreAt_G2_three q.exponent_pos K hK3 hp hp2 hdvd hxord hxinner
    · have hNF := conj_normalForm_of_pointwise
        (odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p h2 q.exponent_pos K hK'
          .G2 (Or.inr ⟨rfl, h3⟩)).1
      exact fieldCoreAt_of_oddInnerField q.prime_p h2 q.exponent_pos K hK' hNF hp hdvd hxord hxinner

private theorem fieldCoreAt_adjointF4_of_dvd_card {q : TauCeti.PrimePower} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.F4 K)) :
    ∀ x : MulAut (adjointGroup Tag.F4 K), x ^ p = 1 → x ∉ innAutDerived (adjointGroup Tag.F4 K) →
      FieldCoreAt p x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hdvd : p ∣ CFSG.Open.ordF4 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    exact hcard
  have hcnt : 0 < degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) :=
    degCount_F4_pos_of_dvd_ordF4 hp Nat.card_pos hpK hdvd
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : adjointGroup Tag.F4 K →*
      MulAut (adjointGroup Tag.F4 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  exact fieldCoreAt_adjointF4 q.prime_p q.exponent_pos K hK' hp hp2 hcnt hxord hxinner

theorem degCount_E6_pos_of_dvd_card {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E6 K)) :
    0 < degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h0
  have hzero : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0 := by omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := adjointGroup Tag.E6 K) p hcard
  have hzF : IsElemAbelian p (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hy]; exact pow_orderOf_eq_one y)
  have hzcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have h1 := elemAbelian_card_eq_one_of_degCount_zero (τ := Tag.E6) (Or.inl rfl) K hp
    (by omega) hpK rfl hzero hzF
  rw [hzcard] at h1
  exact hp.one_lt.ne' h1

private theorem fieldCoreAt_adjointE6_of_dvd_card {q : TauCeti.PrimePower} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E6 K)) :
    ∀ x : MulAut (adjointGroup Tag.E6 K), x ^ p = 1 → x ∉ innAutDerived (adjointGroup Tag.E6 K) →
      FieldCoreAt p x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  by_cases h3 : p = 3
  · subst h3
    have hq3 : q.p ≠ 3 := fun h => hpq h.symm
    have hxI : x ∉ e6Inndiag K := fun hmem =>
      hxo (commutator_le_innAutDerived _ (e6Inndiag_le_commutator (K := K) hmem))
    exact fieldCoreAt_E6_of_not_mem_e6Inndiag q.prime_p hq3 q.exponent_pos K hK' hxp hxI
  · have hp5 : 5 ≤ p := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    have hcnt := degCount_E6_pos_of_dvd_card hp hp5 hpK hcard
    exact fieldCoreAt_adjointE6 q.prime_p q.exponent_pos K hK' hp (by omega) hcnt hxord hxinner

theorem degCount_E7_pos_of_dvd_card {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E7 K)) :
    0 < degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h0
  have hzero : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0 := by omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := adjointGroup Tag.E7 K) p hcard
  have hzF : IsElemAbelian p (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hy]; exact pow_orderOf_eq_one y)
  have hzcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have h1 := elemAbelian_card_eq_one_of_degCount_zero (τ := Tag.E7) (Or.inr (Or.inl rfl)) K hp
    (by omega) hpK rfl hzero hzF
  rw [hzcard] at h1
  exact hp.one_lt.ne' h1

theorem degCount_E8_pos_of_dvd_card {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E8 K)) :
    0 < degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h0
  have hzero : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 0 := by omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := adjointGroup Tag.E8 K) p hcard
  have hzF : IsElemAbelian p (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hy]; exact pow_orderOf_eq_one y)
  have hzcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have h1 := elemAbelian_card_eq_one_of_degCount_zero (τ := Tag.E8) (Or.inr (Or.inr rfl)) K hp
    (by omega) hpK rfl hzero hzF
  rw [hzcard] at h1
  exact hp.one_lt.ne' h1

theorem degCount_E78_pos_three {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) (hpK : ¬ 3 ∣ Nat.card K) :
    0 < degCount τ (orderOf ((Nat.card K : ℕ) : ZMod 3)) := by
  have hq0 : ((Nat.card K : ℕ) : ZMod 3) ≠ 0 := fun h =>
    hpK ((ZMod.natCast_eq_zero_iff (Nat.card K) 3).1 h)
  have he2 : orderOf ((Nat.card K : ℕ) : ZMod 3) ∣ 2 := by
    have h := ZMod.orderOf_dvd_card_sub_one hq0
    simpa using h
  have h2mem : 2 ∈ degreesW τ := by rcases hτ with rfl | rfl <;> decide
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨h2mem, by simpa using he2⟩)

private theorem fieldCoreAt_adjointE7_of_dvd_card {q : TauCeti.PrimePower} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E7 K)) :
    ∀ x : MulAut (adjointGroup Tag.E7 K), x ^ p = 1 → x ∉ innAutDerived (adjointGroup Tag.E7 K) →
      FieldCoreAt p x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : adjointGroup Tag.E7 K →*
      MulAut (adjointGroup Tag.E7 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  have hcnt : 0 < degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_cases h3 : p = 3
    · subst h3
      exact degCount_E78_pos_three (Or.inl rfl) hpK
    · have hp5 : 5 ≤ p := by
        have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
        omega
      exact degCount_E7_pos_of_dvd_card hp hp5 hpK hcard
  exact fieldCoreAt_adjointE7 q.prime_p q.exponent_pos K hK' hp hp2 hcnt hxord hxinner

private theorem fieldCoreAt_adjointE8_of_dvd_card {q : TauCeti.PrimePower} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card) (hK' : Nat.card K = q.p ^ q.exponent)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hcard : p ∣ Nat.card (adjointGroup Tag.E8 K)) :
    ∀ x : MulAut (adjointGroup Tag.E8 K), x ^ p = 1 → x ∉ innAutDerived (adjointGroup Tag.E8 K) →
      FieldCoreAt p x := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  intro x hxp hxo
  have hxinner : x ∉ (MulAut.conj : adjointGroup Tag.E8 K →*
      MulAut (adjointGroup Tag.E8 K)).range :=
    fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxp fun h => hxinner (by rw [h]; exact one_mem _)
  have hcnt : 0 < degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_cases h3 : p = 3
    · subst h3
      exact degCount_E78_pos_three (Or.inr rfl) hpK
    · have hp5 : 5 ≤ p := by
        have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
        omega
      exact degCount_E8_pos_of_dvd_card hp hp5 hpK hcard
  exact fieldCoreAt_adjointE8 q.prime_p q.exponent_pos K hK' hp hcnt hxord hxinner

private theorem outerPLayerAt_G2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_G2] at h
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hK' : Nat.card K = q.p ^ q.exponent :=
    hKcard.trans (TauCeti.PrimePower.card_def q)
  have eS : S ≃* adjointGroup Tag.G2 K := e.trans eK
  have hpdvdM : p ∣ Nat.card (adjointGroup Tag.G2 K) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
    (fieldCoreAt_adjointG2_of_dvd_card hv hKcard hK' hKchar hp hp2 hpq.symm hpdvdM)

private theorem outerPLayerAt_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.F4 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_F4] at h
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hK' : Nat.card K = q.p ^ q.exponent :=
    hKcard.trans (TauCeti.PrimePower.card_def q)
  have eS : S ≃* adjointGroup Tag.F4 K := e.trans eK
  have hpdvdM : p ∣ Nat.card (adjointGroup Tag.F4 K) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
    (fieldCoreAt_adjointF4_of_dvd_card hKcard hK' hp hp2 hpq.symm hpdvdM)

private theorem outerPLayerAt_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E6 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_E6] at h
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent :=
    hKcard.trans (TauCeti.PrimePower.card_def q)
  have eS : S ≃* adjointGroup Tag.E6 K := e.trans eK
  have hpdvdM : p ∣ Nat.card (adjointGroup Tag.E6 K) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
    (fieldCoreAt_adjointE6_of_dvd_card hKcard hK' hp hp2 hpq.symm hpdvdM)

private theorem outerPLayerAt_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E7 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_E7] at h
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hK' : Nat.card K = q.p ^ q.exponent :=
    hKcard.trans (TauCeti.PrimePower.card_def q)
  have eS : S ≃* adjointGroup Tag.E7 K := e.trans eK
  have hpdvdM : p ∣ Nat.card (adjointGroup Tag.E7 K) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
    (fieldCoreAt_adjointE7_of_dvd_card hKcard hK' hp hp2 hpq.symm hpdvdM)

private theorem outerPLayerAt_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.E8 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_E8] at h
  obtain ⟨K, _, _, hKcard, hKchar, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hK' : Nat.card K = q.p ^ q.exponent :=
    hKcard.trans (TauCeti.PrimePower.card_def q)
  have eS : S ≃* adjointGroup Tag.E8 K := e.trans eK
  have hpdvdM : p ∣ Nat.card (adjointGroup Tag.E8 K) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
    (fieldCoreAt_adjointE8_of_dvd_card hKcard hK' hp hp2 hpq.symm hpdvdM)

theorem lieOuterPLayer_excUntwisted : ∀ p : ℕ, p.Prime → p ≠ 2 →
    LieOuterPLayer p isExcUntwistedIdx := by
  intro p hp hp2 d hd hP hnExc S hS hfin he hnot hpdvd
  obtain ⟨e⟩ := he
  cases d with
  | G2 q => exact outerPLayerAt_G2 hp hp2 hd e hnot hpdvd
  | F4 q => exact outerPLayerAt_F4 hp hp2 hd e hnot hpdvd
  | E6 q => exact outerPLayerAt_E6 hp hp2 hd e hnot hpdvd
  | E7 q => exact outerPLayerAt_E7 hp hp2 hd e hnot hpdvd
  | E8 q => exact outerPLayerAt_E8 hp hp2 hd e hnot hpdvd
  | A n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedA n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | B n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | C n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | D n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedD n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedE6 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | trialityD4 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | suzuki k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeG2 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeF4 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | tits => exact absurd hP (by simp [isExcUntwistedIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
