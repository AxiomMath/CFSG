module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubModels
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)
open CFSG.Assembly.LowTwoRank

theorem CompParab.pSubgroup_le_perfectJoin {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J) {p : ℕ} (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) {A : Subgroup Y} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : A ≤ perfectJoin J :=
  pSubgroup_le_perfectJoin_of_parabolic h.parab h.odd hp hpZ hH hAJ hA

theorem FixPrimeHyp.isCyclic_of_hub {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
    {u : Y} (h : FixPrimeHyp L J p u) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) :
    ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q →
      IsCyclic Q := by
  intro Q hQ hQp
  have hQJ : Q ≤ J := fun x hx => h.fix x (hQ hx).1 (by
    have := Subgroup.mem_centralizer_iff.1 (hQ hx).2 u (Set.mem_singleton u)
    rw [this, mul_inv_cancel_right])
  exact h.cyc (perfectJoin J) (perfectJoin_le J) (perfectJoin_perfect J) Q
    (h.parab.pSubgroup_le_perfectJoin h.prime hpZ hH hQJ hQp) hQp

theorem FixPrimeHyp.torusFree_of_index (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ} {u : Y} (h : FixPrimeHyp L J p u)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1) (ht : IndexTorusFree p d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hH : PerfectJoinHub p (↥L ⧸ Subgroup.center ↥L)) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q →
        IsCyclic Q := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.parab.comp.2.2.1
  have hpZ := ToralCensus.not_dvd_card_center_of_index hGA d hd e h.prime h.five_le ht
  exact ⟨hpZ, h.isCyclic_of_hub hpZ hH⟩

@[expose] def IsLieOfTorusFree (P : TauCeti.LieTypeIndex → Prop) (p : ℕ) (X : Type) [Group X] :
    Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧ IndexTorusFree p d.1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsLieOfTorus (P : TauCeti.LieTypeIndex → Prop) (p : ℕ) (X : Type) [Group X] :
    Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧ ¬ IndexTorusFree p d.1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isLieOf_split {P : TauCeti.LieTypeIndex → Prop} {p : ℕ} {X : Type} [Group X]
    (h : IsLieOf P X) : IsLieOfTorusFree P p X ∨ IsLieOfTorus P p X := by
  obtain ⟨d, hd, he⟩ := h
  by_cases ht : IndexTorusFree p d.1
  · exact Or.inl ⟨d, hd, ht, he⟩
  · exact Or.inr ⟨d, hd, ht, he⟩

@[expose] def FixPrimeATorus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOfTorus IdxA p (↥L ⧸ Subgroup.center ↥L) → PrimeCensusConcl L p u

@[expose] def FixPrimeTwistedATorus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOfTorus IdxTwistedA p (↥L ⧸ Subgroup.center ↥L) →
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q

@[expose] def FixPrimeCycTorusFree (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOfTorusFree P p (↥L ⧸ Subgroup.center ↥L) →
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q

@[expose] def FixPrimeCycTorus (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
    IsLieOfTorus P p (↥L ⧸ Subgroup.center ↥L) →
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q

namespace ToralCensus

theorem classical_index {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD)
    {d : TauCeti.LieTypeIndex} (h : P d) : IsClassicalOrG2Index d ∧ ∀ q, d ≠ .G2 q := by
  rcases hP with rfl | rfl | rfl | rfl | rfl <;> cases d <;>
    simp_all [IdxA, IdxTwistedA, IdxB, IdxD, IdxTwistedD, IsClassicalOrG2Index]

theorem torusFree_of_classical (hGA : CFSG.Open.GriessAllModelsStatement)
    {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD) {Y : Type}
    [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ} {u : Y} (h : FixPrimeHyp L J p u)
    (hX : IsLieOfTorusFree P p (↥L ⧸ Subgroup.center ↥L)) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q →
        IsCyclic Q := by
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  obtain ⟨hd, hG2⟩ := classical_index hP hPd
  exact h.torusFree_of_index hGA d hd ht e
    (perfectJoinHub_of_classicalIndex d hd hG2 e h.prime h.five_le ht)

end ToralCensus

theorem fixPrimeATorusFree (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
      IsLieOfTorusFree IdxA p (↥L ⧸ Subgroup.center ↥L) → PrimeCensusConcl L p u :=
  fun _ _ _ _ _ _ _ h hX =>
    let hc := ToralCensus.torusFree_of_classical hGA (Or.inl rfl) h hX
    ⟨hc.1, Or.inl hc.2⟩

theorem fixPrimeTwistedATorusFree (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (u : Y), FixPrimeHyp L J p u →
      IsLieOfTorusFree IdxTwistedA p (↥L ⧸ Subgroup.center ↥L) →
      ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
        ∀ Q : Subgroup Y, Q ≤ L ⊓ Subgroup.centralizer ({u} : Set Y) → IsPGroup p Q → IsCyclic Q :=
  fun _ _ _ _ _ _ _ h hX => ToralCensus.torusFree_of_classical hGA (Or.inr (Or.inl rfl)) h hX

theorem fixPrimeCycTorusFree_b (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPrimeCycTorusFree IdxB :=
  fun _ _ _ _ _ _ _ h hX =>
    (ToralCensus.torusFree_of_classical hGA (Or.inr (Or.inr (Or.inl rfl))) h hX).2

theorem fixPrimeCycTorusFree_d (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPrimeCycTorusFree IdxD :=
  fun _ _ _ _ _ _ _ h hX =>
    (ToralCensus.torusFree_of_classical hGA (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h hX).2

theorem fixPrimeCycTorusFree_twistedD (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPrimeCycTorusFree IdxTwistedD :=
  fun _ _ _ _ _ _ _ h hX =>
    (ToralCensus.torusFree_of_classical hGA (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h hX).2

theorem fixPrimeCycTorusFree_g2 (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPrimeCycTorusFree IdxG2 := by
  intro Y _ _ L J p u h hX
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  have hd : IsClassicalOrG2Index d.1 := by
    obtain ⟨d, hv⟩ := d
    cases d <;> first | exact hPd | exact hPd.elim
  exact (h.torusFree_of_index hGA d hd ht e
    (perfectJoinHub_of_index d hd e h.prime h.five_le ht)).2

theorem fixPrimeA_of_torus (hGA : CFSG.Open.GriessAllModelsStatement) (hT : FixPrimeATorus) :
    FixPrimeA := by
  intro Y _ _ L J p u h hX
  rcases isLieOf_split (p := p) hX with hX | hX
  · exact fixPrimeATorusFree hGA Y L J p u h hX
  · exact hT Y L J p u h hX

theorem fixPrimeTwistedA_of_torus (hGA : CFSG.Open.GriessAllModelsStatement)
    (hT : FixPrimeTwistedATorus) : FixPrimeTwistedA := by
  intro Y _ _ L J p u h hX
  rcases isLieOf_split (p := p) hX with hX | hX
  · exact fixPrimeTwistedATorusFree hGA Y L J p u h hX
  · exact hT Y L J p u h hX

theorem fixPrimeCyc_of_halves {P : TauCeti.LieTypeIndex → Prop} (hF : FixPrimeCycTorusFree P)
    (hT : FixPrimeCycTorus P) : FixPrimeCyc (IsLieOf P) := by
  intro Y _ _ L J p u h hX
  rcases isLieOf_split (p := p) hX with hX | hX
  · exact hF Y L J p u h hX
  · exact hT Y L J p u h hX

namespace ToralCensus

theorem not_sq_dvd_smallBound {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 2 ^ 10 * 3 ^ 7 * 5 * 7 * 13 := by
  intro h
  have hd : p ∣ 2 ^ 10 * 3 ^ 7 * 5 * 7 * 13 := (dvd_pow_self p two_ne_zero).trans h
  have key : p = 5 ∨ p = 7 ∨ p = 13 := by
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h13
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h7
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h5
        · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h33
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4)
            omega
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h33)
            omega
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h13))
  rcases key with rfl | rfl | rfl <;> norm_num at h

theorem card_statedProj_dvd_card_gl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Nat.card (StatedProj H) ∣ Nat.card (GL ι K) :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card H)

open TauCeti in
theorem card_dvd_of_small {X : Type} [Group X] (hS : IsSmallTwoOrG2 X) :
    Nat.card X ∣ 2 ^ 10 * 3 ^ 6 * 5 * 7 * 13 := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl <;>
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] <;> decide
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := statedClassicalModel_of_typeA hv e
    rw [hp, hf] at hc
    obtain ⟨-, K, hK, hKf, hcard, ⟨e'⟩⟩ := hc
    have := Fintype.ofFinite K
    rw [Nat.card_congr e'.toEquiv]
    refine (card_statedProj_dvd_card_gl _).trans ?_
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hcard]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
    decide
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at hc
    obtain ⟨-, K, hK, hKf, hcard, ⟨e'⟩⟩ := hc
    have := Fintype.ofFinite K
    rw [Nat.card_congr e'.toEquiv]
    refine (card_statedProj_dvd_card_gl _).trans ?_
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hcard]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
    decide

end ToralCensus

theorem fixPrimeCyc_small
    (hGA : CFSG.Open.GriessAllModelsStatement) : FixPrimeCyc IsSmallTwoOrG2 := by
  intro Y _ _ L J p u h hS Q hQ hQp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.parab.comp.2.2.1
  have hZ : Nat.card (Subgroup.center ↥L) ∣ 3 := by
    rcases ToralCensus.card_center_of_small hGA h.parab.odd hS with h1 | ⟨h3, -⟩
    · rw [h1]
      exact one_dvd 3
    · rw [h3]
  have hL : Nat.card ↥L ∣ 2 ^ 10 * 3 ^ 7 * 5 * 7 * 13 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)]
    exact (mul_dvd_mul (ToralCensus.card_dvd_of_small hS) hZ).trans (by norm_num)
  have hQL : Nat.card Q ∣ Nat.card ↥L := Subgroup.card_dvd_of_le (hQ.trans inf_le_left)
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    exact ToralCensus.not_sq_dvd_smallBound hp h.five_le
      ((pow_dvd_pow p (by omega : 2 ≤ k)).trans (hk ▸ hQL.trans hL))
  interval_cases k
  · rw [pow_zero] at hk
    have := Subgroup.card_eq_one.mp hk
    subst this
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

end CFSG.AGLEmbedding
