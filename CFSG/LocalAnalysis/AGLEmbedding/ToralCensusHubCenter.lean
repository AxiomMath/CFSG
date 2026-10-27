module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank

namespace ToralCensus

theorem card_multiplicative_zmod_prod (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem card_center_dvd_multiplierOrders (hGA : CFSG.Open.GriessAllModelsStatement)
    {A X : Type} [Group A] [Group X] [Finite A] [Group.IsPerfect A]
    (e : A ⧸ Subgroup.center A ≃* X)
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f) :
    Nat.card (Subgroup.center A) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨g⟩⟩ := hGA X t n p f hm
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (CFSG.GH74.Generic.centralQuotientMap e) (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    ← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
    Nat.card_congr g.toEquiv, Nat.card_prod, card_multiplicative_zmod_prod,
    card_multiplicative_zmod_prod] at hdvd
  exact hdvd

theorem prime_dvd_genericOrders_fst (hGA : CFSG.Open.GriessAllModelsStatement) {A X : Type}
    [Group A] [Group X] [Finite A] [Group.IsPerfect A] (e : A ⧸ Subgroup.center A ≃* X)
    {t : StatedLieTag} {n f : ℕ} (hm : CFSG.Models.LieModel X t n 2 f) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card (Subgroup.center A)) :
    ℓ ∣ (genericOrders t n 2 f).1 := by
  have h := hdvd.trans (card_center_dvd_multiplierOrders hGA e hm)
  rw [genericOrders_snd_eq_one_of_two t n f hm.1.2.1, mul_one] at h
  rcases (Nat.Prime.dvd_mul hℓ).1 h with h1 | h2
  · exact h1
  · have h16 : ℓ ∣ 2 ^ 4 := h2.trans (exceptionalOrders_mul_dvd_sixteen_of_two t n f)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h16)) hℓ2

theorem odd_two_pow_pred {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  obtain ⟨k, hk⟩ : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  exact ⟨k - 1, by omega⟩

theorem gcd_four_eq_one_of_odd {m : ℕ} (hm : Odd m) : Nat.gcd 4 m = 1 := by
  have h : Nat.Coprime (2 ^ 2) m := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
  simpa using h

theorem genericOrders_fst_eq_one_of_two {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f)
    (ht : t = .PSp ∨ t = .POmegaPlus ∨ (t = .POmegaMinus ∧ 1 ≤ n) ∨ t = .G2) :
    (genericOrders t n 2 f).1 = 1 := by
  have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  rcases ht with rfl | rfl | ⟨rfl, hn⟩ | rfl
  · have h := odd_two_pow_pred hf
    simp only [genericOrders]
    exact Nat.Coprime.symm (Nat.coprime_two_right.2 h)
  · simp [genericOrders, hq]
  · simp only [genericOrders]
    refine gcd_four_eq_one_of_odd ?_
    have : Even ((2 ^ f) ^ n) := (Nat.even_pow' (by omega)).2 hq
    exact this.add_one
  · simp [genericOrders]

theorem false_of_prime_dvd_one {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 1) : False :=
  hℓ.not_dvd_one h

open TauCeti in
theorem prime_dvd_torus_of_dvd_card_center (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] (d : ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : A ⧸ Subgroup.center A ≃* (CFSGIndex.lie d).Group)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card (Subgroup.center A)) :
    (∃ r q, d.1 = .A r q ∧ ℓ ∣ q.card - 1) ∨ (∃ r q, d.1 = .twistedA r q ∧ ℓ ∣ q.card + 1) := by
  obtain ⟨d, hv⟩ := d
  have key : ∀ {t : StatedLieTag} {n f : ℕ},
      CFSG.Models.LieModel (CFSGIndex.lie ⟨d, hv⟩).Group t n 2 f →
        ℓ ∣ (genericOrders t n 2 f).1 :=
    fun hm => prime_dvd_genericOrders_fst hGA e hm hℓ hℓ2 hdvd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have hc := statedClassicalModel_of_typeA hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hd] at hm
    have h := key hm
    simp only [genericOrders] at h
    refine Or.inl ⟨r, q, rfl, ?_⟩
    rw [PrimePower.card_def, hd]
    exact h.trans (Nat.gcd_dvd_right _ _)
  | twistedA r q =>
    change q.p = 2 at hd
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hd] at hm
    have h := key hm
    simp only [genericOrders] at h
    refine Or.inr ⟨r, q, rfl, ?_⟩
    rw [PrimePower.card_def, hd]
    exact h.trans (Nat.gcd_dvd_right _ _)
  | B r q =>
    change q.p = 2 at hd
    exfalso
    rcases (show r = 2 ∨ 3 ≤ r by have : 2 ≤ r := hrange.1; omega) with rfl | hr3
    · have hc :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [hd] at hm
      have h := key hm
      rw [genericOrders_fst_eq_one_of_two hm.1.2.1 (Or.inl rfl)] at h
      exact false_of_prime_dvd_one hℓ h
    · have hc := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd hr3
        (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [hd] at hm
      have h := key hm
      rw [genericOrders_fst_eq_one_of_two hm.1.2.1 (Or.inl rfl)] at h
      exact false_of_prime_dvd_one hℓ h
  | D r q =>
    change q.p = 2 at hd
    exfalso
    have hc := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hd] at hm
    have h := key hm
    rw [genericOrders_fst_eq_one_of_two hm.1.2.1 (Or.inr (Or.inl rfl))] at h
    exact false_of_prime_dvd_one hℓ h
  | twistedD r q =>
    change q.p = 2 at hd
    exfalso
    have hc := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
      (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hd] at hm
    have h := key hm
    rw [genericOrders_fst_eq_one_of_two hm.1.2.1
      (Or.inr (Or.inr (Or.inl ⟨rfl, by have : 4 ≤ r := hrange; omega⟩)))] at h
    exact false_of_prime_dvd_one hℓ h
  | G2 q =>
    change q.p = 2 at hd
    exfalso
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    have hm : CFSG.Models.LieModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩,
        Or.inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
    rw [hd] at hm
    have h := key hm
    rw [genericOrders_fst_eq_one_of_two hm.1.2.1 (Or.inr (Or.inr (Or.inr rfl)))] at h
    exact false_of_prime_dvd_one hℓ h
  | _ => exact hd.elim

theorem card_add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by rw [← Nat.sq_sub_sq q 1, one_pow]⟩

theorem not_dvd_card_center_of_index (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1)
    (e : A ⧸ Subgroup.center A ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ht : IndexTorusFree p d.1) : ¬ p ∣ Nat.card (Subgroup.center A) := by
  intro hdvd
  rcases prime_dvd_torus_of_dvd_card_center hGA d hd e hp (by omega) hdvd with
    ⟨r, q, hdq, h⟩ | ⟨r, q, hdq, h⟩
  · rw [hdq] at ht
    rcases ht with h2 | h1
    · rw [h2] at h
      exact false_of_prime_dvd_one hp h
    · exact h1 h
  · rw [hdq] at ht
    rcases ht with h2 | h1
    · rw [h2] at h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · exact h1 (h.trans (card_add_one_dvd_sq_sub_one _))

theorem card_center_eq_one_of_index (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (hA : ∀ r q, d.1 ≠ .A r q)
    (h2A : ∀ r q, d.1 ≠ .twistedA r q)
    (e : A ⧸ Subgroup.center A ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : Odd (Nat.card (Subgroup.center A))) : Nat.card (Subgroup.center A) = 1 := by
  by_contra h1
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd h1
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hℓd)
  rcases prime_dvd_torus_of_dvd_card_center hGA d hd e hℓ hℓ2 hℓd with ⟨r, q, h, -⟩ | ⟨r, q, h, -⟩
  · exact hA r q h
  · exact h2A r q h

theorem rest_index {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD ∨ P = IdxG2) {d : TauCeti.LieTypeIndex}
    (h : P d) : IsClassicalOrG2Index d ∧ (∀ r q, d ≠ .A r q) ∧ (∀ r q, d ≠ .twistedA r q) := by
  rcases hP with rfl | rfl | rfl | rfl <;> cases d <;>
    simp_all [IdxB, IdxD, IdxTwistedD, IdxG2, IsClassicalOrG2Index]

theorem eq_one_of_odd_of_dvd_two {z : ℕ} (hodd : Odd z) (h : z ∣ 2) : z = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

open TauCeti in
theorem card_center_of_small
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A]
    [Group.IsPerfect A] (hodd : Odd (Nat.card (Subgroup.center A)))
    (hS : IsSmallTwoOrG2 (A ⧸ Subgroup.center A)) :
    Nat.card (Subgroup.center A) = 1 ∨ (Nat.card (Subgroup.center A) = 3 ∧
      Nonempty (A ⧸ Subgroup.center A ≃* alternatingGroup (Fin 6))) := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · have hn5 : 5 ≤ n := by omega
    have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
      (CFSG.GH74.Generic.centralQuotientMap e)
      (CFSG.GH74.Generic.centralQuotientMap_surjective e)
      (CFSG.GH74.Generic.centralQuotientMap_ker e).le
    rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
      (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn5).2] at hdvd
    rcases hn with rfl | rfl | rfl
    · rw [ite_eq_right (by decide)] at hdvd
      exact Or.inl (eq_one_of_odd_of_dvd_two hodd hdvd)
    · rw [ite_eq_left (by decide)] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hpos := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      generalize Nat.card (Subgroup.center A) = z at hdvd hodd hle hpos ⊢
      interval_cases z
      · exact Or.inl rfl
      · exact absurd hodd (by decide)
      · exact Or.inr ⟨rfl, ⟨e⟩⟩
      · exact absurd hdvd (by decide)
      · exact absurd hdvd (by decide)
      · exact absurd hodd (by decide)
    · rw [ite_eq_right (by decide)] at hdvd
      exact Or.inl (eq_one_of_odd_of_dvd_two hodd hdvd)
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := statedClassicalModel_of_typeA hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hp, hf] at hm
    have h := card_center_dvd_multiplierOrders hGA e hm
    simp only [genericOrders, exceptionalOrders] at h
    exact Or.inl (eq_one_of_odd_of_dvd_two hodd (by simpa using h))
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
    rw [hp, hf] at hm
    have h := card_center_dvd_multiplierOrders hGA e hm
    simp only [genericOrders, exceptionalOrders] at h
    exact Or.inl (Nat.dvd_one.1 (by simpa using h))

end ToralCensus

theorem oddCenterRest_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) : OddCenterRest := by
  intro Y _ _ L hL hodd hR
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hlie : ∀ {P : TauCeti.LieTypeIndex → Prop},
      (P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD ∨ P = IdxG2) →
      IsLieOf P (↥L ⧸ Subgroup.center ↥L) → Nat.card (Subgroup.center ↥L) = 1 := by
    rintro P hP ⟨d, hPd, ⟨e⟩⟩
    obtain ⟨hd, hA, h2A⟩ := ToralCensus.rest_index hP hPd
    exact ToralCensus.card_center_eq_one_of_index hGA d hd hA h2A e hodd
  rcases hR with h | h | h | h | hS
  · exact Or.inl (hlie (Or.inl rfl) h)
  · exact Or.inl (hlie (Or.inr (Or.inl rfl)) h)
  · exact Or.inl (hlie (Or.inr (Or.inr (Or.inl rfl))) h)
  · exact Or.inl (hlie (Or.inr (Or.inr (Or.inr rfl))) h)
  · exact ToralCensus.card_center_of_small hGA hodd hS

end CFSG.AGLEmbedding
