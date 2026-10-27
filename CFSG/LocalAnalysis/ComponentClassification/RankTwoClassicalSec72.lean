module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Facts
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoChar2C0Basic

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tightlyEmbedded_subgroupOf_of_ti {T X : Subgroup G} (hTX : T ≤ X)
    (heven : Even (Nat.card T))
    (hti : ∀ x ∈ X, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T) :
    TightlyEmbedded (T.subgroupOf X) := by
  have hcard : Nat.card (T.subgroupOf X) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv
  refine ⟨hcard ▸ heven, fun x hx => ?_⟩
  have hx' : (x : G) ∉ normalizer (T : Set G) := by
    intro h
    apply hx
    rw [← subgroupOf_normalizer_eq hTX]
    exact h
  have heq : (T.subgroupOf X ⊓ rightConjugate (T.subgroupOf X) x : Subgroup X) =
      (T ⊓ rightConjugate T (x : G)).subgroupOf X := by
    ext y
    simp only [mem_inf, mem_subgroupOf, mem_rightConjugate_iff, coe_mul, coe_inv]
  have hbot : T ⊓ rightConjugate T (x : G) = ⊥ := by
    by_contra hne
    exact hx' ((rightConjugate_eq_self_iff T (x : G)).mp (hti x x.2 hne))
  rw [heq, hbot, Subgroup.bot_subgroupOf, card_bot]
  exact odd_one

section CharTwo

variable {K : Type} [Field K]

theorem charP_two_of_card [Finite K] {k : ℕ} (hK : Nat.card K = 2 ^ k) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem units_eq_one_of_sq_eq_one [CharP K 2] {u : Kˣ} (h : u ^ 2 = 1) : u = 1 := by
  apply Units.ext
  have h2 : (u : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have h1 : ((u : K) - 1) ^ 2 = 0 := by
    have : ((u : K) - 1) ^ 2 = (u : K) ^ 2 - 2 * (u : K) + 1 := by ring
    rw [this, h2, CharTwo.two_eq_zero, zero_mul, sub_zero, CharTwo.add_self_eq_zero]
  simpa [sub_eq_zero] using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1

theorem odd_orderOf_units [Finite K] [CharP K 2] (u : Kˣ) : Odd (orderOf u) := by
  rcases Nat.even_or_odd (orderOf u) with ⟨j, hj⟩ | h
  · exfalso
    have hpos : 0 < orderOf u := orderOf_pos u
    have h1 : (u ^ j) ^ 2 = 1 := by
      rw [← pow_mul, show j * 2 = orderOf u by omega, pow_orderOf_eq_one]
    have h3 := orderOf_le_of_pow_eq_one (by omega : 0 < j) (units_eq_one_of_sq_eq_one h1)
    omega
  · exact h

end CharTwo

section Represents

variable {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)}

omit [Finite G] in
theorem Represents.eq_of_orderOf_eq_two [CharP K 2]
    {e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H} {x : G} {M M' : GL ι K}
    (hM : Represents e x M) (hM' : Represents e x M') (h2 : orderOf M = 2)
    (h2' : orderOf M' = 2) : M = M' := by
  obtain ⟨hx, hMH, he⟩ := hM
  obtain ⟨hx', hMH', he'⟩ := hM'
  have hq : (QuotientGroup.mk ⟨M, hMH⟩ : Assembly.LowTwoRank.StatedProj H) =
      QuotientGroup.mk ⟨M', hMH'⟩ :=
    he.symm.trans he'
  rw [QuotientGroup.eq, mem_subgroupOf] at hq
  obtain ⟨c, hc⟩ := hq
  have hM'eq : M' = M * Matrix.GeneralLinearGroup.scalar ι c := by
    have h : ((⟨M, hMH⟩⁻¹ * ⟨M', hMH'⟩ : ↥H) : GL ι K) = M⁻¹ * M' := rfl
    rw [h] at hc
    rw [hc]
    group
  have hne : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    have hM1 : M = 1 := Units.ext (Subsingleton.elim _ _)
    rw [hM1, orderOf_one] at h2
    omega
  have hM2 : M ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one M
  have hM'2 : M' ^ 2 = 1 := by rw [← h2']; exact pow_orderOf_eq_one M'
  have hcomm : Commute M (Matrix.GeneralLinearGroup.scalar ι c) :=
    (Matrix.GeneralLinearGroup.scalar_commute c M).symm
  rw [hM'eq, hcomm.mul_pow, hM2, one_mul, ← map_pow] at hM'2
  have hc2 : c ^ 2 = 1 := by
    apply Units.ext
    have h := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hM'2
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h
    have h' : Matrix.scalar ι ((c ^ 2 : Kˣ) : K) = Matrix.scalar ι (1 : K) := by
      rw [h]; exact (Matrix.scalar_apply (1 : K)).trans Matrix.diagonal_one |>.symm
    rw [Matrix.scalar_inj] at h'
    simpa using h'
  rw [hM'eq, units_eq_one_of_sq_eq_one hc2, map_one, mul_one]

omit [Finite G] in
theorem exists_represents_orderOf_eq_two [Finite K] [CharP K 2]
    (e : rankTwoQuot A ≃* Assembly.LowTwoRank.StatedProj H) {x : G} (hx : x ∈ A)
    (hx2 : x ^ 2 = 1) (hxZ : (⟨x, hx⟩ : ↥A) ∉ center ↥A) :
    ∃ M : GL ι K, Represents e x M ∧ orderOf M = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk ⟨x, hx⟩))
  have hS : N ^ 2 ∈ (Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hN, ← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    rw [this, QuotientGroup.mk_one, map_one]
  have hS' := hS
  rw [mem_subgroupOf] at hS'
  obtain ⟨c, hc⟩ := hS'
  obtain ⟨k, hk⟩ := odd_orderOf_units c
  have hpow : (N ^ 2) ^ (2 * k + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, ← hk, pow_orderOf_eq_one, map_one, Subgroup.coe_one]
  set N' : ↥H := (N ^ (2 * k + 1))⁻¹ with hN'
  have hN'2 : N' ^ 2 = 1 := by
    rw [hN', inv_pow, ← pow_mul, show (2 * k + 1) * 2 = 2 * (2 * k + 1) by ring, pow_mul, hpow,
      inv_one]
  have hmk : (QuotientGroup.mk N : Assembly.LowTwoRank.StatedProj H) = QuotientGroup.mk N' := by
    rw [QuotientGroup.eq]
    have h : N⁻¹ * N' = ((N ^ 2) ^ (k + 1))⁻¹ := by
      rw [hN', ← pow_mul, ← mul_inv_rev, ← pow_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    rw [h]
    exact inv_mem (pow_mem hS _)
  have hN'1 : N' ≠ 1 := by
    intro h1
    apply hxZ
    rw [← QuotientGroup.eq_one_iff]
    apply e.injective
    rw [← hN, hmk, h1, QuotientGroup.mk_one, map_one]
  refine ⟨(N' : GL ι K), ⟨hx, N'.2, hN.symm.trans hmk⟩, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime hN'2 hN'1

end Represents

section Classes

variable {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_letterHolds (ℓ : ℕ) (φ : (ι → K) → K) : ∃ L : Letter, LetterHolds L ℓ φ := by
  rcases Nat.even_or_odd ℓ with hℓ | hℓ
  · by_cases h : ∀ v, φ v = 0
    · exact ⟨.a, hℓ, h⟩
    · push Not at h
      exact ⟨.c, hℓ, h⟩
  · exact ⟨.b, hℓ⟩

omit [Finite G] in
theorem not_mem_center_of_orderOf_eq_two (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp : p ∈ A)
    (hp2 : orderOf p = 2) : (⟨p, hp⟩ : ↥A) ∉ center ↥A := by
  intro hpZ
  have hdvd := Subgroup.orderOf_dvd_natCard (center ↥A) hpZ
  rw [Subgroup.orderOf_mk, hp2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hdvd)

namespace ClassicalModel

omit [Finite G] in
theorem suzukiType_of_isPrimary (D : ClassicalModel A) {p : G} (hp : D.IsPrimary p) {L : Letter}
    {ℓ : ℕ} (hL : D.SuzukiType p L ℓ) : (L = .b ∧ ℓ = 1) ∨ (L = .a ∧ ℓ = 2) := by
  cases D with
  | linear => exact hL.elim
  | unitary => exact hL.elim
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, hr⟩ := hp
    obtain ⟨-, M', hM', hM'2, hr', hlet⟩ := hL
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    obtain rfl : ℓ = 1 := hr'.symm.trans hr
    cases L with
    | a => exact (Nat.not_even_one hlet.1).elim
    | b => exact Or.inl ⟨rfl, rfl⟩
    | c => exact (Nat.not_even_one hlet.1).elim
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, hr, hQ⟩ := hp
    obtain ⟨-, M', hM', hM'2, hr', hlet⟩ := hL
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    obtain rfl : ℓ = 2 := hr'.symm.trans hr
    cases L with
    | a => exact Or.inr ⟨rfl, rfl⟩
    | b => exact absurd (show Odd 2 from hlet) (by decide)
    | c =>
      obtain ⟨-, v, hv⟩ := hlet
      exact absurd (hQ v) hv
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, hr, hQ⟩ := hp
    obtain ⟨-, M', hM', hM'2, hr', hlet⟩ := hL
    obtain rfl := hM.eq_of_orderOf_eq_two hM' hM2 hM'2
    obtain rfl : ℓ = 2 := hr'.symm.trans hr
    cases L with
    | a => exact Or.inr ⟨rfl, rfl⟩
    | b => exact absurd (show Odd 2 from hlet) (by decide)
    | c =>
      obtain ⟨-, v, hv⟩ := hlet
      exact absurd (hQ v) hv

omit [Finite G] in
theorem not_case23_of_isPrimary (D : ClassicalModel A) {p : G} (hp : D.IsPrimary p) :
    ¬ Case23 D p := by
  rintro ⟨ℓ, a, b, (⟨hℓ, hpb, -⟩ | ⟨hpc, -⟩), -⟩
  · rcases D.suzukiType_of_isPrimary hp hpb with ⟨-, rfl⟩ | ⟨h, -⟩
    · omega
    · cases h
  · rcases D.suzukiType_of_isPrimary hp hpc with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

omit [Finite G] in
theorem not_case4_of_isPrimary (D : ClassicalModel A) {p : G} (hp : D.IsPrimary p) :
    ¬ Case4 D p := by
  rintro ⟨⟨ℓ, hpc⟩, -⟩
  rcases D.suzukiType_of_isPrimary hp hpc with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

end ClassicalModel

theorem ClassicalJSylow.jSylowAt (h : ClassicalJSylow) (D : ClassicalModel A)
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hq : 4 ≤ D.q) {p : G}
    (hp : p ∈ A) (hp2 : orderOf p = 2) : JSylowAt A p := by
  obtain ⟨hL, hU, hS, hP, hM⟩ := h
  have hpZ := not_mem_center_of_orderOf_eq_two hZ hp hp2
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact hL G A (.linear n m hn hm hnm K hK e) rfl hA hZ hq p _ ⟨hp2, M, hM', hM2, rfl⟩
  | unitary n m hn hm K hK e =>
    have := charP_two_of_card (k := 2 * m) (by rw [hK, ← pow_mul, mul_comm])
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact hU G A (.unitary n m hn hm K hK e) rfl hA hZ hq p _ ⟨hp2, M, hM', hM2, rfl⟩
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M)
      (fun v => sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v))
    exact hS L G A (.symplectic n m hn hm hnm K hK e) rfl hA hZ hq p _
      ⟨hp2, M, hM', hM2, rfl, hLM⟩
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadPlus n K
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v)
    exact hP L G A (.orthPlus n m hn hm K hK e) rfl hA hZ hq p _ ⟨hp2, M, hM', hM2, rfl, hLM⟩
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadMinus n K b c
        (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          K) - 1) *ᵥ v)
    exact hM L G A (.orthMinus n m hn hm K hK b c hbc e) rfl hA hZ hq p _
      ⟨hp2, M, hM', hM2, rfl, hLM⟩

end Classes

section JGroup

variable {A : Subgroup G}

omit [Finite G] in
theorem jGroup_le (A : Subgroup G) (p : G) : jGroup A p ≤ A ⊓ centralizer ({p} : Set G) :=
  inf_le_left.trans (CFSG.ABGTheoremB.pCoreIn_le 2 _)

omit [Finite G] in
theorem conjCommuting_conj {p a x : G} (ha : a ∈ A ⊓ centralizer ({p} : Set G))
    (hx : x ∈ conjCommuting A p) : a * x * a⁻¹ ∈ conjCommuting A p := by
  obtain ⟨b, hb, rfl, hbp⟩ := hx
  obtain ⟨haA, hap⟩ := mem_inf.mp ha
  have hap' : Commute a p := mem_centralizer_singleton_iff.mp hap
  exact ⟨a * b, mul_mem haA hb, by group, (hap'.mul_left hbp).mul_left hap'.inv_left⟩

omit [Finite G] in
theorem mem_normalizer_centralizer_of {S : Set G} {a : G} (h1 : ∀ x ∈ S, a * x * a⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, a⁻¹ * x * a ∈ S) : a ∈ normalizer (centralizer S : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  simp only [mem_centralizer_iff]
  constructor
  · intro hh s hs
    have := hh _ (h2 s hs)
    calc s * (a * h * a⁻¹) = a * ((a⁻¹ * s * a) * h) * a⁻¹ := by group
      _ = a * (h * (a⁻¹ * s * a)) * a⁻¹ := by rw [this]
      _ = a * h * a⁻¹ * s := by group
  · intro hh s hs
    have := hh _ (h1 s hs)
    calc s * h = a⁻¹ * ((a * s * a⁻¹) * (a * h * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * h * a⁻¹) * (a * s * a⁻¹)) * a := by rw [this]
      _ = h * s := by group

omit [Finite G] in
theorem le_normalizer_jGroup (A : Subgroup G) (p : G) :
    A ⊓ centralizer ({p} : Set G) ≤ normalizer (jGroup A p : Set G) := by
  intro a ha
  refine mem_normalizer_inf (CFSG.ABGTheoremB.le_normalizer_map_subtype
    (A ⊓ centralizer ({p} : Set G)) (CFSG.pCore 2 _) ha) ?_
  refine mem_normalizer_centralizer_of (fun x hx => conjCommuting_conj ha hx) fun x hx => ?_
  have h := conjCommuting_conj (inv_mem ha) hx
  rwa [inv_inv] at h

omit [Finite G] in
theorem RegularOn.centralizer_le {J : Subgroup G} {S : Set G} {p : G} (h : RegularOn A J S)
    (hp : p ∈ S) (hN : A ⊓ centralizer ({p} : Set G) ≤ normalizer (J : Set G)) :
    A ⊓ centralizer ({p} : Set G) ≤ centralizer (J : Set G) := by
  intro a ha
  refine h.2 a (mem_inf.mpr ⟨(mem_inf.mp ha).1, hN ha⟩) p hp ?_
  rw [mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2, mul_inv_cancel_right]

end JGroup

omit [Finite G] in
theorem Conclusion222.mono {A T : Subgroup G} {q : ℕ} {I I' II II' : G → Prop}
    (h : Conclusion222 A T q I II) (hI : ∀ p, I p → I' p) (hII : ∀ t, II t → II' t) :
    Conclusion222 A T q I' II' := by
  obtain ⟨hZ, hfus, h⟩ := h
  refine ⟨hZ, hfus, fun t ht ht1 p hp => ?_⟩
  rcases h t ht ht1 p hp with ⟨h1, h2, h3⟩ | h4
  · exact Or.inl ⟨h1, h2, hI p h3⟩
  · exact Or.inr (hII t h4)

omit [Finite G] in
theorem CaseI.case1234 {A : Subgroup G} {D : ClassicalModel A} {p : G} (h : CaseI D p) :
    Case1 D p ∨ Case23 D p ∨ Case4 D p := by
  revert h
  unfold CaseI
  cases D.family with
  | linear => exact Or.inl
  | unitary => exact Or.inl
  | symplectic => exact fun h => h.elim Or.inl fun h => Or.inr (Or.inl h)
  | orthPlus => exact fun h => h.elim Or.inl fun h => Or.inr (Or.inr h)
  | orthMinus => exact fun h => h.elim Or.inl fun h => Or.inr (Or.inr h)

theorem Classical222Large.conclusion (h : Classical222Large) {A T : Subgroup G}
    (D : ClassicalModel A) (hq : 4 ≤ D.q) (hH : Hyp221 A T) :
    Conclusion222 A T D.q (fun p => Case1 D p ∨ Case23 D p ∨ Case4 D p) fun _ => CaseII D T :=
  (h G A T D hq hH).mono (fun _ hp => hp.case1234) fun _ h => h.elim


namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem inf_centralizer_singleton_eq {t p : G} (hρ : t⁻¹ * p ∈ R) :
    A ⊓ centralizer ({t} : Set G) = A ⊓ centralizer ({p} : Set G) := by
  ext a
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun ha => ?_
  have hc' : Commute a (t⁻¹ * p) := hc.commute_of_mem ha hρ
  have hp : p = t * (t⁻¹ * p) := by group
  constructor
  · intro h
    have h1 : Commute a t := h
    have h2 := h1.mul_right hc'
    rw [← hp] at h2
    exact h2
  · intro h
    have h1 : Commute a p := h
    have h2 := h1.mul_right hc'.inv_right
    rw [show p * (t⁻¹ * p)⁻¹ = t by group] at h2
    exact h2

theorem aPart_ne_one {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hρ : t⁻¹ * p ∈ R) : p ≠ 1 := by
  rintro rfl
  have htR : t ∈ R := by simpa using inv_mem hρ
  have : t ∈ R ⊓ T := mem_inf.mpr ⟨htR, ht⟩
  rw [hc.inf_eq_bot, mem_bot] at this
  exact ht1 this

theorem aParts_of {J : Subgroup G} {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) (hle : ∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ J)
    (hcen : A ⊓ centralizer ({p} : Set G) ≤ centralizer (J : Set G)) : AParts A R T p J :=
  ⟨hp, hc.aPart_ne_one ht ht1 hρ, ⟨t, ht, hρ⟩, hle, hcen⟩

theorem jData_of {t p : G} {n : ℕ} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R)
    (hle : ∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p)
    (hreg : RegularOn A (jGroup A p) (nonidentity (jGroup A p)))
    (hcyc : AutCyclic A (jGroup A p) n) (hsyl : JSylowAt A p) :
    ∃ y : G, JData A R T p (jGroup A p) y := by
  obtain ⟨-, y, hy, hyo, hyc⟩ := hcyc
  refine ⟨y, ⟨(jGroup_le A p).trans inf_le_left, hle t ht p hp hρ, hc.aPart_ne_one ht ht1 hρ,
    ⟨t, ht, hρ⟩, hle, ?_, le_normalizer_jGroup A p, fun j hj hj1 j' hj' hj'1 =>
      hreg.1 j ⟨hj, hj1⟩ j' ⟨hj', hj'1⟩, fun a ha j hj hj1 haj => hreg.2 a ha j ⟨hj, hj1⟩ haj,
    hy, hyo, hyc, ?_⟩⟩
  · intro b hb hbp
    exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr ⟨b, hb, rfl, hbp⟩))
  · intro x hx hxc hx2
    have hx' : x ∈ centralizer (conjCommuting A p) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl, hbp⟩
      exact (mem_centralizer_singleton_iff.mp (hxc b hb hbp)).symm
    exact mem_inf.mpr ⟨hsyl x hx hx' hx2, hx'⟩

variable (h32 : Lemma32)
include h32

theorem isAPart {t p : G} (ht : t ∈ T) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) : IsAPart A t p := by
  refine ⟨hp, ⟨1, ?_⟩, hc.sylowR.le hρ⟩
  have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hρ
  rw [pow_one, show p = t * (t⁻¹ * p) by group, hcomm.mul_pow, (hc.elemT h32).2 t ht,
    (hc.elemR h32).2 _ hρ, one_mul]

theorem center_le_centralizer (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    (center A).map A.subtype ≤ centralizer (T : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  intro t ht
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart h32 h4 h34 ht
  have h1 : Commute (z : G) p := by
    have := mem_center_iff.mp hz ⟨p, hp⟩
    exact (congrArg Subtype.val this).symm
  have h2 : Commute (z : G) (t⁻¹ * p)⁻¹ := (hc.commute_of_mem z.2 hρ).inv_right
  have h3 := h1.mul_right h2
  rw [show p * (t⁻¹ * p)⁻¹ = t by group] at h3
  exact h3.eq.symm

theorem generalizedFitting_le (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hF : ClassicalCentralizerCharTwo) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) :
    ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype := by
  intro t ht ht1
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart h32 h4 h34 ht
  rw [hc.inf_centralizer_singleton_eq hρ]
  refine (RankTwoChar2C0.generalizedFitting_centralizer_of_isCharacteristicP hp
    (hF (rankTwoQuot A) hTy _ ?_)).1
  have hp2 : p ^ 2 = 1 := by
    have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hρ
    rw [show p = t * (t⁻¹ * p) by group, hcomm.mul_pow, (hc.elemT h32).2 t ht,
      (hc.elemR h32).2 _ hρ, one_mul]
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow]
    have : (⟨p, hp⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
    rw [this, QuotientGroup.mk_one]
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hpK : p ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp h1 ⟨a, ha⟩)
    have htK : t ∈ centralizer (A : Set G) := by
      have : t = p * (t⁻¹ * p)⁻¹ := by group
      rw [this]
      exact mul_mem hpK (inv_mem (hc.sylowR.le hρ))
    have hbot := two_subgroup_inf_conjugate_eq_bot _ T
      (tightlyEmbedded_centralizer hc.hyp.standard) hc.sylowT.isPGroup g
      (by rw [normalizer_centralizer_eq hc.hyp.standard]; exact hc.not_mem) hc.sylowT.le
    have : t ∈ T ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨ht, htK⟩
    rw [hbot, mem_bot] at this
    exact ht1 this

theorem hyp221 (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hF : ClassicalCentralizerCharTwo) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) :
    Hyp221 A T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm := Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp hc.not_mem hc.sylowT hc.le_normalizer
    hOut
  have hti := lemma26_of_isAdmissible hadm (hc.center_le_centralizer h32 h4 h34)
    (hc.generalizedFitting_le h32 h4 h34 hF hTy)
  refine ⟨hc.hyp.standard.1, hc.le_normalizer, hc.le_sup_centralizer h32 h4 h34, ?_,
    hadm.1.2.2.2, hadm.1.1, hadm.1.2.1, ?_, ?_⟩
  ·
    rintro c hc' ⟨k, hk⟩
    have hcK : c ∈ centralizer (A : Set G) := (mem_inf.mp hc').2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hp : IsPGroup 2 ↥(zpowers c) := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    obtain ⟨S, hS, hcS⟩ := exists_isSylowOf_le (zpowers_le.mpr hcK) hp
    exact (h32 G A hc.hyp S hS).2 c (hcS (mem_zpowers c))
  ·
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hc.sylowT.isPGroup
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := hadm.1.2.1
      rw [hn, pow_zero] at this
      omega
    exact tightlyEmbedded_subgroupOf_of_ti le_sup_left
      (by rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, hn0⟩)) hti
  ·
    rcases hadm.2.2.1 with h4' | hadm'
    · exact Or.inl h4'
    · right
      intro x hx y hy
      obtain ⟨hyT, hyN⟩ := mem_inf.mp hy
      have hx' : x ∈ ((T ⊔ A : Subgroup G) : Set G) := hx
      rw [coe_mul_of_left_le_normalizer_right T A hc.le_normalizer] at hx'
      obtain ⟨t', ht', a, ha, rfl⟩ := hx'
      have hTa : rightConjugate T (t' * a) = rightConjugate T a := by
        rw [← rightConjugate_mul,
          (rightConjugate_eq_self_iff T t').mpr (Subgroup.le_normalizer ht')]
      rw [hTa, mem_rightConjugate_iff] at hyT
      have h1 : a * y * a⁻¹ ∈ T ⊓ normalizer (rightConjugate T a⁻¹ : Set G) := by
        refine mem_inf.mpr ⟨hyT, ?_⟩
        rw [mem_normalizer_rightConjugate_iff]
        simpa [mul_assoc] using hyN
      have h2 := hadm' a⁻¹ (inv_mem ha) h1
      rw [centralizer_rightConjugate, mem_rightConjugate_iff] at h2
      simpa [mul_assoc] using h2

theorem case222 (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hF : ClassicalCentralizerCharTwo) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (h222 : Classical222Large) (D : ClassicalModel A) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) :
    ((∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p) ∧ Nat.card T ≤ D.q ∧
      (Case1 D p ∨ Case23 D p ∨ Case4 D p)) ∨ CaseII D T := by
  obtain ⟨-, -, h⟩ := h222.conclusion D hq (hc.hyp221 h32 h4 h34 h2 hOut hF hTy)
  rcases h t ht ht1 p (hc.isAPart h32 ht hp hρ) with ⟨hle, hT, hI⟩ | hII
  · exact Or.inl ⟨fun t' ht' p' hp' hρ' => hle t' ht' p' (hc.isAPart h32 ht' hp' hρ'), hT, hI⟩
  · exact Or.inr hII

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
