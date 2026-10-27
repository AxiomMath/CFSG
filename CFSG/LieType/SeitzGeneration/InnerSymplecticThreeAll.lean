module

public import CFSG.LieType.SeitzGeneration.ClassicalThreeLeaves
public import CFSG.LieType.SeitzGeneration.SpPlaneThree

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull (coprime_card_ker_proj)

@[expose] def SpPlaneThreeF2Gen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ (r : ℕ), 5 ≤ r →
    ∀ E : Subgroup (StatedSp r K), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤

theorem three_ne_zero_of_card_prime_pow {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : f ≠ 0) (hK : Nat.card K = ℓ ^ f) : (3 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  intro h3
  have h3' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h3
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
    ((CharP.cast_eq_zero_iff K p 3).1 h3')
  subst hp3
  have h1 : ℓ ∣ 3 ^ (n : ℕ) := by
    rw [← hcard]
    exact dvd_pow_self ℓ hf
  exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow h1))

theorem exists_ne_zero_ne_one_of_card_three_le {K : Type} [Field K] [Finite K]
    (h : 3 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra! hc
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := by
    intro s
    by_cases hs : s = 0
    · exact ⟨false, by simp [hs]⟩
    · exact ⟨true, by simp [hc s hs]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [show Nat.card Bool = 2 by simp] at hle
  omega

theorem planeGen_inner_sp_model_three (hF2 : SpPlaneThreeF2Gen) {d : TauCeti.ValidLieTypeIndex}
    {K : Type} [Field K] [Finite K] {r ℓ f : ℕ}
    (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) (hrq : ¬ (ℓ ^ f = 2 ∧ (r = 3 ∨ r = 4)))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hinner : InnerPlane d 3 E) : PlaneGen E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKge : 2 ≤ Nat.card K := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    omega
  have hne3 : Nat.card K ≠ 3 := by
    intro h
    have h1 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ hf
    rw [← hK, h] at h1
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h1)
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_card_prime_pow hℓ hℓ3 hf hK
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega) (by
      by_cases h4 : 4 ≤ Nat.card K
      · exact Or.inl (Or.inr h4)
      · have h2 : Nat.card K = 2 := by omega
        exact Or.inr (Or.inr ⟨h2, hr⟩))
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner Nat.prime_three hc hinner)
  refine planeGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hcomm₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    haveI := hE₁.1
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E₁) ⟨y, hy⟩)
  refine CFSG.RankThree.PartOne.CTP.closure_centralizers_of_lift (proj r K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r) (K := K))
    ?_ E₁ hcomm₁ (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := r) (K := K) (by omega) Nat.prime_three (by norm_num)
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl 3))
  · intro E' hc' he' hcd' _
    have hcard9 : Nat.card E' = 9 := hcd'.trans (hcard₁.trans (by norm_num))
    rcases (by omega : Nat.card K = 2 ∨ 4 ≤ Nat.card K) with h2 | h4
    · have hr5 : 5 ≤ r := by
        by_contra h5
        exact hrq ⟨by rw [← hK]; exact h2, by omega⟩
      exact hF2 K h2 r hr5 E' hc' he' hcard9
    · exact closure_centralizers_spPlane_three h3K
        (exists_ne_zero_ne_one_of_card_three_le (by omega)) (by omega) hc' he' hcard9

theorem seitzInnerThreeSymplecticHigh_of_F2 (hF2 : SpPlaneThreeF2Gen) :
    SeitzInnerThreeSymplecticHigh := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, hsp⟩
  subst hp3
  rcases hsp with ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    have hq : 3 ≠ q.p := by simpa using hpd
    have hrq : ¬ (q.p ^ q.exponent = 2 ∧ (r = 3 ∨ r = 4)) := by
      rintro ⟨h2, hr34⟩
      have h2' : q.p ^ q.exponent = q.p ^ 1 := by rw [h2, hq2, pow_one]
      have he1 : q.exponent = 1 := Nat.pow_right_injective q.prime_p.two_le h2'
      have hB : TauCeti.LieTypeIndex.B r q = TauCeti.LieTypeIndex.B 3 q ∨
          TauCeti.LieTypeIndex.B r q = TauCeti.LieTypeIndex.B 4 q := by
        rcases hr34 with h | h <;> subst h <;> simp
      exact hex (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq2, he1, hB⟩)))⟩)
    haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      Nat.finite_of_card_ne_zero (by
        rw [CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv]
        exact pow_ne_zero _ q.prime_p.ne_zero)
    exact planeGen_inner_sp_model_three hF2 (d := ⟨.B r q, hv⟩)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p hq.symm (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hr3 hrq hE hc hinner
  ·
    have hq : 3 ≠ q.p := by simpa using hpd
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr3 : 3 ≤ r := hrange.1
    have hq2 : q.p ≠ 2 := hrange.2
    have hrq : ¬ (q.p ^ q.exponent = 2 ∧ (r = 3 ∨ r = 4)) := by
      rintro ⟨h2, -⟩
      have hdvd : q.p ∣ 2 := by
        rw [← h2]
        exact dvd_pow_self _ q.exponent_pos.ne'
      exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd)
    haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) :=
      Nat.finite_of_card_ne_zero (by
        rw [card_fixedField_C r q hv]
        exact pow_ne_zero _ q.prime_p.ne_zero)
    exact planeGen_inner_sp_model_three hF2 (d := ⟨.C r q, hv⟩)
      (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p hq.symm (card_fixedField_C r q hv) hr3 hrq hE hc hinner

end CFSG.LieType.SeitzGeneration
