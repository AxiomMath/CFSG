module

public import CFSG.LieType.SeitzGeneration.OuterSUPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Sec66T (center_eq_bot_of_simple')

section Plane

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem card_inf_innU_eq_prime (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hAel : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hAnot : ¬ A ≤ innU h n) :
    Nat.card (A ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have : Finite (MulAut (primeFormP h (idGram K n))) := inferInstance
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hne
  set π := primeFormFieldFactor h hC hn hne with hπdef
  have hApow : ∀ x : A, x ^ p = 1 := fun x => by
    have h1 : (x : MulAut (primeFormP h (idGram K n))) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (x : MulAut (primeFormP h (idGram K n))) x.2
    exact Subtype.ext (by simpa using h1)
  set π' : A →* (K ≃+* K) := π.comp A.subtype with hπ'
  have hD : ∀ a ∈ A, π a = 1 ↔ a ∈ primeFormD h (idGram K n) := fun a _ => by
    rw [← hkerD, MonoidHom.mem_ker]
  have hADH : ∀ a ∈ A, a ∈ primeFormD h (idGram K n) → a ∈ innU h n := fun a haA haD =>
    pElement_mem_inner_of_not_dvd_gcd h hn hne hp hg haD (by
      have := hApow ⟨a, haA⟩
      exact congrArg Subtype.val this)
  have hπne : π' ≠ 1 := by
    intro h1
    apply hAnot
    intro a haA
    have : π a = 1 := by
      have := congrArg (fun φ : A →* (K ≃+* K) => φ ⟨a, haA⟩) h1
      simpa [hπ'] using this
    exact hADH a haA ((hD a haA).mp this)
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  obtain ⟨hker, -⟩ := card_ker_eq_prime_of_ne_one hp hApow hAcard π' hπne
  have hAD : A ⊓ innU h n = A ⊓ primeFormD h (idGram K n) :=
    le_antisymm (inf_le_inf_left _ (innU_le_primeFormD h)) (fun a ha => ⟨ha.1, hADH a ha.1 ha.2⟩)
  have hkerA : (π'.ker).map A.subtype = A ⊓ primeFormD h (idGram K n) := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hD x x.2).mp hx⟩
    · rintro ⟨haA, haD⟩
      exact ⟨⟨a, haA⟩, (hD a haA).mpr haD, rfl⟩
  rw [hAD, ← hkerA, Subgroup.card_map_of_injective A.subtype_injective]
  exact hker

theorem three_lt_of_exceptional (hp3 : 3 ≤ p) (hpf : p ∣ f)
    (hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : 3 < p := by
  by_contra hlt
  have hp3' : p = 3 := by omega
  obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq₀.2
  have hf3 : f = 3 := by
    have := Nat.mul_div_cancel' hpf
    rw [hf1, hp3'] at this
    omega
  apply hg
  rw [hq₀.1, hℓ2, hf3, hp3']
  norm_num

end Plane

section Data

variable {n : ℕ}

private theorem fieldAutData_primeFormP_of_instance (hn3 : 3 ≤ n)
    {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hpair : ∀ (f₀ : ℕ) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
      (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c), f = p * f₀ → ¬ (p ∣ n ∧ p ∣ ℓ ^ f₀ + 1) →
      ¬ (n = 3 ∧ ℓ ^ f₀ = 2) →
      ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
        Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
          ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : FieldAutData (primeFormP h (idGram K n)) p := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf1 : 1 ≤ f := h.one_le
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hKcard : Nat.card K = ℓ ^ (2 * f) := h.card
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card h.prime (by omega) hKcard
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hg
  refine fieldAutData_of_standard
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = primeFormFieldHom h hC σ} ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE hEc
    by_cases hEH : E ≤ innU h n
    · obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
        rw [hbot, Subgroup.card_bot] at hEc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨g, rfl⟩ := hEH haE
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (map_one _)
    · have hcard := card_inf_innU_eq_prime h hn3 hne hp hg hE hEc hEH
      have h1 : (E ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hσ1 : primeFormFieldFactor h hC hn3 hne α ≠ 1 := by
      intro h1
      have hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← ker_primeFormFieldFactor h hC hn3 hne]
        exact h1
      obtain ⟨g, hgk⟩ := pElement_mem_inner_of_not_dvd_gcd h hn3 hne hp hg hD hαp
      exact hout g hgk.symm
    have hσp : (primeFormFieldFactor h hC hn3 hne α) ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    have hσord : orderOf (primeFormFieldFactor h hC hn3 hne α) = p := orderOf_eq_prime hσp hσ1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
        α hord _ rfl hσord
    refine ⟨primeFormConjHom h _ M, ⟨M, rfl⟩,
      primeFormFieldHom h hC (primeFormFieldFactor h hC hn3 hne α), ⟨_, hσord, rfl⟩, ?_⟩
    rw [← hM]
    group
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (primeFormFieldHom h hC)
      (zpowers_ringEquiv_eq_of_orderOf h.prime (by omega) hKcard hσ hτ)
  ·
    rintro _ ⟨σ, hσ, rfl⟩ hdvd x hx hcomm
    obtain ⟨hpf, -, -, -, -, -, -, -, -, hsimple, h72⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσ n hn3 hne hZ
    have hFeq : fixedSubgroup (primeFormFieldHom h hC σ) = fieldFixedPSU h n σ :=
      Subgroup.ext fun _ => Iff.rfl
    rw [hFeq] at hx hcomm hdvd
    by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
    · exfalso
      have hlt := three_lt_of_exceptional hp3 hpf hq₀ hg
      have h72' := (h72 hq₀ hlt).1
      rw [h72'] at hdvd
      have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · obtain ⟨hs, hnab, -⟩ := hsimple hq₀
      have hnab' : ∃ a b : ↥(fieldFixedPSU h n σ), a * b ≠ b * a := by
        push Not at hnab
        exact hnab
      have hz : (⟨x, hx⟩ : ↥(fieldFixedPSU h n σ)) ∈ Subgroup.center ↥(fieldFixedPSU h n σ) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcomm g g.2).symm
      rw [center_eq_bot_of_simple' hnab', Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
  ·
    rintro _ ⟨σ, hσ, rfl⟩ d hd hne'
    obtain ⟨A, rfl⟩ := hd
    obtain ⟨hpf, -, -, -, -, -, hrange, -, -, -, h72⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσ n hn3 hne hZ
    have hFeq : fixedSubgroup (primeFormFieldHom h hC σ) = fieldFixedPSU h n σ :=
      Subgroup.ext fun _ => Iff.rfl
    by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
    · right
      rw [hFeq]
      intro hdvd
      have hlt := three_lt_of_exceptional hp3 hpf hq₀ hg
      have h72' := (h72 hq₀ hlt).1
      rw [h72'] at hdvd
      have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    left
    have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
    rw [hFeq, ← hrange, range_subfieldPSU_eq_map] at hne' ⊢
    have hne'' : (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar n).map
        (primeFormConjSU h _ A).toMonoidHom ≠
          suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar n := by
      intro hh
      apply hne'
      rw [map_primeFormConjHom_map_mk, hh]
    have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
    have hgq : ¬ (p ∣ n ∧ p ∣ ℓ ^ (f / p) + 1) := by
      rintro ⟨hpn, hpq⟩
      apply hg
      refine Nat.dvd_gcd hpn ?_
      have hodd : Odd p := hp.odd_of_ne_two hp2
      have h1 := hodd.nat_add_dvd_pow_add_pow (ℓ ^ (f / p)) 1
      rw [one_pow, ← pow_mul, Nat.div_mul_cancel hpf] at h1
      exact hpq.trans h1
    have hgen := hpair (f / p) (fixSubfield σ) (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar
      hfeq hgq hq₀ A hne''
    have h4 := congrArg (Subgroup.map (QuotientGroup.mk' (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))) hgen
    rw [map_closure_union, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      at h4
    rw [map_primeFormConjHom_map_mk]
    exact h4

theorem fieldAutData_primeFormP_odd (hpair : SubfieldPairSUOdd) (hn3 : 3 ≤ n)
    {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : FieldAutData (primeFormP h (idGram K n)) p :=
  fieldAutData_primeFormP_of_instance hn3 h
    (fun f₀ k h₀ hbar hf hgq hq₀ A hne' =>
      hpair ℓ f f₀ K h k h₀ hbar p hp hp2 hf n hn3 hgq hq₀ A hne')
    hne hp hp2 hpℓ hg

end Data

end CFSG.LieType.SeitzGeneration
