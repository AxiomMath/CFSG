module

public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.LieType.SeitzGeneration.OuterSUData
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

section Planes

variable {ℓ f p n : ℕ} {K : Type} [Field K]

theorem unitarySU_planeGen_of_ne (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hn : 3 ≤ n) (hq : p ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2)
    (E : Subgroup (unitarySU ℓ f K n)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  by_cases hpq : p ∣ ℓ ^ f + 1
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact closure_centralizers_unitarySU_of_dvd_add_one h hp hpq (hq hpq) E hcomm hexp hcard
  · by_cases hpq' : p ∣ ℓ ^ f - 1
    · exact unitarySU_planeGen_split h hp hp2 hpq' (by omega) E hcomm hexp hcard
    · have hp5 : 5 ≤ p := by
        have hp3 : p ≠ 3 := by
          rintro rfl
          have h3 : ¬ 3 ∣ ℓ ^ f := fun h3 =>
            hpℓ ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).1
              (Nat.prime_three.dvd_of_dvd_pow h3))
          omega
        have := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h' | h' | h' | h'
        · exact absurd h' hp2
        · exact absurd h' hp3
        · exact absurd (h' ▸ hp) (by norm_num)
        · exact h'
      exact unitarySUNontoral ℓ f p n K h hp hp5 hpℓ hpq hn E hcomm hexp hcard

theorem planeGen_primeFormP_unitary (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hker : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (hq : p ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2)
    (A : Subgroup (primeFormP h (idGram K n))) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    Subgroup.closure {k : primeFormP h (idGram K n) | ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  let ψ : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (ℓ ^ f) K) :=
    (Classical.choice (unitary_prime_form_full_semilinear_realization h
      (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).1).trans (unitaryPSUEquiv h (by omega))
  let A' := A.map ψ.toMonoidHom
  have hA' : IsElemAbelian p A' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hA _
  have : CFSG.IsElementaryAbelian p A' :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A').mpr hA'
  have hAc' : Nat.card A' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hAc]
  have hgen := closure_centralizers_statedProj_unitary_of_lift h hp (by omega) hker A' hAc'
    (fun E' hc he hcd => unitarySU_planeGen_of_ne h hp hp2 hpℓ hn hq E' hc he hcd)
  rw [eq_top_iff]
  intro x _
  have hx : ψ x ∈ Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ b ∈ A', b ≠ 1 ∧ k * b = b * k} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hset : {k : StatedProj (StatedSU n (ℓ ^ f) K) | ∃ b ∈ A', b ≠ 1 ∧ k * b = b * k} ⊆
      ψ.toMonoidHom '' {k : primeFormP h (idGram K n) | ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k} := by
    rintro k ⟨b, ⟨b', hb', rfl⟩, hb1, hkb⟩
    refine ⟨ψ.symm k, ⟨b', hb', fun h1 => hb1 (by rw [h1, map_one]), ?_⟩, by simp⟩
    apply ψ.injective
    simpa using hkb
  have h2 : ψ x ∈ (Subgroup.closure
      {k : primeFormP h (idGram K n) | ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}).map ψ.toMonoidHom := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hset hx
  obtain ⟨y, hy, hyx⟩ := h2
  rwa [ψ.injective hyx] at hy

end Planes

section Fix

variable {ℓ f p n : ℕ} {K : Type} [Field K]

theorem fixPlaneGen_primeFormP (h : UnitaryFieldData ℓ f K) (hn3 : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (h8 : ¬ (p = 3 ∧ ℓ ^ f = 8)) :
    FixPlaneGen (primeFormP h (idGram K n)) p := by
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  intro α hα A hA hAa hAc
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  have hτ1 : primeFormFieldFactor h hC hn3 hne α ≠ 1 := by
    intro h1
    have hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h hC hn3 hne]
      exact h1
    obtain ⟨g, hgk⟩ := pElement_mem_inner_of_not_dvd_gcd h hn3 hne hp hg hD hαp
    exact hout g hgk.symm
  have hτp : (primeFormFieldFactor h hC hn3 hne α) ^ p = 1 := by
    rw [← map_pow, hαp, map_one]
  have hτ : orderOf (primeFormFieldFactor h hC hn3 hne α) = p := orderOf_eq_prime hτp hτ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
      α hord _ rfl hτ
  obtain ⟨d, hd⟩ : ∃ d, d = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = primeFormFieldFactor h hC hn3 hne α := ⟨_, rfl⟩
  rw [← hd, ← hτdef] at hM
  rw [← hτdef] at hτ
  have hαeq : α = d * primeFormFieldHom h hC τ * d⁻¹ := by
    rw [← hM]
    group
  have hfixα : fixedSubgroup α = (fixedSubgroup (primeFormFieldHom h hC τ)).map d.toMonoidHom := by
    rw [hαeq]
    exact fixedSubgroup_conj d _
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hg
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, -, h72⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hτ n hn3 hne hZ
  have hFeq : fixedSubgroup (primeFormFieldHom h hC τ) = fieldFixedPSU h n τ :=
    Subgroup.ext fun _ => Iff.rfl
  have hjrange : (primeSubfieldPSU h hp hp2 hτ n).range =
      fixedSubgroup (primeFormFieldHom h hC τ) := by
    rw [hFeq, hrange]
  have hA₁F : A.map d⁻¹.toMonoidHom ≤ fixedSubgroup (primeFormFieldHom h hC τ) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' := hA ha
    rw [hfixα] at ha'
    obtain ⟨y, hy, rfl⟩ := ha'
    change d⁻¹ (d y) ∈ fixedSubgroup (primeFormFieldHom h hC τ)
    simpa using hy
  have hA₁c : Nat.card (A.map d⁻¹.toMonoidHom) = p ^ 2 := by
    rw [← hAc]
    exact Nat.card_congr (A.equivMapOfInjective _ (MulEquiv.injective _)).toEquiv.symm
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
  · exfalso
    have hlt := three_lt_of_exceptional hp3 hpf hq₀ hg
    obtain ⟨h72c, -⟩ := h72 hq₀ hlt
    have hdvd : p ∣ 2 ^ 3 * 3 ^ 2 := by
      have h1 : p ^ 2 ∣ Nat.card (fieldFixedPSU h n τ) := by
        rw [← hA₁c, ← hFeq]
        exact Subgroup.card_dvd_of_le hA₁F
      rw [h72c] at h1
      exact (dvd_pow_self p two_ne_zero).trans (by norm_num; exact h1)
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      omega
  have hA₂map : ((A.map d⁻¹.toMonoidHom).comap (primeSubfieldPSU h hp hp2 hτ n)).map
      (primeSubfieldPSU h hp hp2 hτ n) = A.map d⁻¹.toMonoidHom := by
    rw [Subgroup.map_comap_eq, hjrange]
    exact inf_eq_right.2 hA₁F
  have hA₂c : Nat.card ((A.map d⁻¹.toMonoidHom).comap (primeSubfieldPSU h hp hp2 hτ n)) =
      p ^ 2 := by
    have h1 : Nat.card (((A.map d⁻¹.toMonoidHom).comap (primeSubfieldPSU h hp hp2 hτ n)).map
        (primeSubfieldPSU h hp hp2 hτ n)) =
        Nat.card ((A.map d⁻¹.toMonoidHom).comap (primeSubfieldPSU h hp hp2 hτ n)) :=
      Subgroup.card_map_of_injective hinj
    rw [hA₂map, hA₁c] at h1
    exact h1.symm
  have hA₁a : IsElemAbelian p (A.map d⁻¹.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _
  have hA₂a : IsElemAbelian p ((A.map d⁻¹.toMonoidHom).comap (primeSubfieldPSU h hp hp2 hτ n)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h1 := congrArg Subtype.val (hA₁a.1.is_comm.comm
        (⟨primeSubfieldPSU h hp hp2 hτ n a, a.2⟩ : A.map d⁻¹.toMonoidHom)
        ⟨primeSubfieldPSU h hp hp2 hτ n b, b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h1
    · rw [map_pow, map_one]
      exact hA₁a.2 _ hx
  have hgen := planeGen_primeFormP_unitary (fixSubfield_unitaryFieldData h hp hp2 hτ) hn3 hq₀
    hp hp2 hpℓ (by
      rintro hdvd
      apply hg
      refine Nat.dvd_gcd ((Nat.dvd_gcd_iff.1 hdvd).1) ?_
      have hodd : Odd p := hp.odd_of_ne_two hp2
      have h1 := hodd.nat_add_dvd_pow_add_pow (ℓ ^ (f / p)) 1
      rw [one_pow, ← pow_mul, Nat.div_mul_cancel hpf] at h1
      exact ((Nat.dvd_gcd_iff.1 hdvd).2).trans h1) (by
      rintro hdvd h2
      apply h8
      obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
      have hp3' : p = 3 := by
        rw [h2] at hdvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
      refine ⟨hp3', ?_⟩
      have := Nat.mul_div_cancel' hpf
      rw [hf1, hp3'] at this
      rw [hℓ2, ← this]
      norm_num) _ hA₂a hA₂c
  intro x hx
  rw [hfixα] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← hjrange] at hy
  obtain ⟨z, rfl⟩ := hy
  have hz : z ∈ Subgroup.closure {k | ∃ b ∈ (A.map d⁻¹.toMonoidHom).comap
      (primeSubfieldPSU h hp hp2 hτ n), b ≠ 1 ∧ k * b = b * k} := by
    rw [hgen]
    exact Subgroup.mem_top _
  refine (Subgroup.closure_le ((Subgroup.closure
      {k | k ∈ fixedSubgroup α ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}).comap
        (d.toMonoidHom.comp (primeSubfieldPSU h hp hp2 hτ n)))).2 ?_ hz
  rintro k ⟨b, hb, hb1, hkb⟩
  refine Subgroup.subset_closure ⟨?_, d (primeSubfieldPSU h hp hp2 hτ n b), ?_, ?_, ?_⟩
  · rw [hfixα]
    exact ⟨primeSubfieldPSU h hp hp2 hτ n k, hjrange ▸ ⟨k, rfl⟩, rfl⟩
  · obtain ⟨a, ha, hab⟩ := hb
    change d (primeSubfieldPSU h hp hp2 hτ n b) ∈ A
    rw [← hab]
    simpa using ha
  · intro h1
    apply hb1
    apply hinj
    apply d.injective
    rw [h1, map_one, map_one]
  · change d (primeSubfieldPSU h hp hp2 hτ n k) * d (primeSubfieldPSU h hp hp2 hτ n b) =
      d (primeSubfieldPSU h hp hp2 hτ n b) * d (primeSubfieldPSU h hp hp2 hτ n k)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hkb]

end Fix

end CFSG.LieType.SeitzGeneration
