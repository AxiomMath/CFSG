module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPair

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCLinComm
open CFSG.RankThree.PartOne.CTP
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

theorem rootDescent_of_cop {n : ℕ} {K : Type} [Field K] [Finite K] {k : Subfield K}
    {σ : K ≃+* K} {p : ℕ} (hp : p.Prime) (hk : ∀ x, x ∈ k ↔ σ x = x) (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1))) :
    ∀ a : Kˣ, (a : K) ∈ k → (∃ u : Kˣ, u ^ n = a) → ∃ w : Kˣ, (w : K) ∈ k ∧ w ^ n = a := by
  by_cases hpn : p ∣ n
  · refine KCLinearSubfield.root_descent_of_not_dvd hp hk hσp ?_
    intro hd
    rw [Nat.card_units] at hd
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (by
      have := Nat.dvd_gcd (dvd_refl p) (Nat.dvd_gcd hpn hd)
      rwa [Nat.Coprime.gcd_eq_one hcop] at this))
  · exact KCLinearSubfield.root_descent_of_coprime hk hσp
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm


theorem fixedSubgroup_fieldAut_eq_range_gen {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    {σ : K ≃+* K} (hσ : orderOf σ = p) :
    fixedSubgroup (fieldAut n K σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  exact SetLike.coe_injective
    (KCLinearSubfield.fixed_points_eq_range hk (by omega) (rootDescent_of_cop hp hk hσp hcop))

theorem outer_descent_gen {n : ℕ} (hn3 : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1))) :
    ∀ α : MulAut (projectiveSL n K), IsOuterOfOrder p α →
      ∃ d ∈ linearAutGroup n K, ∃ g ∈ {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut n K σ},
        α = d * g * d⁻¹ := by
  intro α hα
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  have hαE := mem_semilinearAutGroup_of_pow_eq_one hn3 hp hp2 hαp
  have hαD : α ∉ linearAutGroup n K := fun hD => by
    obtain ⟨g, hg⟩ := inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hαp
    exact hout g hg.symm
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf
      hn3 hK
  obtain ⟨-, σ, hσord, ⟨h, hhD, hαh⟩, -⟩ := hdesc p hp hpℓ α hαE hαD hord
  exact ⟨h, hhD, fieldAut n K σ, ⟨σ, hσord, rfl⟩, hαh⟩

theorem fieldAutData_projectiveSL_gen {n : ℕ} (hn3 : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    (hpair : ∀ k : Subfield K, Nat.card K = Nat.card k ^ p → ∀ A : GL (Fin n) K,
      (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k →
      Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
        ((slSub n k).map (slConjugation n K A).toMonoidHom :
          Set (SpecialLinearGroup (Fin n) K))) = ⊤) :
    FieldAutData (projectiveSL n K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  refine fieldAutData_of_standard (linearAutGroup n K)
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut n K σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    by_cases hEH : E ≤ innSL n K
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
    · have hAE : E ≤ (semilinPsi n K).range := fun a ha => by
        rw [range_semilinPsi]
        exact mem_semilinearAutGroup_of_pow_eq_one hn3 hp hp2
          (elemPow_eq_one_of_isElementaryAbelian a ha)
      have hcard := card_inf_inner_eq_prime hn3 hp hcop hcyc hAE hEc hEH
      have h1 : (E ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  · exact outer_descent_gen hn3 hp hp2 hℓ hpℓ hf hK hcop
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hσ,
      fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hτ,
      show semilinearFixedSubfield σ = semilinearFixedSubfield τ from
        fixedField_eq_of_orderOf hℓ hf hK hσ hτ]
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hcomm
    rw [fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hσ] at hx hcomm
    exact eq_one_of_central_range hn3 _ hx hcomm
  · rintro _ ⟨σ, hσ, rfl⟩ d hd hne
    left
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hd
    rw [fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hσ] at hne ⊢
    set k := semilinearFixedSubfield σ with hk
    have hpf : p ∣ f ∧ Nat.card k = ℓ ^ (f / p) :=
      card_semilinearFixedSubfield hℓ hf hK hσ
    have hcardK : Nat.card K = Nat.card k ^ p := by
      rw [hK, hpf.2, ← pow_mul, Nat.div_mul_cancel hpf.1]
    have hne' : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k := by
      intro h
      apply hne
      rw [map_conjAut_range_linearSubfieldInclusion, h, range_linearSubfieldInclusion_eq_map]
    have hgen := hpair k hcardK A hne'
    have h4 := congrArg (Subgroup.map (proj n K)) hgen
    rw [map_closure_union, Subgroup.map_top_of_surjective _ (proj_surjective n K)] at h4
    rw [map_conjAut_range_linearSubfieldInclusion, range_linearSubfieldInclusion_eq_map]
    exact h4

theorem fieldAutData_projectiveSL_of_cop {n : ℕ} (hn3 : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1))) :
    FieldAutData (projectiveSL n K) p :=
  fieldAutData_projectiveSL_gen hn3 hp hp2 hℓ hpℓ hf hK hcop fun k hcard A hne =>
    subfieldPairSL_gen hp hp2 k hcard hn3 A hne

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
