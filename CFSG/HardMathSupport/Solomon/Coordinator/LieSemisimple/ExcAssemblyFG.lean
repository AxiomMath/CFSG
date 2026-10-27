module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Ree

set_option linter.unusedSectionVars false


private theorem exists_form_of_theta {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (hex : ∀ α : MulAut (adjointGroup τ K), ∃ (g : adjointGroup τ K) (σ : K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹)
    {Θ : MulAut (adjointGroup τ K) →* (K ≃+* K)}
    (hΘ : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      Θ α = σ)
    (β : MulAut (adjointGroup τ K)) (hβ : β ^ p = 1) :
    ∃ (g : adjointGroup τ K) (σ : K ≃+* K),
      β = MulAut.conj g * exactNormalAut τ K 1 σ 0 ∧ σ ^ p = 1 := by
  obtain ⟨g, σ, hf⟩ := hex β
  refine ⟨g, σ, MulEquiv.ext fun h => Subtype.ext ?_, ?_⟩
  · rw [hf h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one, Subgroup.coe_inv]
  · rw [← hΘ β g σ hf, ← map_pow, hβ, map_one]

private theorem exists_form_of_phi (t : ReeTag) {K : Type} [Field K] [Finite K] [CharP K t.prime]
    {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = t.prime ^ f)
    (hex : ∀ α : MulAut (adjointGroup t.tag K), ∃ (g : adjointGroup t.tag K) (k : ℕ),
      α = MulAut.conj g * t.finiteExceptionalAut K ^ k)
    {Θ : MulAut (adjointGroup t.tag K) →* Multiplicative (ZMod (2 * f))}
    (hΘ : ∀ (α : MulAut (adjointGroup t.tag K)) (g : adjointGroup t.tag K) (k : ℕ),
      α = MulAut.conj g * t.finiteExceptionalAut K ^ k →
        Θ α = Multiplicative.ofAdd (k : ZMod (2 * f)))
    (β : MulAut (adjointGroup t.tag K)) (hβ : β ^ p = 1) :
    ∃ (g : adjointGroup t.tag K) (σ : K ≃+* K),
      β = MulAut.conj g * exactNormalAut t.tag K 1 σ 0 ∧ σ ^ p = 1 := by
  obtain ⟨g, k, hk⟩ := hex β
  have hdvd : 2 * f ∣ p * k := by
    have h1 : Θ β ^ p = 1 := by rw [← map_pow, hβ, map_one]
    rw [hΘ β g k hk, ← ofAdd_nsmul, ofAdd_eq_one] at h1
    rw [← ZMod.natCast_eq_zero_iff]
    simpa using h1
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  obtain ⟨j, rfl⟩ : 2 ∣ k := hcop.dvd_of_dvd_mul_left ((Dvd.intro f rfl).trans hdvd)
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (Fact.out : t.prime.Prime) hf hK
  refine ⟨g, fr ^ j, ?_, ?_⟩
  · rw [hk, finiteExceptionalAut_pow_two_mul,
      exactNormalAut_one_eq_finiteFrobeniusAut_pow t (ringAut_pow_apply_of_frobenius hfr j)]
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, mul_comm]
    have h2 : 2 * f ∣ 2 * (p * j) := by
      rw [show 2 * (p * j) = p * (2 * j) by ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

private theorem exists_form_FG {τ : Tag} (hτ : τ = .F4 ∨ τ = .G2) {K : Type} [Field K]
    [Finite K] (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) :
    ∃ (g : adjointGroup τ K) (σ : K ≃+* K),
      β = MulAut.conj g * exactNormalAut τ K 1 σ 0 ∧ σ ^ p = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K
  have hqK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  rcases hτ with rfl | rfl
  · by_cases hℓ2 : ℓ = 2
    ·
      have hc2 : CharP K 2 := by rw [← hℓ2]; infer_instance
      haveI : CharP K ReeTag.F4.prime := hc2
      have hK : Nat.card K = ReeTag.F4.prime ^ (f : ℕ) := by rw [hqK, hℓ2]; rfl
      obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf1 K hK
      exact exists_form_of_phi ReeTag.F4 hp hp2 hf1 hK (fun α => by
        obtain ⟨⟨g, k⟩, hk⟩ := (hNF α).exists
        exact ⟨g, k, hk⟩) hΘ β hβ
    ·
      obtain ⟨hNF, Θ, hΘ, -, -, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ
        hℓ2 hf1 K hqK .F4 (Or.inl rfl)
      exact exists_form_of_theta (fun α => by
        obtain ⟨⟨g, σ⟩, h, -⟩ := hNF α
        exact ⟨g, σ, h⟩) hΘ β hβ
  · by_cases hℓ2 : ℓ = 2
    ·
      have h3 := hG2 rfl
      have hf2 : 2 ≤ (f : ℕ) := by
        by_contra hlt
        have h1 : (f : ℕ) = 1 := by omega
        rw [hqK, hℓ2, h1] at h3
        norm_num at h3
      have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [hqK, hℓ2]
      obtain ⟨hNF, Θ, hΘ, -, -, -⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
          hf2 K hK
      exact exists_form_of_theta (fun α => by
        obtain ⟨⟨g, σ⟩, h, -⟩ := hNF α
        exact ⟨g, σ, h⟩) hΘ β hβ
    · by_cases hℓ3 : ℓ = 3
      ·
        have hc3 : CharP K 3 := by rw [← hℓ3]; infer_instance
        haveI : CharP K ReeTag.G2.prime := hc3
        have hK : Nat.card K = ReeTag.G2.prime ^ (f : ℕ) := by rw [hqK, hℓ3]; rfl
        obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := G2_three_exact_automorphism_normal_form hf1 K hK
        exact exists_form_of_phi ReeTag.G2 hp hp2 hf1 hK (fun α => by
          obtain ⟨⟨g, k⟩, hk⟩ := (hNF α).exists
          exact ⟨g, k, hk⟩) hΘ β hβ
      ·
        obtain ⟨hNF, Θ, hΘ, -, -, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ
          hℓ2 hf1 K hqK .G2 (Or.inr ⟨rfl, hℓ3⟩)
        exact exists_form_of_theta (fun α => by
          obtain ⟨⟨g, σ⟩, h, -⟩ := hNF α
          exact ⟨g, σ, h⟩) hΘ β hβ

theorem perfectInLayer_exc_FG {τ : Tag} (hτ : τ = .F4 ∨ τ = .G2) {K : Type} [Field K]
    [Finite K] (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (hmon : MonomialToralAt τ p)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : PerfectInLayer β := by
  classical
  obtain ⟨g, σ, hβe, hσp⟩ := exists_form_FG hτ hG2 hp hp2 β hβ
  by_cases hσ : σ = 1
  · subst hσ
    rw [exactNormalAut_one_one_zero, mul_one] at hβe
    subst hβe
    have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with h | h <;> simp [h]
    have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
      rcases hτ with h | h
      · exact single_edge_perfect τ K (by simp [h])
      · subst h
        exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
          (hG2 rfl)).commutator_eq_top
    have hgp : g ^ p = 1 := by
      have : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, hβ, map_one]
      exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
    have hg1 : (g : ModGL τ K) ≠ 1 := fun h1 => hβ1 (by
      have : g = 1 := Subtype.ext h1
      rw [this, map_one])
    have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ Nat.card K := fun hτG2 => by
      have h3 := hG2 hτG2
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      by_cases hp3' : p = 3
      · subst hp3'
        right
        have hK3 : Nat.card K ≠ 3 := fun h' => hpK (by rw [h'])
        omega
      · left
        have h4 : p ≠ 4 := fun h' => by rw [h'] at hp; exact absurd hp (by norm_num)
        omega
    exact perfectInLayer_exc_inner_untw hτ5 hp hpK hsmall hmon hperf (MulAut.conj g) g
      (baseChangeGL_mem_adjointGroup _ g.2) (fun c => by simp [MulAut.conj_apply])
      (by rw [← Subgroup.coe_pow, hgp]; rfl) hg1
  · rw [hβe]
    exact perfectInLayer_exc_field τ hp g 1 σ hσ hσp (by rw [← hβe]; exact hβ)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
