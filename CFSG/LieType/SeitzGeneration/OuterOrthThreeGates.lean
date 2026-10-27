module

public import CFSG.LieType.SeitzGeneration.OuterOrthGeneric

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

theorem plane_inf_inner_card_of_top (hg : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤) (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q))) (hAe : CFSG.IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2)
    (hAH : ¬ A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    Nat.card (A ⊓ OuterAutomorphisms.inner (matrixProjectiveDerived Q) : Subgroup _) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hAe
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨hHD, k₂, hk₂⟩, -⟩ := hg
  set D := (linearConjugationHom Q).range with hDdef
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hHdef
  have : H.Normal := OuterAutomorphisms.inner_normal _
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hAE : A ≤ matrixProjectiveImage Q := htop ▸ le_top
  have hADH : A ⊓ D ≤ H := by
    rintro x ⟨hxA, hxD⟩
    exact CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
      hk₂ hp hp2 hxD (CFSG.elemPow_eq_one_of_isElementaryAbelian x hxA)
  set φ : A →* (K ≃+* K) := ψ.comp (Subgroup.inclusion hAE) with hφ
  have hφker : φ.ker = D.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      hψker, Subgroup.mem_subgroupOf]
    rfl
  have hφp : ∀ a : A, φ a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have ha : a ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a
    rw [ha, map_one]
  have hrange_dvd : Nat.card φ.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
    obtain ⟨a, ha⟩ := σ.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← ha, hφp, OneMemClass.coe_one]
  have hrange_ne : Nat.card φ.range ≠ 1 := by
    intro h1
    apply hAH
    intro x hx
    apply hADH
    refine ⟨hx, ?_⟩
    have hmem : (⟨x, hx⟩ : A) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have : φ ⟨x, hx⟩ ∈ φ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [hφker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hrange : Nat.card φ.range = p := ((Nat.dvd_prime hp).mp hrange_dvd).resolve_left hrange_ne
  have hkercard : Nat.card φ.ker = p := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, hAcard, sq] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hHD' : H ≤ D := hHD
  have hAHeq : A ⊓ H = A ⊓ D := le_antisymm (inf_le_inf_left _ hHD') (le_inf inf_le_left hADH)
  have hcardAD : Nat.card (A ⊓ D : Subgroup _) = p := by
    rw [← hkercard, hφker, inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective A.subtype_injective]
  rw [hAHeq, hcardAD]

theorem exists_conj_mem_of_plane_of_top (hg : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤) (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hE : CFSG.IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ g : matrixProjectiveDerived Q, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have hnontriv : ∃ x : MulAut (matrixProjectiveDerived Q), x ∈ E ∧
      x ∈ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ∧
        x ≠ 1 := by
    by_cases hin : E ≤
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range
    · have hne : E ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2, hin x.2, fun h => hx1 (Subtype.ext h)⟩
    · have hpl : Nat.card ↥(E ⊓ (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range) = p :=
        plane_inf_inner_card_of_top hg htop hp hp2 E hE hEc hin
      have hne : (E ⊓ (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range) ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        rw [this] at hpl
        have := hp.one_lt
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2.1, x.2.2, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x, hxE, ⟨g, hg'⟩, hx1⟩ := hnontriv
  exact ⟨g, fun h1 => hx1 (by rw [← hg', h1, map_one]), hg' ▸ hxE⟩

theorem outer_mem_E_not_D_of_top (hg : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : IsOuterOfOrder p α) :
    α ∈ matrixProjectiveImage Q ∧ α ∉ (linearConjugationHom Q).range := by
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  refine ⟨htop ▸ Subgroup.mem_top α, fun hD => ?_⟩
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  obtain ⟨g, hgα⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2
      hD hαp
  exact hout g hgα.symm

end Gates

section Assembly

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem fieldAutData_matrixProjectiveDerived_odd {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hplane : ∀ E : Subgroup (MulAut (matrixProjectiveDerived Q)),
      CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        ∃ g : matrixProjectiveDerived Q, g ≠ 1 ∧ MulAut.conj g ∈ E)
    (hQ : ∀ σ : K ≃+* K, orderOf σ = p → ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hdesc : ∀ α : MulAut (matrixProjectiveDerived Q), IsOuterOfOrder p α →
      ∃ D ∈ (linearConjugationHom Q).range, ∃ (σ : K ≃+* K) (h : orderOf σ = p),
        α = D * fieldAutT Q σ (hQ σ h) * D⁻¹)
    (hgood : ∀ (σ : K ≃+* K) (h : orderOf σ = p), FixedGood Q σ (hQ σ h)) :
    FieldAutData (matrixProjectiveDerived Q) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine fieldAutData_of_standard (linearConjugationHom Q).range
    {g | ∃ (σ : K ≃+* K) (h : orderOf σ = p), g = fieldAutT Q σ (hQ σ h)}
    hplane ?_ ?_ ?_ ?_
  · intro α hα
    obtain ⟨D, hD, σ, h, rfl⟩ := hdesc α hα
    exact ⟨D, hD, _, ⟨σ, h, rfl⟩, rfl⟩
  · rintro _ ⟨σ₁, h₁, rfl⟩ _ ⟨σ₂, h₂, rfl⟩
    have hz : ∀ {τ₁ τ₂ : K ≃+* K}, orderOf τ₁ = p → orderOf τ₂ = p →
        τ₂ ∈ Subgroup.zpowers τ₁ := fun {τ₁ τ₂} g₁ g₂ => by
      have := zpowers_ringEquiv_eq_of_orderOf hℓ hf hK g₁ g₂
      exact this ▸ Subgroup.mem_zpowers τ₂
    have hmem : ∀ {τ₁ τ₂ : K ≃+* K} (g₁ : orderOf τ₁ = p) (g₂ : orderOf τ₂ = p),
        fieldPair Q τ₂ (hQ τ₂ g₂) ∈ Subgroup.zpowers (fieldPair Q τ₁ (hQ τ₁ g₁)) := by
      intro τ₁ τ₂ g₁ g₂
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hz g₁ g₂)
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
      rw [fieldPair_zpow_val, hm]
      rfl
    exact fixedSubgroup_eq_of_zpowers_eq (matrixProjectiveConjugationHom Q)
      (le_antisymm ((Subgroup.zpowers_le).2 (hmem h₂ h₁)) ((Subgroup.zpowers_le).2 (hmem h₁ h₂)))
  · rintro _ ⟨σ, h, rfl⟩ -
    exact (hgood σ h).1
  · rintro _ ⟨σ, h, rfl⟩ g hg' hne
    exact Or.inl ((hgood σ h).2 g hg' hne)

end Assembly

end CFSG.LieType.SeitzGeneration
