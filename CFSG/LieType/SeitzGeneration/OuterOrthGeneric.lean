module

public import CFSG.LieType.SeitzGeneration.OuterOrthPair
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

omit [Finite K] in
theorem mem_E_of_pow_eq_one_gates (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    {β : MulAut (matrixProjectiveDerived Q)} (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
  have hpg : IsPGroup p (Subgroup.zpowers β) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hβp, _root_.one_zpow]
    rfl
  have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ hpg
  have h1 : β ∈ projectivePointFamilyAut Q := hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β))
  rw [hg.2.2.2.2.2.1] at h1
  exact h1

theorem mem_conj_of_mem_D_gates (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ p = 1) : ∃ g : matrixProjectiveDerived Q, MulAut.conj g = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp (by omega) hβD hβp

theorem outer_mem_E_not_D (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : IsOuterOfOrder p α) :
    α ∈ matrixProjectiveImage Q ∧ α ∉ (linearConjugationHom Q).range := by
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  refine ⟨mem_E_of_pow_eq_one_gates hg hp hp3 hαp, fun hD => ?_⟩
  obtain ⟨g, hgα⟩ := mem_conj_of_mem_D_gates hg hp hp3 hD hαp
  exact hout g hgα.symm

omit [Finite K] in
theorem exists_conj_mem_of_plane_gates (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    (E : Subgroup (MulAut (matrixProjectiveDerived Q))) (hE : CFSG.IsElementaryAbelian p E)
    (hEc : Nat.card E = p ^ 2) : ∃ g : matrixProjectiveDerived Q, g ≠ 1 ∧ MulAut.conj g ∈ E := by
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
        (hg.2.2.2.2.2.2.2.1 p hp hp3 E hE hEc hin).1
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

end Gates

section Descent

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem exists_conj_fieldAutT_of_similarity {σ : K ≃+* K}
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) {U : similarityPairs Q}
    (hUσ : U.val.right = σ) (S : GL (Fin d) K) (ν : Kˣ)
    (hSQ : ∀ v, Q (S.val *ᵥ v) = ν * Q v)
    (hSA : S * U.val.left = glFieldAut (Fin d) K σ S) :
    ∃ D ∈ (linearConjugationHom Q).range,
      matrixProjectiveConjugationHom Q U = D * fieldAutT Q σ hQσ * D⁻¹ := by
  subst hUσ
  have hSinv : ∀ v, Q ((S⁻¹ : GL (Fin d) K).val *ᵥ v) = ((ν⁻¹ : Kˣ) : K) * Q v := by
    intro v
    have h1 := hSQ ((S⁻¹ : GL (Fin d) K).val *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    rw [h1, ← mul_assoc, Units.inv_mul, one_mul]
  let Dp : similarityPairs Q :=
    ⟨⟨S⁻¹, 1⟩, ν⁻¹, fun v => by
      rw [coordinateSemilinearMap_apply]
      have := hSinv v
      simpa using this⟩
  have hDplin : Dp ∈ linearSimilarityPairs Q := (mem_linearSimilarityPairs_iff _ Dp).2 rfl
  have hUeq : U = Dp * fieldPair Q U.val.right hQσ * Dp⁻¹ := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · have h1 : U.val.left = S⁻¹ * glFieldAut (Fin d) K U.val.right S := by
        rw [← hSA]
        group
      rw [h1]
      simp [Dp, fieldPair]
    · simp [Dp, fieldPair]
  refine ⟨matrixProjectiveConjugationHom Q Dp, ⟨⟨Dp, hDplin⟩, rfl⟩, ?_⟩
  have hκ := congrArg (matrixProjectiveConjugationHom Q) hUeq
  rw [map_mul, map_mul, map_inv] at hκ
  exact hκ

theorem exists_conj_fieldAutT_of_descent {ℓ f p : ℕ}
    {Disp : ∀ U : similarityPairs Q,
      QuadraticForm (KCOrthogonalDescent.fixedField U.val) (KCOrthogonalDescent.fixedSpace U.val) →
        Prop}
    {a : MulAut (matrixProjectiveDerived Q)} (haE : a ∈ matrixProjectiveImage Q)
    (hdesc : KCOrthogonalDescent.OrthogonalFieldDescent ℓ f p Q Disp a)
    (hQ : ∀ σ : K ≃+* K, orderOf σ = p → ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hDisp : ∀ (U : similarityPairs Q)
      (Q₀ : QuadraticForm (KCOrthogonalDescent.fixedField U.val)
        (KCOrthogonalDescent.fixedSpace U.val)), orderOf U.val.right = p → Disp U Q₀ →
      ∃ (S : GL (Fin d) K) (ν : Kˣ), (∀ v, Q (S.val *ᵥ v) = ν * Q v) ∧
        S * U.val.left = glFieldAut (Fin d) K U.val.right S) :
    ∃ D ∈ (linearConjugationHom Q).range, ∃ (σ : K ≃+* K) (h : orderOf σ = p),
      a = D * fieldAutT Q σ (hQ σ h) * D⁻¹ := by
  obtain ⟨g, hg⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord, -, U, cc, Q₀, hUκ, hUr, -, hdisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  have hordU : orderOf U.val.right = p := by rw [hUr]; exact hord
  obtain ⟨S, ν, hSQ, hSA⟩ := hDisp U Q₀ hordU hdisp
  obtain ⟨D, hD, hDeq⟩ := exists_conj_fieldAutT_of_similarity Q (hQ _ hordU) rfl S ν hSQ hSA
  exact ⟨D, hD, U.val.right, hordU, by rw [← hUκ]; exact hDeq⟩

end Descent

section Fixed

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem center_eq_bot_of_solvableRadical' {N : Type} [Group N]
    (h : solvableRadical N = ⊥) : Subgroup.center N = ⊥ :=
  le_bot_iff.1 (h ▸ le_sSup ⟨inferInstance, inferInstance⟩)

@[expose] def FixedGood (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) : Prop :=
  (∀ x ∈ fixedSubgroup (fieldAutT Q σ hQσ),
    (∀ y ∈ fixedSubgroup (fieldAutT Q σ hQσ), x * y = y * x) → x = 1) ∧
  ∀ g ∈ (linearConjugationHom Q).range,
    (fixedSubgroup (fieldAutT Q σ hQσ)).map g.toMonoidHom ≠ fixedSubgroup (fieldAutT Q σ hQσ) →
      Subgroup.closure ((fixedSubgroup (fieldAutT Q σ hQσ) : Set (matrixProjectiveDerived Q)) ∪
        ((fixedSubgroup (fieldAutT Q σ hQσ)).map g.toMonoidHom :
          Set (matrixProjectiveDerived Q))) = ⊤

theorem fixedGood_of_subfieldConclusion {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
    {Q₀ : QuadraticForm k (Fin d → k)} {σ : K ≃+* K} {p : ℕ} {hext : IsExtension k Q₀ Q}
    {hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)}
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ) (hpair : OrthPairShape k Q₀ Q) :
    FixedGood Q σ hQσ := by
  obtain ⟨-, -, hfixiff, -, -, -, hrad, -, -, -⟩ := hconc
  have hfix : fixedSubgroup (fieldAutT Q σ hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => hfixiff t
  refine ⟨fun x hx hc => ?_, ?_⟩
  · have hxN := (hfixiff x).1 hx
    have hcen : (⟨x, hxN⟩ : ↥(subfieldFixedGroup k Q₀ Q)) ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y.1 ((hfixiff y.1).2 y.2)).symm
    rw [center_eq_bot_of_solvableRadical' hrad, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · rw [hfix]
    exact hpair

end Fixed

section Assembly

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

omit [Finite K] in
theorem fieldAutData_matrixProjectiveDerived {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hg : OrthogonalGates Q f)
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
    (fun E hE hEc => exists_conj_mem_of_plane_gates hg hp hp3 E hE hEc) ?_ ?_ ?_ ?_
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
