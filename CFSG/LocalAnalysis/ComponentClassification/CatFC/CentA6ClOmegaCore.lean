module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Lift

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem omegaLieModel_dvd_360 (hO : LieOrderFormulasInput) {X : Type} [Group X] {τ : StatedLieTag}
    {n e : ℕ} (hadm : StatedLieAdmissible τ n 3 e) (hm : Blueprint.LieModel X τ n 3 e)
    (hX : Nat.card X ∣ 360) : τ = .PSL ∧ n = 2 ∧ e = 2 ∧ Nat.card X = 360 := by
  obtain ⟨-, hmul, hfac⟩ := hO X τ n 3 e hadm hm
  have hf : 1 ≤ e := hadm.2.1
  rcases lieSylowExponent_ge_three hadm (by norm_num) with ⟨rfl, rfl⟩ | h3
  · have hXle : Nat.card X ≤ 360 := Nat.le_of_dvd (by norm_num) hX
    obtain ⟨q, hq⟩ : ∃ q, 3 ^ e = q := ⟨_, rfl⟩
    have hqodd : Odd q := hq ▸ (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
    simp only [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      hq] at hmul
    have hg : Nat.gcd 2 (q - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    rw [hg, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hmul
    have he2 : e ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have h27 : 27 ≤ q := by
        rw [← hq]
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hlt
      have h1 : 27 * (27 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul h27 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h27 2) 1)
      norm_num at h1
      omega
    interval_cases e
    · exact absurd (by norm_num) hadm.2.2.2.2
    · have hq9 : q = 9 := by rw [← hq]; norm_num
      subst hq9
      refine ⟨rfl, rfl, rfl, ?_⟩
      norm_num at hmul
      omega
  · exfalso
    have hdvd : 3 ^ (lieSylowExponent τ n * e) ∣ Nat.card X := by
      rw [← hfac]
      exact Nat.ordProj_dvd (Nat.card X) 3
    have h3f : 3 ≤ lieSylowExponent τ n * e := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : 3 ^ 3 ∣ 360 := ((pow_dvd_pow 3 h3f).trans hdvd).trans hX
    norm_num at h27

section Witness

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.omega_witness (hO : LieOrderFormulasInput) (h : A6Hyp σ D) {Y : Type}
    [Group Y] (hY : IsQuasisimple Y) (φ : Y →* ↥(fixedSubgroup σ)) (hφ : φ.range ≠ ⊥)
    {τ : StatedLieTag} {n e : ℕ} (hadm : StatedLieAdmissible τ n 3 e)
    (hm : Blueprint.LieModel (Y ⧸ center Y) τ n 3 e) :
    τ = .PSL ∧ n = 2 ∧ e = 2 ∧ φ.range = D := by
  have hQ : commutator Y = ⊤ := Group.isPerfect_def.mp hY.1
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 : φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
    have h2 : commutator Y = ⁅(⊤ : Subgroup Y), ⊤⁆ := rfl
    rw [h2] at hQ
    rw [h1, ← Subgroup.map_commutator, hQ]
  have hle : φ.range ≤ D := h.2.2 _ hperf
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_range hY φ hφ
  have hR : Nat.card φ.range ∣ 360 := (Subgroup.card_dvd_of_le hle).trans (h.card_D ▸ dvd_rfl)
  have hdvd : Nat.card (Y ⧸ center Y) ∣ Nat.card φ.range := by
    rw [Nat.card_congr E.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨h1, h2, h3, h4⟩ := omegaLieModel_dvd_360 hO hadm hm (hdvd.trans hR)
  refine ⟨h1, h2, h3, ?_⟩
  have h360 : 360 ∣ Nat.card φ.range := h4 ▸ hdvd
  have hcard : Nat.card φ.range = 360 := Nat.dvd_antisymm hR h360
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [h.card_D]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_D, hcard])

theorem A6Hyp.omega_false_of_commuting (hO : LieOrderFormulasInput) (h : A6Hyp σ D) {Y₁ Y₂ : Type}
    [Group Y₁] [Group Y₂] (hY₁ : IsQuasisimple Y₁) (hY₂ : IsQuasisimple Y₂)
    (φ₁ : Y₁ →* ↥(fixedSubgroup σ)) (φ₂ : Y₂ →* ↥(fixedSubgroup σ))
    (hφ₁ : φ₁.range ≠ ⊥) (hφ₂ : φ₂.range ≠ ⊥) (hcomm : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x)
    (m₁ : ∃ (τ : StatedLieTag) (n e : ℕ), StatedLieAdmissible τ n 3 e ∧
      Blueprint.LieModel (Y₁ ⧸ center Y₁) τ n 3 e)
    (m₂ : ∃ (τ : StatedLieTag) (n e : ℕ), StatedLieAdmissible τ n 3 e ∧
      Blueprint.LieModel (Y₂ ⧸ center Y₂) τ n 3 e) : False := by
  obtain ⟨τ₁, n₁, e₁, a₁, l₁⟩ := m₁
  obtain ⟨τ₂, n₂, e₂, a₂, l₂⟩ := m₂
  obtain ⟨-, -, -, hr₁⟩ := h.omega_witness hO hY₁ φ₁ hφ₁ a₁ l₁
  obtain ⟨-, -, -, hr₂⟩ := h.omega_witness hO hY₂ φ₂ hφ₂ a₂ l₂
  obtain ⟨-, ⟨eD⟩, -⟩ := h
  obtain ⟨a, b, hab⟩ := a6sq_nonab
  apply hab
  have key : ∀ u v : ↥D, u * v = v * u := by
    intro u v
    have hu : u.val ∈ φ₁.range := hr₁ ▸ u.2
    have hv : v.val ∈ φ₂.range := hr₂ ▸ v.2
    obtain ⟨x, hx⟩ := hu
    obtain ⟨y, hy⟩ := hv
    apply Subtype.ext
    change u.val * v.val = v.val * u.val
    rw [← hx, ← hy]
    exact hcomm x y
  have := congrArg eD (key (eD.symm a) (eD.symm b))
  simpa using this

end Witness

section Transfer

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 (projChain projChain_eq_one_iff)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)

@[expose] noncomputable def omegaToFixed {Y : Type} [Group Y] (hY : commutator Y = ⊤)
    (φ : Y →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) :
    Y →* ↥(fixedSubgroup (projectiveConjugation Q A μ hsim)) :=
  (projChain Q A μ hsim).comp
    ((((fixedCentralizerEquiv Q A μ hsim).symm.toMonoidHom.comp φ)).codRestrict
      ((orthogonalDerived Q).subgroupOf (fixedSubgroup (similarityConjugation Q A μ hsim)))
      (fun y => by
        rw [Subgroup.mem_subgroupOf]
        have h1 := a6sq_range_le_derived
          ((orthogonalOperatorCentralizer Q A.toLinearMap).subtype.comp φ) hY
        exact h1 ⟨y, rfl⟩))

theorem omegaToFixed_eq_one_iff {Y : Type} [Group Y] (hY : commutator Y = ⊤)
    (φ : Y →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) (y : Y) :
    omegaToFixed Q A μ hsim hY φ y = 1 ↔ (φ y).val ∈ scalarSigns Q := by
  unfold omegaToFixed
  rw [MonoidHom.comp_apply, projChain_eq_one_iff]
  rfl

theorem omega_exists_mul_ne {Y : Type} [Group Y] (hY : IsQuasisimple Y) :
    ∃ x y : Y, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hY
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul]

theorem omegaToFixed_ne_bot {Y : Type} [Group Y] (hY : IsQuasisimple Y)
    (φ : Y →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) (hφ : Function.Injective φ) :
    (omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY.1) φ).range ≠ ⊥ := by
  intro hbot
  obtain ⟨x, y, hxy⟩ := omega_exists_mul_ne hY
  apply hxy
  have h2 : ∀ z, (φ z).val ∈ scalarSigns Q := fun z =>
    (omegaToFixed_eq_one_iff Q A μ hsim (Group.isPerfect_def.mp hY.1) φ z).mp (by
      have : omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY.1) φ z ∈
          (omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY.1) φ).range := ⟨z, rfl⟩
      rw [hbot] at this
      exact this)
  apply hφ
  rw [map_mul, map_mul]
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp (scalarSigns_central Q (h2 x)) (φ y).val).symm

theorem omegaToFixed_comm {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] (h₁ : commutator Y₁ = ⊤)
    (h₂ : commutator Y₂ = ⊤) (φ₁ : Y₁ →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap))
    (φ₂ : Y₂ →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap))
    (hcomm : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x) (x : Y₁) (y : Y₂) :
    omegaToFixed Q A μ hsim h₁ φ₁ x * omegaToFixed Q A μ hsim h₂ φ₂ y =
      omegaToFixed Q A μ hsim h₂ φ₂ y * omegaToFixed Q A μ hsim h₁ φ₁ x := by
  unfold omegaToFixed
  simp only [MonoidHom.comp_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.val) (hcomm x y)

variable {Q A μ hsim} in
theorem omega_false_of_witness [Finite (projectiveDerived Q)] (hO : LieOrderFormulasInput)
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (h : A6Hyp (projectiveConjugation Q A μ hsim) D) {Y : Type} [Group Y] (hY : IsQuasisimple Y)
    (φ : Y →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) (hφ : Function.Injective φ)
    {τ : StatedLieTag} {n e : ℕ} (hadm : StatedLieAdmissible τ n 3 e)
    (hm : Blueprint.LieModel (Y ⧸ center Y) τ n 3 e) (hne : ¬ (τ = .PSL ∧ n = 2 ∧ e = 2)) :
    False := by
  obtain ⟨h1, h2, h3, -⟩ := h.omega_witness hO hY
    (omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY.1) φ)
    (omegaToFixed_ne_bot Q A μ hsim hY φ hφ) hadm hm
  exact hne ⟨h1, h2, h3⟩

variable {Q A μ hsim} in
theorem omega_false_of_two_witnesses [Finite (projectiveDerived Q)] (hO : LieOrderFormulasInput)
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (h : A6Hyp (projectiveConjugation Q A μ hsim) D) {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂]
    (hY₁ : IsQuasisimple Y₁) (hY₂ : IsQuasisimple Y₂)
    (φ₁ : Y₁ →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) (hφ₁ : Function.Injective φ₁)
    (φ₂ : Y₂ →* ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) (hφ₂ : Function.Injective φ₂)
    (hcomm : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x)
    (m₁ : ∃ (τ : StatedLieTag) (n e : ℕ), StatedLieAdmissible τ n 3 e ∧
      Blueprint.LieModel (Y₁ ⧸ center Y₁) τ n 3 e)
    (m₂ : ∃ (τ : StatedLieTag) (n e : ℕ), StatedLieAdmissible τ n 3 e ∧
      Blueprint.LieModel (Y₂ ⧸ center Y₂) τ n 3 e) : False :=
  h.omega_false_of_commuting hO hY₁ hY₂
    (omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY₁.1) φ₁)
    (omegaToFixed Q A μ hsim (Group.isPerfect_def.mp hY₂.1) φ₂)
    (omegaToFixed_ne_bot Q A μ hsim hY₁ φ₁ hφ₁) (omegaToFixed_ne_bot Q A μ hsim hY₂ φ₂ hφ₂)
    (omegaToFixed_comm Q A μ hsim _ _ φ₁ φ₂ hcomm) m₁ m₂

end Transfer

end CFSG.ComponentClassification.CatFC
