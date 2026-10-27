module

public import CFSG.LinearAlgebra.LinearGroups.SLConjugationRank
public import CFSG.LinearAlgebra.LinearGroups.SLConjugationFrob

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField

private noncomputable def slConjugationEmbFun {K : Type*} [Field K] (n : ℕ) {G : Type*}
    [Group G] (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) (x : ↥E) :
    MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
  slConjugation n K (Classical.choose (hconj x x.2))

private lemma slConjugationEmbFun_apply {K : Type*} [Field K] (n : ℕ) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) (x : ↥E)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ι (slConjugationEmbFun n ι hconj x g) = (x : G) * ι g * (x : G)⁻¹ :=
  (Classical.choose_spec (hconj x x.2) g).symm

private noncomputable def slConjugationEmbHom {K : Type*} [Field K] (n : ℕ) {G : Type*}
    [Group G] (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι)
    {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) :
    ↥E →* MulAut (Matrix.SpecialLinearGroup (Fin n) K) where
  toFun := slConjugationEmbFun n ι hconj
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply hι
    rw [slConjugationEmbFun_apply]
    simp
  map_mul' x y := by
    apply MulEquiv.ext
    intro g
    apply hι
    rw [MulAut.mul_apply, slConjugationEmbFun_apply, slConjugationEmbFun_apply,
      slConjugationEmbFun_apply]
    simp only [Subgroup.coe_mul]
    group

private lemma slConjugationEmbHom_apply {K : Type*} [Field K] (n : ℕ) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) (x : ↥E)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ι (slConjugationEmbHom n ι hι hconj x g) = (x : G) * ι g * (x : G)⁻¹ :=
  slConjugationEmbFun_apply n ι hconj x g

private lemma range_slConjugationEmbHom_le {K : Type*} [Field K] (n : ℕ) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) :
    (slConjugationEmbHom n ι hι hconj).range ≤ (slConjugation n K).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Classical.choose (hconj x x.2), rfl⟩

private lemma mem_ker_slConjugationEmbHom_iff {K : Type*} [Field K] (n : ℕ) {G : Type*}
    [Group G] (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι)
    {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) (x : ↥E) :
    x ∈ (slConjugationEmbHom n ι hι hconj).ker ↔
      (x : G) ∈ Subgroup.centralizer (ι.range : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
    have h1 : slConjugationEmbHom n ι hι hconj x g = g := by
      simpa using congrArg (fun f : MulAut (Matrix.SpecialLinearGroup (Fin n) K) => f g) hx
    have h2 : (x : G) * ι g * (x : G)⁻¹ = ι g := by
      rw [← slConjugationEmbHom_apply n ι hι hconj x g, h1]
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro hx
    apply MulEquiv.ext
    intro g
    apply hι
    rw [slConjugationEmbHom_apply, MulAut.one_apply]
    have hcomm : ι g * (x : G) = (x : G) * ι g :=
      (Subgroup.mem_centralizer_iff.mp hx) (ι g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

private noncomputable def kerEquiv {K : Type*} [Field K] (n : ℕ) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) :
    (slConjugationEmbHom n ι hι hconj).ker ≃
      ↥(E ⊓ Subgroup.centralizer (ι.range : Set G)) where
  toFun x := ⟨(x.1 : G), ⟨x.1.2, (mem_ker_slConjugationEmbHom_iff n ι hι hconj x.1).mp x.2⟩⟩
  invFun x :=
    ⟨⟨x.1, x.2.1⟩, (mem_ker_slConjugationEmbHom_iff n ι hι hconj ⟨x.1, x.2.1⟩).mpr x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl

private lemma card_ker_slConjugationEmbHom {K : Type*} [Field K] (n : ℕ) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin n) K →* G) (hι : Function.Injective ι) {E : Subgroup G}
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation n K A g)) :
    Nat.card (slConjugationEmbHom n ι hι hconj).ker =
      Nat.card ↥(E ⊓ Subgroup.centralizer (ι.range : Set G)) :=
  Nat.card_congr (kerEquiv n ι hι hconj)

private lemma slConjugationEmbHom_comm_slFieldAut {F : Type*} [Field F] {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* G) (hι : Function.Injective ι) (σ : F ≃+* F)
    (φ : G →* G) (hφι : ∀ g, φ (ι g) = ι (slFieldAut (Fin 3) F σ g)) {E : Subgroup G}
    (hφE : ∀ x ∈ E, φ x = x)
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 3) F,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation 3 F A g)) :
    ∀ x, slConjugationEmbHom 3 ι hι hconj x * slFieldAut (Fin 3) F σ =
      slFieldAut (Fin 3) F σ * slConjugationEmbHom 3 ι hι hconj x := by
  intro x
  apply MulEquiv.ext
  intro g
  apply hι
  rw [MulAut.mul_apply, MulAut.mul_apply, slConjugationEmbHom_apply, ← hφι g,
    ← hφι (slConjugationEmbHom 3 ι hι hconj x g), slConjugationEmbHom_apply]
  have key : φ ((x : G) * ι g * (x : G)⁻¹) = (x : G) * φ (ι g) * (x : G)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hφE x x.2]
  exact key.symm

theorem card_le_nine_mul_card_inf_centralizer_of_sl3 {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    {G : Type*} [Group G] (ι : Matrix.SpecialLinearGroup (Fin 3) K →* G)
    (hι : Function.Injective ι) {E : Subgroup G} [Finite E] (hE : CFSG.Open.IsElemAbelian 3 E)
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 3) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation 3 K A g)) :
    Nat.card E ≤ 9 * Nat.card ↥(E ⊓ Subgroup.centralizer (ι.range : Set G)) := by
  have h := card_le_nine_mul_card_ker_of_range_le_slConjugation h3 hE
    (slConjugationEmbHom 3 ι hι hconj) (range_slConjugationEmbHom_le 3 ι hι hconj)
  rwa [card_ker_slConjugationEmbHom 3 ι hι hconj] at h

theorem card_le_three_mul_card_inf_centralizer_of_sl2 {K : Type} [Field K] [Finite K]
    (h3 : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K) {G : Type*} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hι : Function.Injective ι) {E : Subgroup G}
    [Finite E] (hE : CFSG.Open.IsElemAbelian 3 E)
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 2) K,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation 2 K A g)) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (ι.range : Set G)) := by
  have h := card_le_three_mul_card_ker_of_range_le_slConjugation_two h3 h4 hE
    (slConjugationEmbHom 2 ι hι hconj) (range_slConjugationEmbHom_le 2 ι hι hconj)
  rwa [card_ker_slConjugationEmbHom 2 ι hι hconj] at h

theorem card_le_three_mul_card_inf_centralizer_of_sl3_frob {F : Type} [Field F] [Finite F]
    {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 3 = 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q)
    {G : Type*} [Group G] (ι : Matrix.SpecialLinearGroup (Fin 3) F →* G)
    (hι : Function.Injective ι) (φ : G →* G)
    (hφι : ∀ g, φ (ι g) = ι (slFieldAut (Fin 3) F σ g)) {E : Subgroup G} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) (hφE : ∀ x ∈ E, φ x = x)
    (hconj : ∀ x ∈ E, ∃ A : Matrix.GeneralLinearGroup (Fin 3) F,
      ∀ g, x * ι g * x⁻¹ = ι (slConjugation 3 F A g)) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (ι.range : Set G)) := by
  have hθσ := slConjugationEmbHom_comm_slFieldAut ι hι σ φ hφι hφE hconj
  have h := card_le_three_mul_card_ker_of_range_le_slConjugation_frob hF hq σ hσ hE
    (slConjugationEmbHom 3 ι hι hconj) (range_slConjugationEmbHom_le 3 ι hι hconj) hθσ
  rwa [card_ker_slConjugationEmbHom 3 ι hι hconj] at h

end CFSG.LinearGroups
