module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
import CFSG.Adapters.LinearCatalog
import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

theorem map_glbCore_le {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (k : ℕ) (φ : K ≃* L) (P : Subgroup K) :
    (GLBCore p k P).map φ.toMonoidHom ≤ GLBCore p k (P.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap, fullCore_le_iff]
  intro Q hQP hQk
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  exact normalizer_le_glbCore p k (Subgroup.map_mono hQP)
    (by rwa [pRank_map_of_injective p hp φ.toMonoidHom φ.injective Q])

theorem glbCore_eq_top_of_pGroup {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (k : ℕ)
    {P : Subgroup K} (hP : IsPGroup p P) (hcore : GLBCore p k P = ⊤) (T : Sylow p K) :
    GLBCore p k (T : Subgroup K) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K S T
  have hS : GLBCore p k (S : Subgroup K) = ⊤ :=
    top_le_iff.mp (hcore ▸ glbCore_mono p k hPS)
  have h := map_glbCore_le hp k (MulAut.conj g) (S : Subgroup K)
  rw [hS, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, top_le_iff] at h
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact h

namespace LinThreeCore

open Matrix
open scoped MatrixGroups commutatorElement

section Elementary

variable {F : Type} [Field F]

abbrev x01 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a

abbrev x02 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a

abbrev x12 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a

abbrev x10 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a

abbrev x21 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a

abbrev x20 (a : F) : SL(3, F) := SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a

@[expose] def y1 (a b : F) : SL(3, F) := x01 a * x02 b

@[expose] def y2 (a b : F) : SL(3, F) := x02 a * x12 b

theorem y1_mul (a b a' b' : F) : y1 a b * y1 a' b' = y1 (a + a') (b + b') := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y1, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply] <;> ring

theorem y2_mul (a b a' b' : F) : y2 a b * y2 a' b' = y2 (a + a') (b + b') := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y2, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply] <;> ring

theorem x21_mul_y1 (c a b : F) : x21 c * y1 a b = y1 (a - b * c) b * x21 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y1, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply]

theorem x12_mul_y1 (c a b : F) : x12 c * y1 a b = y1 a (b - a * c) * x12 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y1, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply]

theorem x10_mul_y2 (c a b : F) : x10 c * y2 a b = y2 a (b + c * a) * x10 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y2, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply]
  ring

theorem y1_apply (a b : F) :
    (y1 a b : Matrix (Fin 3) (Fin 3) F) 0 1 = a ∧ (y1 a b : Matrix (Fin 3) (Fin 3) F) 0 2 = b := by
  constructor <;>
    simp [y1, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply]

theorem y2_apply (a b : F) :
    (y2 a b : Matrix (Fin 3) (Fin 3) F) 0 2 = a ∧ (y2 a b : Matrix (Fin 3) (Fin 3) F) 1 2 = b := by
  constructor <;>
    simp [y2, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply]

@[expose] def psi1 : Multiplicative (F × F) →* SL(3, F) :=
  MonoidHom.mk' (fun y => y1 (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2) fun y z => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, y1_mul]

@[expose] def psi2 : Multiplicative (F × F) →* SL(3, F) :=
  MonoidHom.mk' (fun y => y2 (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2) fun y z => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, y2_mul]

theorem psi1_ofAdd (a b : F) : psi1 (Multiplicative.ofAdd (a, b)) = y1 a b := rfl

theorem psi1_apply (y : Multiplicative (F × F)) :
    psi1 y = y1 (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2 := rfl

theorem psi2_apply (y : Multiplicative (F × F)) :
    psi2 y = y2 (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2 := rfl

@[expose] def E1 (F : Type) [Field F] : Subgroup SL(3, F) := psi1.range

@[expose] def E2 (F : Type) [Field F] : Subgroup SL(3, F) := psi2.range

theorem eq_one_of_psi1_mem_center {y : Multiplicative (F × F)}
    (hy : psi1 y ∈ Subgroup.center SL(3, F)) : y = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hy
  obtain ⟨a, b⟩ := y
  have e : (y1 a b : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) r := hr.symm
  have h01 := congr_arg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) e
  have h02 := congr_arg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) e
  simp only [(y1_apply a b).1, (y1_apply a b).2, Matrix.scalar_apply,
    Matrix.diagonal_apply] at h01 h02
  simp at h01 h02
  subst h01 h02
  rfl

theorem eq_one_of_psi2_mem_center {y : Multiplicative (F × F)}
    (hy : psi2 y ∈ Subgroup.center SL(3, F)) : y = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hy
  obtain ⟨a, b⟩ := y
  have e : (y2 a b : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) r := hr.symm
  have h02 := congr_arg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) e
  have h12 := congr_arg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) e
  simp only [(y2_apply a b).1, (y2_apply a b).2, Matrix.scalar_apply,
    Matrix.diagonal_apply] at h02 h12
  simp at h02 h12
  subst h02 h12
  rfl

theorem mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  simpa [mul_assoc] using h2 _ hx

theorem transvection_mem_normalizer_range {H : Type*} [Group H] (ψ : H →* SL(3, F))
    {i j : Fin 3} (hij : i ≠ j)
    (hconj : ∀ (c : F) (y : H), ∃ y' : H, SpecialLinearGroup.transvection hij c * ψ y =
      ψ y' * SpecialLinearGroup.transvection hij c) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ Subgroup.normalizer (ψ.range : Set SL(3, F)) := by
  have key : ∀ c' : F, ∀ x ∈ ψ.range, SpecialLinearGroup.transvection hij c' * x *
      (SpecialLinearGroup.transvection hij c')⁻¹ ∈ ψ.range := by
    rintro c' _ ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hconj c' y
    exact ⟨y', by rw [hy', mul_inv_cancel_right]⟩
  refine mem_normalizer_of_conj (key c) fun x hx => ?_
  have := key (-c) x hx
  rwa [← SpecialLinearGroup.transvection_inv, inv_inv] at this

theorem x12_mem_normalizer_E1 (c : F) : x12 c ∈ Subgroup.normalizer (E1 F : Set SL(3, F)) := by
  have h := transvection_mem_normalizer_range (F := F) psi1 (show (1 : Fin 3) ≠ 2 by decide)
    (fun c y => ?_) c
  · exact h
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y).1,
    (Multiplicative.toAdd y).2 - (Multiplicative.toAdd y).1 * c), ?_⟩
  rw [psi1_apply, psi1_apply, toAdd_ofAdd]
  exact x12_mul_y1 c _ _

theorem x21_mem_normalizer_E1 (c : F) : x21 c ∈ Subgroup.normalizer (E1 F : Set SL(3, F)) := by
  have h := transvection_mem_normalizer_range (F := F) psi1 (show (2 : Fin 3) ≠ 1 by decide)
    (fun c y => ?_) c
  · exact h
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y).1 - (Multiplicative.toAdd y).2 * c,
    (Multiplicative.toAdd y).2), ?_⟩
  rw [psi1_apply, psi1_apply, toAdd_ofAdd]
  exact x21_mul_y1 c _ _

theorem x10_mem_normalizer_E2 (c : F) : x10 c ∈ Subgroup.normalizer (E2 F : Set SL(3, F)) := by
  have h := transvection_mem_normalizer_range (F := F) psi2 (show (1 : Fin 3) ≠ 0 by decide)
    (fun c y => ?_) c
  · exact h
  refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y).1,
    (Multiplicative.toAdd y).2 + c * (Multiplicative.toAdd y).1), ?_⟩
  rw [psi2_apply, psi2_apply, toAdd_ofAdd]
  exact x10_mul_y2 c _ _

theorem x01_mem_E1 (a : F) : x01 a ∈ E1 F :=
  ⟨Multiplicative.ofAdd (a, 0), by simp [psi1_ofAdd, y1]⟩

theorem x02_mem_E1 (a : F) : x02 a ∈ E1 F :=
  ⟨Multiplicative.ofAdd (0, a), by simp [psi1_ofAdd, y1]⟩

theorem E2_le_normalizer_E1 : E2 F ≤ Subgroup.normalizer (E1 F : Set SL(3, F)) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, b⟩ := y
  exact mul_mem (Subgroup.le_normalizer (x02_mem_E1 a)) (x12_mem_normalizer_E1 b)

theorem pow_eq_one_of_card {p : ℕ} (hF : Nat.card F = p) (y : Multiplicative (F × F)) :
    y ^ p = 1 := by
  obtain ⟨u, v⟩ := y
  have hu : p • u = 0 := hF ▸ card_nsmul_eq_zero'
  have hv : p • v = 0 := hF ▸ card_nsmul_eq_zero'
  change Multiplicative.ofAdd (u, v) ^ p = 1
  rw [← ofAdd_nsmul, Prod.smul_mk, hu, hv]
  rfl

omit [Field F] in
theorem card_multiplicative_prod {p : ℕ} (hF : Nat.card F = p) :
    Nat.card (Multiplicative (F × F)) = p ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, hF, sq]

theorem isPGroup_range {p : ℕ} (hF : Nat.card F = p)
    (ψ : Multiplicative (F × F) →* SL(3, F)) : IsPGroup p ψ.range :=
  (IsPGroup.of_card (card_multiplicative_prod hF)).of_surjective ψ.rangeRestrict
    ψ.rangeRestrict_surjective

omit [Field F] in
theorem two_le_pRank_range {A K : Type*} [CommGroup A] [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hA : Nat.card A = p ^ 2) (hexp : ∀ a : A, a ^ p = 1) (φ : A →* K)
    (hφ : Function.Injective φ) : 2 ≤ Open.pRank p φ.range := by
  refine le_pRank_of_isElemAbelian hp (E := φ.range) ⟨inferInstance, ?_⟩ ?_
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem exists_pGroup_glbCore_eq_top {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    {K : Type*} [Group K] [Finite K] (f : SL(3, F) →* K) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → x ∈ Subgroup.center SL(3, F)) :
    ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hcard := card_multiplicative_prod hF
  have hr₁ : 2 ≤ Open.pRank p ((E1 F).map f) := by
    have := two_le_pRank_range hp hcard (pow_eq_one_of_card hF) (f.comp psi1) (by
      rw [injective_iff_map_eq_one]
      exact fun y hy => eq_one_of_psi1_mem_center (hker _ hy))
    rwa [MonoidHom.range_comp] at this
  have hr₂ : 2 ≤ Open.pRank p ((E2 F).map f) := by
    have := two_le_pRank_range hp hcard (pow_eq_one_of_card hF) (f.comp psi2) (by
      rw [injective_iff_map_eq_one]
      exact fun y hy => eq_one_of_psi2_mem_center (hker _ hy))
    rwa [MonoidHom.range_comp] at this
  have hU : IsPGroup p (E1 F ⊔ E2 F : Subgroup SL(3, F)) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_range hF psi1) (isPGroup_range hF psi2)
      E2_le_normalizer_E1
  refine ⟨(E1 F ⊔ E2 F).map f, hU.map f, ?_⟩
  set Γ := GLBCore p 2 ((E1 F ⊔ E2 F).map f)
  have hN₁ : ∀ g ∈ Subgroup.normalizer (E1 F : Set SL(3, F)), f g ∈ Γ := fun g hg =>
    normalizer_le_glbCore p 2 (Subgroup.map_mono le_sup_left) hr₁
      (Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩)
  have hN₂ : ∀ g ∈ Subgroup.normalizer (E2 F : Set SL(3, F)), f g ∈ Γ := fun g hg =>
    normalizer_le_glbCore p 2 (Subgroup.map_mono le_sup_right) hr₂
      (Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩)
  have h01 : ∀ c, f (x01 c) ∈ Γ := fun c => hN₁ _ (Subgroup.le_normalizer (x01_mem_E1 c))
  have h02 : ∀ c, f (x02 c) ∈ Γ := fun c => hN₁ _ (Subgroup.le_normalizer (x02_mem_E1 c))
  have h12 : ∀ c, f (x12 c) ∈ Γ := fun c => hN₁ _ (x12_mem_normalizer_E1 c)
  have h21 : ∀ c, f (x21 c) ∈ Γ := fun c => hN₁ _ (x21_mem_normalizer_E1 c)
  have h10 : ∀ c, f (x10 c) ∈ Γ := fun c => hN₂ _ (x10_mem_normalizer_E2 c)
  have h20 : ∀ c, f (x20 c) ∈ Γ := by
    intro c
    have hc : x20 c = ⁅x21 c, x10 (1 : F)⁆ := by
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) c (1 : F)
      rw [mul_one] at this
      exact this.symm
    rw [hc, map_commutatorElement, commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (h21 c) (h10 1)) (Γ.inv_mem (h21 c)))
      (Γ.inv_mem (h10 1))
  have hclosure : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) ≤ Γ.comap f := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    show f _ ∈ Γ
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact h01 c
      | exact h02 c
      | exact h12 c
      | exact h21 c
      | exact h10 c
      | exact h20 c
  rw [eq_top_iff]
  intro k _
  obtain ⟨x, rfl⟩ := hf k
  refine hclosure ?_
  rw [CFSG.LinearGroups.special_linear_elementary_generation]
  exact Subgroup.mem_top x

end Elementary

end LinThreeCore

theorem kFactLinThreeCore : KFactLinThreeCore := by
  intro K _ _ d ⟨e⟩ p hp _ ⟨q, hqp, hq1, hd⟩ T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have ε : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
  have hF : Nat.card (GaloisField q.p q.exponent) = p := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq1, hqp, pow_one]
  obtain ⟨P, hP, hcore⟩ := LinThreeCore.exists_pGroup_glbCore_eq_top hp hF
    (ε.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (ε.symm.surjective.comp (QuotientGroup.mk'_surjective _)) fun x hx =>
      (QuotientGroup.eq_one_iff x).mp (ε.symm.injective (hx.trans ε.symm.map_one.symm))
  exact glbCore_eq_top_of_pGroup hp 2 hP hcore T

end CFSG.AGLEmbeddingD2
