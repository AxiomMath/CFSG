module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem linearIndependent_of_hypGram {r ε : ℕ} {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}
    {v : HypIndex r ε → V} (hv : ∀ x y, B (v x) (v y) = hypGram r ε K x y) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg y
  have := congrArg (B (v (hypPartner y))) hg
  simp only [map_sum, map_smul, hv, hypGram_apply, hypPartner_hypPartner, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_zero] at this
  exact this

noncomputable def basisOfHypGram [FiniteDimensional K V] {r ε : ℕ} {σ : K →+* K}
    {B : V →ₛₗ[σ] V →ₗ[K] K} (v : HypIndex r ε → V)
    (hv : ∀ x y, B (v x) (v y) = hypGram r ε K x y) (hn : Module.finrank K V = 2 * r + ε) :
    Module.Basis (HypIndex r ε) K V :=
  basisOfLinearIndependentOfCardEqFinrank' v (linearIndependent_of_hypGram hv)
    (by simp only [Fintype.card_sum, Fintype.card_fin, hn]; omega)

theorem coe_basisOfHypGram [FiniteDimensional K V] {r ε : ℕ} {σ : K →+* K}
    {B : V →ₛₗ[σ] V →ₗ[K] K} (v : HypIndex r ε → V)
    (hv : ∀ x y, B (v x) (v y) = hypGram r ε K x y) (hn : Module.finrank K V = 2 * r + ε) :
    ⇑(basisOfHypGram v hv hn) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

theorem exists_bar_mul_eq_neg_one (h : UnitaryFieldData p f K) : ∃ u : K, h.bar u * u = -1 := by
  obtain ⟨u, hu⟩ := h.normHom_surjective (-1)
  refine ⟨u, ?_⟩
  have := congrArg Subtype.val hu
  rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
  rw [mul_comm, this]
  rfl

theorem exists_add_bar_eq_neg_one (h : UnitaryFieldData p f K) : ∃ c : K, c + h.bar c = -1 := by
  obtain ⟨c, hc⟩ := h.traceLin_surjective (-1)
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  rw [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
  rw [this]
  rfl

theorem exists_hypBasis (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r ε : ℕ}
    (hn : Module.finrank K V = 2 * r + ε) :
    ∃ w : Module.Basis (HypIndex r ε) K V, ∀ x y, B (w x) (w y) = hypGram r ε K x y := by
  classical
  obtain ⟨o₀, ho₀⟩ := h.exists_orthonormal_basis hB hBl
  have hcard : Fintype.card (HypIndex r ε) = Fintype.card (Fin (Module.finrank K V)) := by
    simp only [Fintype.card_sum, Fintype.card_fin, hn]
    omega
  let e : HypIndex r ε ≃ Fin (Module.finrank K V) := Fintype.equivOfCardEq hcard
  let o : HypIndex r ε → V := fun x => o₀ (e x)
  have ho : ∀ x y, B (o x) (o y) = if x = y then 1 else 0 := fun x y => by
    simp only [o, ho₀, e.injective.eq_iff]
  obtain ⟨u, hu⟩ := exists_bar_mul_eq_neg_one h
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  let v : HypIndex r ε → V
    | .inl i => o (.inl i) + u • o (.inr (.inr i))
    | .inr (.inl k) => o (.inr (.inl k))
    | .inr (.inr i) => (1 + c) • o (.inl i) + (c * u) • o (.inr (.inr i))
  have hv : ∀ x y, B (v x) (v y) = hypGram r ε K x y := by
    intro x y
    rcases x with i | k | i <;> rcases y with j | l | j <;>
      simp only [v, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ho, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, mul_ite, mul_one,
        mul_zero, add_zero, zero_add, map_mul, map_one, RingHom.id_apply, hypGram_inl_inl,
        hypGram_inl_inr_inl, hypGram_inl_inr_inr, hypGram_inr_inl_inl, hypGram_inr_inl_inr_inl,
        hypGram_inr_inl_inr_inr, hypGram_inr_inr_inl, hypGram_inr_inr_inr_inl,
        hypGram_inr_inr_inr_inr] <;>
      split_ifs <;>
      first | linear_combination | linear_combination hu | linear_combination c * hu |
        linear_combination h.bar c * hu | linear_combination hc + c * h.bar c * hu
  exact ⟨basisOfHypGram v hv hn, fun x y => by rw [coe_basisOfHypGram, hv]⟩

theorem exists_hypBasis_of_pair (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r ε : ℕ}
    (hn : Module.finrank K V = 2 * r + ε) (hr : 0 < r) {a b : V} (ha : B a a = 0)
    (hb : B b b = 0) (hab : B a b = 1) :
    ∃ w : Module.Basis (HypIndex r ε) K V, (∀ x y, B (w x) (w y) = hypGram r ε K x y) ∧
      w (.inl ⟨0, hr⟩) = a ∧ w (.inr (.inr ⟨0, hr⟩)) = b := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hab
  obtain ⟨-, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
  obtain ⟨-, -, -, hWsep, hWdim⟩ := hsplit b hab hb
  set W := (Submodule.span K {a, b}).orthogonalBilin B with hW
  obtain ⟨w', hw'⟩ := exists_hypBasis h (hB.domRestrict W) hWsep (r := r) (ε := ε)
    (by rw [hWdim, hn]; omega)
  have hw'' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y := fun x y => by
    rw [← hw' x y, LinearMap.domRestrict₁₂_apply]
  have haW : ∀ x : W, B a x = 0 := fun x =>
    (Submodule.mem_orthogonalBilin.mp x.2) a (Submodule.subset_span (by simp))
  have hbW : ∀ x : W, B b x = 0 := fun x =>
    (Submodule.mem_orthogonalBilin.mp x.2) b (Submodule.subset_span (by simp))
  have hWa : ∀ x : W, B x a = 0 := fun x => by rw [← hB.eq a x, haW, map_zero]
  have hWb : ∀ x : W, B x b = 0 := fun x => by rw [← hB.eq b x, hbW, map_zero]
  have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
  let v : HypIndex (r + 1) ε → V
    | .inl i => Fin.cases a (fun j => (w' (.inl j) : V)) i
    | .inr (.inl k) => (w' (.inr (.inl k)) : V)
    | .inr (.inr i) => Fin.cases b (fun j => (w' (.inr (.inr j)) : V)) i
  have hv : ∀ x y, B (v x) (v y) = hypGram (r + 1) ε K x y := by
    intro x y
    rcases x with i | k | i <;> rcases y with j | l | j <;>
      [cases i using Fin.cases <;> cases j using Fin.cases;
       cases i using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases;
       cases j using Fin.cases;
       skip;
       cases j using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases;
       cases i using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases] <;>
      simp [v, ha, hb, hab, hba, haW, hbW, hWa, hWb, hw'', Fin.succ_ne_zero,
        (Fin.succ_ne_zero _).symm]
  refine ⟨basisOfHypGram v hv hn, fun x y => by rw [coe_basisOfHypGram, hv], ?_, ?_⟩ <;>
    rw [coe_basisOfHypGram] <;> rfl

theorem hermitian_witt_basis (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {n : ℕ}
    (hn : Module.finrank K V = n) :
    (∃ w : Module.Basis (HypIndex (n / 2) (n - 2 * (n / 2))) K V,
      ∀ x y, B (w x) (w y) = hypGram (n / 2) (n - 2 * (n / 2)) K x y) ∧
    (2 ≤ n → ∃ v : V, v ≠ 0 ∧ B v v = 0) ∧
    (n = 2 → ∃ a b : V, B a a = 0 ∧ B b b = 0 ∧ B a b = 1 ∧ Submodule.span K {a, b} = ⊤) ∧
    ∀ a b : V, B a a = 0 → B b b = 0 → B a b = 1 → ∃ hr : 0 < n / 2,
      ∃ w : Module.Basis (HypIndex (n / 2) (n - 2 * (n / 2))) K V,
        (∀ x y, B (w x) (w y) = hypGram (n / 2) (n - 2 * (n / 2)) K x y) ∧
        w (.inl ⟨0, hr⟩) = a ∧ w (.inr (.inr ⟨0, hr⟩)) = b := by
  have hn' : Module.finrank K V = 2 * (n / 2) + (n - 2 * (n / 2)) := by omega
  obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl hn'
  have hiso : 2 ≤ n → ∃ v : V, v ≠ 0 ∧ B v v = 0 := fun h2 => by
    have hr : 0 < n / 2 := by omega
    refine ⟨w (.inl ⟨0, hr⟩), w.ne_zero _, ?_⟩
    rw [hw, hypGram_inl_inl]
  refine ⟨⟨w, hw⟩, hiso, fun h2 => ?_, fun a b ha hb hab => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hiso h2.ge
    obtain ⟨⟨b, hab, hb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
    obtain ⟨hH, -⟩ := hsplit b hab hb
    exact ⟨a, b, ha, hb, hab, Submodule.eq_top_of_finrank_eq (by rw [hH, hn, h2])⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hab
    obtain ⟨-, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
    obtain ⟨hH, -⟩ := hsplit b hab hb
    have h2 : 2 ≤ n := by
      rw [← hH, ← hn]
      exact Submodule.finrank_le _
    have hr : 0 < n / 2 := by omega
    exact ⟨hr, exists_hypBasis_of_pair h hB hBl hn' hr ha hb hab⟩

end CFSG.ClassicalGroups.UnitaryFlag
