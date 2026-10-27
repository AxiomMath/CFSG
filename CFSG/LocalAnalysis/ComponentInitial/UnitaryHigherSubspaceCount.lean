module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

universe u

variable {p f : ℕ} {K : Type*} [Field K]

section Fiber

variable {V : Type u} [AddCommGroup V] [Module K V] {σ : K →+* K}

abbrev TotIsoSubspaces (B : V →ₛₗ[σ] V →ₗ[K] K) (k : ℕ) : Type u :=
  {W : Submodule K V // Module.finrank K W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B x y = 0}

abbrev pairOrth (B : V →ₛₗ[σ] V →ₗ[K] K) (a b : V) : Submodule K V :=
  (Submodule.span K {a, b}).orthogonalBilin B

variable {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem sup_isotropic {a : V} (haa : B a a = 0) {M : Submodule K V}
    (hM : ∀ x ∈ M, ∀ y ∈ M, B x y = 0) (haM : ∀ x ∈ M, B a x = 0) (hMa : ∀ x ∈ M, B x a = 0) :
    ∀ x ∈ K ∙ a ⊔ M, ∀ y ∈ K ∙ a ⊔ M, B x y = 0 := by
  intro x hx y hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
  simp [haa, haM y₂ hy₂, hMa x₂ hx₂, hM x₂ hx₂ y₂ hy₂]

variable [FiniteDimensional K V] {a b : V}

noncomputable def isoFiberEquiv (ha0 : a ≠ 0) (haa : B a a = 0) (hba : B b a = 1)
    (hUa : ∀ x ∈ pairOrth B a b, B x a = 0) (k : ℕ) :
    {W : TotIsoSubspaces B (k + 1) // a ∈ W.1} ≃
      TotIsoSubspaces (B.domRestrict₁₂ (pairOrth B a b) (pairOrth B a b)) k where
  toFun W := ⟨W.1.1.comap (pairOrth B a b).subtype, by
      have : Module.finrank K ↥(W.1.1 ⊓ pairOrth B a b) + 1 = Module.finrank K W.1.1 :=
        finrank_inf_orthogonal_add_one ha0 hba W.2 fun x hx => W.1.2.2 a W.2 x hx
      rw [W.1.2.1] at this
      rw [finrank_comap_subtype]
      omega,
    fun x hx y hy => W.1.2.2 _ hx _ hy⟩
  invFun W' := ⟨⟨K ∙ a ⊔ W'.1.map (pairOrth B a b).subtype, by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a)
        (W'.1.map (pairOrth B a b).subtype)
      have h0 : K ∙ a ⊓ W'.1.map (pairOrth B a b).subtype = ⊥ :=
        eq_bot_iff.mpr ((inf_le_inf_left _ (Submodule.map_subtype_le _ _)).trans
          (span_inf_orthogonal_eq_bot hba).le)
      rw [h0, finrank_bot, finrank_span_singleton ha0,
        ← (Submodule.equivMapOfInjective _ (pairOrth B a b).injective_subtype _).finrank_eq,
        W'.2.1] at h1
      omega,
    sup_isotropic haa
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact W'.2.2 x hx y hy)
      (by
        rintro _ ⟨x, -, rfl⟩
        exact (Submodule.mem_orthogonalBilin.mp x.2) a (Submodule.subset_span (by simp)))
      (by
        rintro _ ⟨x, -, rfl⟩
        exact hUa x x.2)⟩,
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)⟩
  left_inv W := by
    refine Subtype.ext (Subtype.ext ?_)
    change K ∙ a ⊔ (W.1.1.comap (pairOrth B a b).subtype).map (pairOrth B a b).subtype = W.1.1
    rw [Submodule.map_comap_subtype, inf_comm]
    exact (eq_span_sup_inf_orthogonal hba W.2 fun x hx => W.1.2.2 a W.2 x hx).symm
  right_inv W' := by
    refine Subtype.ext (le_antisymm (fun x hx => ?_) fun x hx =>
      Submodule.mem_sup_right ⟨x, hx, rfl⟩)
    obtain ⟨x₁, hx₁, x₂, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hx
    have hx₁U : x₁ ∈ pairOrth B a b := by
      rw [eq_sub_of_add_eq (show x₁ + (y : V) = x from hsum)]
      exact Submodule.sub_mem _ x.2 y.2
    have hx₁0 : x₁ = 0 := by
      have := (span_inf_orthogonal_eq_bot (B := B) hba).le ⟨hx₁, hx₁U⟩
      exact (Submodule.mem_bot K).mp this
    rw [hx₁0, zero_add] at hsum
    rw [show x = y from Subtype.ext hsum.symm]
    exact hy

end Fiber

theorem card_nonzero_mem (h : UnitaryFieldData p f K) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) :
    Nat.card {x : V // x ≠ 0 ∧ x ∈ W} + 1 = (p ^ f) ^ (2 * Module.finrank K W) := by
  have := h.finite
  have : Finite V := Module.finite_of_finite K
  have hset : {x : V | x ≠ 0 ∧ x ∈ W} = (W : Set V) \ {0} := by
    ext x
    simp [and_comm]
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset,
    Set.ncard_sdiff_singleton_add_one (W.zero_mem) (Set.toFinite _), ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := K), h.card, ← pow_mul, ← pow_mul]
  ring_nf

theorem isoSubspaceCount_formula (h : UnitaryFieldData p f K) (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft → ∀ {n : ℕ},
      Module.finrank K V = n → 2 * k ≤ n →
      (Nat.card (TotIsoSubspaces B k) : ℤ) *
          ∏ i ∈ Finset.Icc 1 k, (((p ^ f : ℕ) : ℤ) ^ (2 * i) - 1) =
        ∏ j ∈ Finset.range k, ((((p ^ f : ℕ) : ℤ) ^ (n - 2 * j) - (-1) ^ (n - 2 * j)) *
          (((p ^ f : ℕ) : ℤ) ^ (n - 2 * j - 1) - (-1) ^ (n - 2 * j - 1))) := by
  induction k with
  | zero =>
    intro V _ _ _ B _ _ n _ _
    have hcard : Nat.card (TotIsoSubspaces B 0) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨⊥, finrank_bot K V, fun x hx y _ => by
        rw [(Submodule.mem_bot K).mp hx, map_zero, LinearMap.zero_apply]⟩, fun W => ?_⟩
      exact Subtype.ext (Submodule.finrank_eq_zero.mp W.2.1)
    simp [hcard]
  | succ k ih =>
    intro V _ _ _ B hB hBl n hn hk
    classical
    have := h.finite
    have : Finite V := Module.finite_of_finite K
    have : Fintype (TotIsoSubspaces B (k + 1)) := Fintype.ofFinite _
    have : Fintype {a : V // a ≠ 0 ∧ B a a = 0} := Fintype.ofFinite _
    set q : ℤ := ((p ^ f : ℕ) : ℤ) with hq
    set P : ℤ := ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1) with hP
    set R : ℤ := ∏ j ∈ Finset.range k, ((q ^ (n - 2 - 2 * j) - (-1) ^ (n - 2 - 2 * j)) *
      (q ^ (n - 2 - 2 * j - 1) - (-1) ^ (n - 2 - 2 * j - 1))) with hR
    have hsig : Nat.card (Σ W : TotIsoSubspaces B (k + 1), {x : V // x ≠ 0 ∧ x ∈ W.1}) =
        Nat.card (Σ a : {a : V // a ≠ 0 ∧ B a a = 0},
          {W : TotIsoSubspaces B (k + 1) // a.1 ∈ W.1}) :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.2.1, x.2.2.1, x.1.2.2 _ x.2.2.2 _ x.2.2.2⟩, ⟨x.1, x.2.2.2⟩⟩
          invFun := fun y => ⟨y.2.1, ⟨y.1.1, y.1.2.1, y.2.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [Nat.card_sigma, Nat.card_sigma] at hsig
    have hleft : ∀ W : TotIsoSubspaces B (k + 1),
        Nat.card {x : V // x ≠ 0 ∧ x ∈ W.1} = (p ^ f) ^ (2 * (k + 1)) - 1 := fun W => by
      have := card_nonzero_mem h W.1
      rw [W.2.1] at this
      omega
    have hfiber : ∀ a : {a : V // a ≠ 0 ∧ B a a = 0},
        (Nat.card {W : TotIsoSubspaces B (k + 1) // a.1 ∈ W.1} : ℤ) * P = R := by
      intro a
      obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl a.2.1 a.2.2
      obtain ⟨-, -, -, hUsep, hUdim⟩ := hsplit b hab hbb
      have hba : B b a.1 = 1 := by rw [← hB.eq a.1 b, hab, map_one]
      have hUa : ∀ x ∈ pairOrth B a.1 b, B x a.1 = 0 := fun x hx => by
        rw [← hB.eq a.1 x,
          (Submodule.mem_orthogonalBilin.mp hx) a.1 (Submodule.subset_span (by simp)), map_zero]
      rw [Nat.card_congr (isoFiberEquiv a.2.1 a.2.2 hba hUa k)]
      have := ih (hB.domRestrict _) hUsep (n := n - 2) (by rw [hUdim, hn]) (by omega)
      rw [this, hR]
    have hiso := (unitary_hermitian_vector_count h hB hBl hn (by omega)).2.2
    simp only [hleft, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card] at hsig
    have hsigZ : (Nat.card (TotIsoSubspaces B (k + 1)) : ℤ) * (q ^ (2 * (k + 1)) - 1) =
        ∑ a : {a : V // a ≠ 0 ∧ B a a = 0},
          (Nat.card {W : TotIsoSubspaces B (k + 1) // a.1 ∈ W.1} : ℤ) := by
      have hpos : 1 ≤ (p ^ f) ^ (2 * (k + 1)) :=
        Nat.one_le_pow _ _ (pow_pos h.prime.pos _)
      have := congrArg (fun m : ℕ => (m : ℤ)) hsig
      push_cast [Nat.cast_sub hpos] at this
      rw [hq]
      exact this
    rw [← hq] at hiso
    have hshift : ∏ j ∈ Finset.range k, ((q ^ (n - 2 * (j + 1)) - (-1) ^ (n - 2 * (j + 1))) *
        (q ^ (n - 2 * (j + 1) - 1) - (-1) ^ (n - 2 * (j + 1) - 1))) = R :=
      Finset.prod_congr rfl fun j _ => by
        rw [show n - 2 * (j + 1) = n - 2 - 2 * j by omega]
    rw [Finset.prod_Icc_succ_top (by omega), ← hP, Finset.prod_range_succ', hshift]
    simp only [mul_zero, Nat.sub_zero]
    calc (Nat.card (TotIsoSubspaces B (k + 1)) : ℤ) * (P * (q ^ (2 * (k + 1)) - 1))
        = (Nat.card (TotIsoSubspaces B (k + 1)) : ℤ) * (q ^ (2 * (k + 1)) - 1) * P := by ring
      _ = ∑ a : {a : V // a ≠ 0 ∧ B a a = 0},
          (Nat.card {W : TotIsoSubspaces B (k + 1) // a.1 ∈ W.1} : ℤ) * P := by
        rw [hsigZ, Finset.sum_mul]
      _ = ∑ _a : {a : V // a ≠ 0 ∧ B a a = 0}, R := Finset.sum_congr rfl fun a _ => hfiber a
      _ = R * ((q ^ n - (-1) ^ n) * (q ^ (n - 1) - (-1) ^ (n - 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hiso,
          mul_comm]

theorem isotropic_subspace_count (h : UnitaryFieldData p f K) {V : Type u} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : Module.finrank K V = n) (k : ℕ) :
    (n < 2 * k → Nat.card (TotIsoSubspaces B k) = 0) ∧
    (2 * k ≤ n → (Nat.card (TotIsoSubspaces B k) : ℤ) *
          ∏ i ∈ Finset.Icc 1 k, (((p ^ f : ℕ) : ℤ) ^ (2 * i) - 1) =
        ∏ j ∈ Finset.range k, ((((p ^ f : ℕ) : ℤ) ^ (n - 2 * j) - (-1) ^ (n - 2 * j)) *
          (((p ^ f : ℕ) : ℤ) ^ (n - 2 * j - 1) - (-1) ^ (n - 2 * j - 1)))) ∧
    Nat.card (TotIsoSubspaces B 0) = 1 := by
  refine ⟨fun hk => ?_, isoSubspaceCount_formula h k hB hBl hn, ?_⟩
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun W => ?_⟩
    obtain ⟨Wc, hWc, -⟩ := exists_isotropicChain_eq W.1 W.2.2
    rw [W.2.1] at hWc
    have hk' := (exists_hypBasis_of_isotropicChain h k hB hBl (r := n / 2)
      (ε := n - 2 * (n / 2)) (by omega) (by omega) Wc hWc).1
    omega
  · have := isoSubspaceCount_formula h 0 hB hBl hn (by omega)
    simpa using this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
