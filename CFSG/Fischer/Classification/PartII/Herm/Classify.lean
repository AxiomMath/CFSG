module

public import CFSG.Fischer.Classification.Unitary.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.ClassicalGroups.Unitary Module

namespace Herm

variable {K : Type*} [Field K] {σ : K ≃+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[(σ : K →+* K)] V →ₗ[K] K}

theorem form_smul_left (c : K) (x y : V) : B (c • x) y = σ c * B x y := by
  simp

theorem form_conj (hB : B.IsSymm) (x y : V) : B y x = σ (B x y) :=
  (hB.eq x y).symm

theorem eq_zero_of_forall_self (hσ : IsUnitaryInvolution σ) (hB : B.IsSymm)
    {S : Submodule K V} (hS : ∀ s ∈ S, B s s = 0) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    B a b = 0 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have h1 := hS (a + b) (S.add_mem ha hb)
  have h2 := hS (a + c • b) (S.add_mem ha (S.smul_mem c hb))
  have hba := form_conj hB a b
  simp only [map_add, LinearMap.add_apply, map_smul, form_smul_left, smul_eq_mul, hS a ha,
    hS b hb, hba] at h1 h2
  have h3 : (c - σ c) * B a b = 0 := by linear_combination h2 - σ c * h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hc
  · exact h

@[expose] def proj (B : V →ₛₗ[(σ : K →+* K)] V →ₗ[K] K) {k : ℕ} (b : Fin k → V) : V →ₗ[K] V :=
  LinearMap.id - ∑ i, (B (b i)).smulRight (b i)

theorem proj_apply {k : ℕ} (b : Fin k → V) (y : V) :
    proj B b y = y - ∑ i, B (b i) y • b i := by
  simp [proj]

theorem eq_proj_add_sum {k : ℕ} (b : Fin k → V) (y : V) :
    y = proj B b y + ∑ i, B (b i) y • b i := by
  rw [proj_apply, sub_add_cancel]

section Family

variable {k : ℕ} {b : Fin k → V} (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
include hb

theorem form_proj (j : Fin k) (y : V) : B (b j) (proj B b y) = 0 := by
  rw [proj_apply, map_sub, map_sum]
  simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, sub_self]

theorem form_proj_left (hB : B.IsSymm) (j : Fin k) (y : V) : B (proj B b y) (b j) = 0 := by
  rw [form_conj hB, form_proj hb, map_zero]

theorem exists_norm_one_perp (hσ : IsUnitaryInvolution σ) (hB : B.IsSymm)
    (hnd : B.SeparatingLeft) [FiniteDimensional K V] (hk : k < finrank K V) :
    ∃ x, (∀ i, B (b i) x = 0) ∧ B x x = 1 := by
  by_contra hne
  push Not at hne
  have hiso : ∀ y, B (proj B b y) (proj B b y) = 0 := by
    intro y
    by_contra hd
    obtain ⟨c, hc⟩ := hσ.norm_surj (B (proj B b y) (proj B b y))⁻¹
      (by rw [map_inv₀, ← form_conj hB]) (inv_ne_zero hd)
    apply hne (c • proj B b y) fun i => by rw [map_smul, form_proj hb, smul_zero]
    rw [form_smul_left, map_smul, smul_eq_mul, ← mul_assoc, hc, inv_mul_cancel₀ hd]
  have hpol : ∀ y y', B (proj B b y) (proj B b y') = 0 := fun y y' =>
    eq_zero_of_forall_self hσ hB (S := LinearMap.range (proj B b))
      (by rintro _ ⟨z, rfl⟩; exact hiso z) ⟨y, rfl⟩ ⟨y', rfl⟩
  have hP0 : ∀ y, proj B b y = 0 := by
    intro y
    refine hnd _ fun y' => ?_
    rw [eq_proj_add_sum (B := B) b y', (B (proj B b y)).map_add, hpol, map_sum]
    simp only [map_smul, form_proj_left hb hB, smul_zero, Finset.sum_const_zero, add_zero]
  have htop : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [eq_proj_add_sum (B := B) b y, hP0, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hle := finrank_range_le_card (R := K) b
  rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at hle
  omega

theorem linearIndependent_of_orthonormal : LinearIndependent K b := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (B (b i)) hg
  rw [map_sum, map_zero] at h
  simpa only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] using h

end Family

theorem exists_orthonormal_family (hσ : IsUnitaryInvolution σ) (hB : B.IsSymm)
    (hnd : B.SeparatingLeft) [FiniteDimensional K V] :
    ∀ k ≤ finrank K V, ∃ b : Fin k → V, ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hb⟩ := ih (by omega)
    obtain ⟨x, hxb, hxx⟩ := exists_norm_one_perp hb hσ hB hnd (by omega)
    refine ⟨Fin.snoc b x, fun i j => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hxx]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [form_conj hB, hxb j, map_zero, ite_eq_right (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hxb i, ite_eq_right (Fin.castSucc_lt_last i).ne]
      | cast j => simp only [Fin.snoc_castSucc, hb i j, Fin.castSucc_inj]

structure IsHermForm (σ : K ≃+* K) (h : V → V → K) : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (c : K) x y, h (c • x) y = σ c * h x y
  conj : ∀ x y, h y x = σ (h x y)

@[expose] def mkForm (hσ : ∀ c, σ (σ c) = c) {h : V → V → K} (hh : IsHermForm σ h) :
    V →ₛₗ[(σ : K →+* K)] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ _ _ h hh.add_left (fun c x y => by rw [hh.smul_left]; rfl)
    (fun x y y' => by rw [hh.conj, hh.add_left, map_add, ← hh.conj, ← hh.conj])
    (fun c x y => by rw [hh.conj, hh.smul_left, map_mul, hσ, ← hh.conj]; rfl)

theorem mkForm_apply (hσ : ∀ c, σ (σ c) = c) {h : V → V → K} (hh : IsHermForm σ h) (x y : V) :
    mkForm hσ hh x y = h x y :=
  rfl

theorem isSymm_mkForm (hσ : ∀ c, σ (σ c) = c) {h : V → V → K} (hh : IsHermForm σ h) :
    (mkForm hσ hh).IsSymm :=
  ⟨fun x y => (hh.conj x y).symm⟩

end Herm

open Herm

section General

variable {K : Type*} [Field K] {σ : K ≃+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_linearEquiv_herm (hσ : IsUnitaryInvolution σ)
    {B : V →ₛₗ[(σ : K →+* K)] V →ₗ[K] K} (hB : B.IsSymm) (hnd : B.SeparatingLeft) :
    ∃ e : V ≃ₗ[K] (Fin (finrank K V) → K), ∀ x y, herm σ (e x) (e y) = B x y := by
  obtain ⟨b, hb⟩ := exists_orthonormal_family hσ hB hnd _ le_rfl
  set β := basisOfLinearIndependentOfCardEqFinrank' b (linearIndependent_of_orthonormal hb)
    (Fintype.card_fin _)
  have hβ : ∀ i, β i = b i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  have key : ∀ c d : Fin (finrank K V) → K,
      B (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, σ (c i) * d i := by
    intro c d
    simp only [map_sum, LinearMap.sum_apply, form_smul_left, map_smul, smul_eq_mul, hb, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨β.equivFun, fun x y => ?_⟩
  have hx := β.sum_equivFun x
  have hy := β.sum_equivFun y
  simp only [hβ] at hx hy
  rw [herm_def, ← key (β.equivFun x) (β.equivFun y), hx, hy]

theorem exists_linearEquiv_herm_of_finrank (hσ : IsUnitaryInvolution σ)
    {B : V →ₛₗ[(σ : K →+* K)] V →ₗ[K] K} (hB : B.IsSymm) (hnd : B.SeparatingLeft) {m : ℕ}
    (hm : finrank K V = m) : ∃ e : V ≃ₗ[K] (Fin m → K), ∀ x y, herm σ (e x) (e y) = B x y := by
  subst hm
  exact exists_linearEquiv_herm hσ hB hnd

theorem exists_linearEquiv_herm_of_form (hσ : IsUnitaryInvolution σ) {h : V → V → K}
    (hh : IsHermForm σ h) (nondeg : ∀ x, (∀ y, h x y = 0) → x = 0) {m : ℕ}
    (hm : finrank K V = m) : ∃ e : V ≃ₗ[K] (Fin m → K), ∀ x y, herm σ (e x) (e y) = h x y :=
  exists_linearEquiv_herm_of_finrank hσ (isSymm_mkForm hσ.invol hh) nondeg hm

end General

section F4

open CFSG.Fischer.Classification.Unitary CFSG.Open
open CFSG.Blueprint.Fischer (K)

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_linearEquiv_herm_frob {B : W →ₛₗ[(frob : K →+* K)] W →ₗ[K] K} (hB : B.IsSymm)
    (hnd : B.SeparatingLeft) {m : ℕ} (hm : finrank K W = m) :
    ∃ e : W ≃ₗ[K] (Fin m → K), ∀ x y, herm frob (e x) (e y) = B x y :=
  exists_linearEquiv_herm_of_finrank isUnitaryInvolution_frob hB hnd hm

theorem exists_linearEquiv_fischerHermitianF4 (h : W → W → K)
    (add_left : ∀ x x' y, h (x + x') y = h x y + h x' y)
    (smul_left : ∀ (c : K) x y, h (c • x) y = c * h x y) (conj : ∀ x y, h y x = h x y ^ 2)
    (nondeg : ∀ x, (∀ y, h x y = 0) → x = 0) {m : ℕ} (hm : finrank K W = m) :
    ∃ e : W ≃ₗ[K] (Fin m → K), ∀ x y, fischerHermitianF4 m (e x) (e y) = h x y := by
  have hc : ∀ x y, h y x = frob (h x y) := fun x y => by rw [frob_apply, conj]
  obtain ⟨e, he⟩ := exists_linearEquiv_herm_of_form isUnitaryInvolution_frob
    (h := fun x y => h y x)
    ⟨fun x x' y => by rw [hc x, hc x', hc (x + x'), add_left, map_add],
      fun c x y => by rw [hc x, hc (c • x), smul_left, map_mul], fun x y => hc y x⟩
    (fun x hx => nondeg x fun y => by rw [hc, hx y, map_zero]) hm
  exact ⟨e, fun x y => by rw [fischerHermitianF4_eq_herm, he]⟩

end F4

end CFSG.Fischer.Classification
