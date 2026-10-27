module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDiag
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt Polynomial

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V]

section PBlk

@[expose] noncomputable def pblk (π T : Module.End K V) : Module.End K V := 1 - π + T * π

theorem pblk_apply (π T : Module.End K V) (v : V) : pblk π T v = v - π v + T (π v) := rfl

variable {π : Module.End K V} (hπ : ∀ v, π (π v) = π v)
include hπ

theorem pblk_pblk_apply {T' : Module.End K V} (hT' : ∀ v, π (T' v) = T' (π v))
    (T : Module.End K V) (v : V) : pblk π T (pblk π T' v) = pblk π (T * T') v := by
  have h : π (pblk π T' v) = T' (π v) := by
    rw [pblk_apply, map_add, map_sub, hπ, sub_self, zero_add, hT', hπ]
  rw [pblk_apply, h, pblk_apply, pblk_apply, Module.End.mul_apply]
  abel

theorem pblk_pow_apply {T : Module.End K V} (hT : ∀ v, π (T v) = T (π v)) (n : ℕ) (v : V) :
    (pblk π T ^ n) v = pblk π (T ^ n) v := by
  have hTn : ∀ m : ℕ, ∀ v, π ((T ^ m) v) = (T ^ m) (π v) := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  induction n generalizing v with
  | zero => simp [pblk_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pblk_pblk_apply hπ (hTn n), ← pow_succ']

theorem pblk_pow_eq_one {T : Module.End K V} (hT : ∀ v, π (T v) = T (π v)) {n : ℕ}
    (hTn : T ^ n = 1) : pblk π T ^ n = 1 :=
  LinearMap.ext fun v => by
    rw [pblk_pow_apply hπ hT, hTn, pblk_apply, Module.End.one_apply, Module.End.one_apply,
      sub_add_cancel]

@[expose] noncomputable def pblkEquiv {T : Module.End K V} (hT : ∀ v, π (T v) = T (π v))
    {n : ℕ} (hn : 0 < n) (hTn : T ^ n = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (pblk π T) (pblk π T ^ (n - 1))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hn,
        pblk_pow_eq_one hπ hT hTn]
      rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel hn,
        pblk_pow_eq_one hπ hT hTn]
      rfl)

theorem pblkEquiv_pow_apply {T : Module.End K V} (hT : ∀ v, π (T v) = T (π v)) {n : ℕ}
    (hn : 0 < n) (hTn : T ^ n = 1) (m : ℕ) (v : V) :
    (pblkEquiv hπ hT hn hTn ^ m) v = (pblk π T ^ m) v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', Module.End.mul_apply]
    rfl

end PBlk

theorem eq_zero_of_apply_eq_neg {g : Module.End K V} {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1)
    (h2 : (2 : K) ≠ 0) {v : V} (hv : g v = -v) : v = 0 := by
  have hpow : ∀ m : ℕ, (g ^ m) v = (-1 : K) ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, pow_succ, mul_smul,
        neg_one_smul]
  have h := hpow n
  rw [hgn, Module.End.one_apply, hn.neg_one_pow, neg_one_smul] at h
  have h2v : (2 : K) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel v
  exact (smul_eq_zero.mp h2v).resolve_left h2

section Plane

variable [Fintype K] [DecidableEq K] [Finite A]
variable (β : LinearMap.BilinForm K V) (ρ : Representation K A V)
variable (hA : ∀ a : A, a ^ p = 1)

include hA in
theorem trace_pow_card [Nontrivial V] (hq : p ∣ Fintype.card K - 1 ∨ p ∣ Fintype.card K + 1)
    (x : A) : (ρ x + ρ x⁻¹) ^ Fintype.card K = ρ x + ρ x⁻¹ := by
  obtain ⟨ℓ, hchar, n, hℓ, hcard⟩ := FiniteField.card' K
  haveI := hchar
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP (Module.End K V) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K V)).injective ℓ
  have hcomm : Commute (ρ x) (ρ x⁻¹) := by
    show ρ x * ρ x⁻¹ = ρ x⁻¹ * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hx : (x ^ Fintype.card K = x ∧ x⁻¹ ^ Fintype.card K = x⁻¹) ∨
      (x ^ Fintype.card K = x⁻¹ ∧ x⁻¹ ^ Fintype.card K = x) := by
    rcases hq with ⟨m, hm⟩ | ⟨m, hm⟩
    · have e : Fintype.card K = p * m + 1 := by
        have := Fintype.card_pos (α := K)
        omega
      have h : ∀ y : A, y ^ Fintype.card K = y := fun y => by
        rw [e, pow_succ, pow_mul, hA, one_pow, one_mul]
      exact Or.inl ⟨h x, h x⁻¹⟩
    · have h : ∀ y : A, y ^ Fintype.card K = y⁻¹ := fun y => by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hm, pow_mul, hA, one_pow]
      exact Or.inr ⟨h x, by rw [h, inv_inv]⟩
  rw [hcard, add_pow_char_pow_of_commute ℓ (n : ℕ) hcomm, ← map_pow, ← map_pow, ← hcard]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

variable (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hρ : IsIsomRep β ρ)
variable (hsymm : ∀ u v, β u v = β v u) (h2 : (2 : K) ≠ 0)

include hp hp2 hA hpK hρ hsymm h2 in
theorem finrank_weightSpace_eq_two [FiniteDimensional K V] (hβ : β.SeparatingLeft)
    (hmax : IsMaxElem β ρ p ∅) (hq : p ∣ Fintype.card K - 1 ∨ p ∣ Fintype.card K + 1)
    (H : Hyperplane A p) (hH : weightSpace ρ H.1 ≠ ⊥) :
    Module.finrank K (weightSpace ρ H.1) = 2 := by
  classical
  obtain ⟨v₁, hv₁W, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
  haveI : Nontrivial V := ⟨⟨v₁, 0, hv₁0⟩⟩
  obtain ⟨x, hx⟩ := exists_not_mem_hyperplane hp H
  have hfix : ∀ v ∈ weightSpace ρ H.1, ρ x v = v → v = 0 := fun v hv h =>
    eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK hx hv h
  have hWinv : ∀ (a : A), ∀ v ∈ weightSpace ρ H.1, ρ a v ∈ weightSpace ρ H.1 :=
    fun a v hv => apply_mem_weightSpace ρ H.1 a hv
  have hxp : ρ x ^ p = 1 := by rw [← map_pow, hA, map_one]
  have hinvx : ∀ v, ρ x (ρ x⁻¹ v) = v := fun v => Representation.self_inv_apply ρ x v
  have hneg : ∀ v ∈ weightSpace ρ H.1, ρ x v = -v → v = 0 := fun v _ h =>
    eq_zero_of_apply_eq_neg (hp.odd_of_ne_two hp2) hxp h2 h
  have hsq : (ρ x + ρ x⁻¹) ^ Fintype.card K = ρ x + ρ x⁻¹ := trace_pow_card ρ hA hq x
  have hsW : ∀ v ∈ weightSpace ρ H.1, (ρ x + ρ x⁻¹) v ∈ weightSpace ρ H.1 :=
    fun v hv => (weightSpace ρ H.1).add_mem (hWinv x v hv) (hWinv x⁻¹ v hv)
  have hsadj : ∀ u v, β ((ρ x + ρ x⁻¹) u) v = β u ((ρ x + ρ x⁻¹) v) := by
    intro u v
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add, LinearMap.add_apply,
      apply_left β ρ hρ x u v, apply_left β ρ hρ x⁻¹ u v, inv_inv, add_comm]
  obtain ⟨c, w₀, hw₀W, hw₀0, hsw₀⟩ := exists_eigenvector (ρ x + ρ x⁻¹) hsq _ hsW hH
  set E : Submodule K V := weightSpace ρ H.1 ⊓ Module.End.eigenspace (ρ x + ρ x⁻¹) c with hE
  have hE0 : E ≠ ⊥ := fun h => hw₀0 (by
    have hmem : w₀ ∈ E := ⟨hw₀W, Module.End.mem_eigenspace_iff.mpr hsw₀⟩
    rw [h] at hmem
    exact hmem)
  have hEnd : ∀ u ∈ E, (∀ e ∈ E, β u e = 0) → u = 0 := by
    intro u hu he
    have hsu : (ρ x + ρ x⁻¹) u = c • u := Module.End.mem_eigenspace_iff.mp hu.2
    refine weightFamily_nondeg β ρ hρ hp hA hpK hβ (some H)
      (by rw [weightFamily_some]; exact hu.1) fun v hv => ?_
    rw [weightFamily_some] at hv
    rw [← lagProj_apply_of_eigen (ρ x + ρ x⁻¹) hsu, lagProj_left β _ _ hsadj c u v]
    exact he _ ⟨Polynomial.aeval_apply_smul_mem_of_le_comap hv _ _ fun v hv => hsW v hv,
      Module.End.mem_eigenspace_iff.mpr (apply_lagProj _ hsq c v)⟩
  obtain ⟨w, hwE, hww⟩ := exists_aniso β (fun u v => hsymm v u) h2 E hEnd hE0
  have hwW : w ∈ weightSpace ρ H.1 := hwE.1
  have hsw : ρ x w + ρ x⁻¹ w = c • w := Module.End.mem_eigenspace_iff.mp hwE.2
  have hw0 : w ≠ 0 := fun h => hww (by simp [h])
  have hyW : ρ x w ∈ weightSpace ρ H.1 := hWinv x w hwW
  have hrel : ρ x (ρ x w) = c • ρ x w - w := by
    have h := congrArg (ρ x) hsw
    rw [map_add, hinvx, map_smul] at h
    rw [eq_sub_iff_add_eq, h]
  have hyy : β (ρ x w) (ρ x w) = β w w := hρ x w w
  have h2b : c * β w w = 2 * β w (ρ x w) := by
    have e1 : β (ρ x w + ρ x⁻¹ w) w = c * β w w := by
      rw [hsw, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [map_add, LinearMap.add_apply, apply_left β ρ hρ x⁻¹ w w, inv_inv, hsymm (ρ x w) w]
      at e1
    rw [← e1]
    ring
  have hc2 : c ≠ 2 := by
    intro hc
    have hfixed : ρ x (ρ x w - w) = ρ x w - w := by
      rw [map_sub, hrel, hc, two_smul]
      abel
    have h0 := hfix _ ((weightSpace ρ H.1).sub_mem hyW hwW) hfixed
    exact hw0 (hfix w hwW (sub_eq_zero.mp h0))
  have hcn2 : c ≠ -2 := by
    intro hc
    have hinv : ρ x (ρ x w + w) = -(ρ x w + w) := by
      rw [map_add, hrel, hc, neg_smul, two_smul]
      abel
    have h0 := hneg _ ((weightSpace ρ H.1).add_mem hyW hwW) hinv
    exact hw0 (hneg w hwW (eq_neg_of_add_eq_zero_left h0))
  have hdet : β w w ^ 2 - β w (ρ x w) ^ 2 ≠ 0 := by
    have h4 : (4 : K) * (β w w ^ 2 - β w (ρ x w) ^ 2) = β w w ^ 2 * ((2 - c) * (2 + c)) := by
      have : (2 : K) * β w (ρ x w) = c * β w w := h2b.symm
      linear_combination (-(2 * β w (ρ x w)) - c * β w w) * this
    intro h0
    rw [h0, mul_zero] at h4
    rcases mul_eq_zero.mp h4.symm with h | h
    · exact hww (pow_eq_zero_iff two_ne_zero |>.mp h)
    · rcases mul_eq_zero.mp h with h | h
      · exact hc2 (sub_eq_zero.mp h).symm
      · exact hcn2 (eq_neg_of_add_eq_zero_right h)
  have hli : LinearIndependent K ![w, ρ x w] := by
    rw [LinearIndependent.pair_iff' hw0]
    intro t ht
    have hyy' : β (ρ x w) (ρ x w) = t ^ 2 * β w w := by
      rw [← ht]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have h3 : (t ^ 2 - 1) * β w w = 0 := by linear_combination hyy'.symm.trans hyy
    have ht2 : t ^ 2 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hww)
    rcases mul_self_eq_one_iff.mp (show t * t = 1 by rw [← pow_two]; exact ht2) with h | h
    · rw [h, one_smul] at ht
      exact hw0 (hfix w hwW ht.symm)
    · rw [h, neg_one_smul] at ht
      exact hw0 (hneg w hwW ht.symm)
  set U : Submodule K V := Submodule.span K (Set.range ![w, ρ x w]) with hU
  have hUmem : ∀ u, u ∈ U ↔ ∃ α γ : K, α • w + γ • ρ x w = u := by
    intro u
    rw [hU, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f 0, f 1, by simp [Fin.sum_univ_two]⟩
    · rintro ⟨α, γ, rfl⟩
      exact ⟨![α, γ], by simp [Fin.sum_univ_two]⟩
  have hwU : w ∈ U := (hUmem w).mpr ⟨1, 0, by simp⟩
  have hyU : ρ x w ∈ U := (hUmem _).mpr ⟨0, 1, by simp⟩
  have hUW : U ≤ weightSpace ρ H.1 := by
    intro u hu
    obtain ⟨α, γ, rfl⟩ := (hUmem u).mp hu
    exact (weightSpace ρ H.1).add_mem ((weightSpace ρ H.1).smul_mem α hwW)
      ((weightSpace ρ H.1).smul_mem γ hyW)
  have hUx : ∀ u ∈ U, ρ x u ∈ U := by
    intro u hu
    obtain ⟨α, γ, rfl⟩ := (hUmem u).mp hu
    refine (hUmem _).mpr ⟨-γ, α + γ * c, ?_⟩
    rw [map_add, map_smul, map_smul, hrel]
    module
  have hUa : ∀ (a : A), ∀ u ∈ U, ρ a u ∈ U := by
    have hpow : ∀ n : ℕ, ∀ u ∈ U, ρ (x ^ n) u ∈ U := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih =>
        intro u hu
        rw [pow_succ', map_mul, Module.End.mul_apply]
        exact hUx _ (ih u hu)
    intro a u hu
    obtain ⟨n, hn⟩ := exists_pow_of_weightSpace ρ hp hx a
    rw [hn u (hUW hu)]
    exact hpow n u hu
  have hrefl : β.IsRefl := fun u v h => (hsymm v u).trans h
  have hdisj : Disjoint U (β.orthogonal U) := by
    rw [Submodule.disjoint_def]
    intro u hu hu'
    obtain ⟨α, γ, rfl⟩ := (hUmem u).mp hu
    have e1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') w hwU
    have e2 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') (ρ x w) hyU
    simp only [map_add, map_smul, smul_eq_mul] at e1 e2
    rw [hsymm (ρ x w) w, hyy] at e2
    have hα : α * (β w w ^ 2 - β w (ρ x w) ^ 2) = 0 := by
      linear_combination β w w * e1 - β w (ρ x w) * e2
    have hγ : γ * (β w w ^ 2 - β w (ρ x w) ^ 2) = 0 := by
      linear_combination β w w * e2 - β w (ρ x w) * e1
    rw [(mul_eq_zero.mp hα).resolve_right hdet, (mul_eq_zero.mp hγ).resolve_right hdet,
      zero_smul, zero_smul, add_zero]
  have hcompl : IsCompl U (β.orthogonal U) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr hdisj
  set π : Module.End K V := Submodule.projection U (β.orthogonal U) hcompl with hπdef
  have hπU : ∀ v, π v ∈ U := fun v => Submodule.projection_apply_mem hcompl v
  have hπleft : ∀ u ∈ U, π u = u := fun u hu =>
    Submodule.projection_apply_of_mem_left hcompl hu
  have hπright : ∀ u ∈ β.orthogonal U, π u = 0 := fun u hu =>
    Submodule.projection_apply_of_mem_right hcompl hu
  have hπsub : ∀ v, v - π v ∈ β.orthogonal U := fun v => Submodule.sub_projection_mem hcompl v
  have hππ : ∀ v, π (π v) = π v := fun v => hπleft _ (hπU v)
  have horthU : ∀ (a : A), ∀ u ∈ β.orthogonal U, ρ a u ∈ β.orthogonal U := by
    intro a u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
    intro n hn
    have h := apply_left β ρ hρ a⁻¹ n u
    rw [inv_inv] at h
    rw [← h]
    exact hu _ (hUa a⁻¹ n hn)
  have hπρ : ∀ (a : A) (v : V), π (ρ a v) = ρ a (π v) := by
    intro a v
    have hv : ρ a v = ρ a (π v) + ρ a (v - π v) := by rw [← map_add, add_sub_cancel]
    rw [hv, map_add, hπleft _ (hUa a _ (hπU v)), hπright _ (horthU a _ (hπsub v)), add_zero]
  have horth : ∀ n ∈ U, ∀ m ∈ β.orthogonal U, β n m = 0 ∧ β m n = 0 := by
    intro n hn m hm
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hm) n hn
    exact ⟨h, (hsymm m n).trans h⟩
  have key : ∀ (a b c d : V), a ∈ U → c ∈ U → b ∈ β.orthogonal U → d ∈ β.orthogonal U →
      β (a + b) (c + d) = β a c + β b d := by
    intro a b c d ha hc hb hd
    simp only [map_add, LinearMap.add_apply]
    rw [(horth _ ha _ hd).1, (horth _ hc _ hb).2]
    ring
  have hπx : ∀ v, π (ρ x v) = ρ x (π v) := hπρ x
  set g : V ≃ₗ[K] V := pblkEquiv hππ hπx hp.pos hxp with hgdef
  have hgapp : ∀ v, g v = v - π v + ρ x (π v) := fun v => rfl
  have hg : ∀ u v, β (g u) (g v) = β u v := by
    intro u v
    have e1 : g u = ρ x (π u) + (u - π u) := by rw [hgapp]; abel
    have e2 : g v = ρ x (π v) + (v - π v) := by rw [hgapp]; abel
    have e3 : β u v = β (π u + (u - π u)) (π v + (v - π v)) := by
      rw [add_sub_cancel, add_sub_cancel]
    rw [e1, e2, key _ _ _ _ (hUx _ (hπU u)) (hUx _ (hπU v)) (hπsub u) (hπsub v),
      hρ x (π u) (π v), e3, key _ _ _ _ (hπU u) (hπU v) (hπsub u) (hπsub v)]
  have hgp : ∀ v, (g ^ p) v = v := by
    intro v
    rw [hgdef, pblkEquiv_pow_apply hππ hπx hp.pos hxp p v, pblk_pow_eq_one hππ hπx hxp,
      Module.End.one_apply]
  have hgA : ∀ (a : A) (v : V), g (ρ a v) = ρ a (g v) := by
    intro a v
    rw [hgapp, hgapp, hπρ a v, map_add, map_sub, rho_rho ρ x a, rho_rho ρ a x, mul_comm]
  have hgW : ∀ i : Option (Hyperplane A p), i ≠ some H →
      ∀ v ∈ weightFamily (p := p) ρ i, g v = v := by
    intro i hi v hv
    have hvo : v ∈ β.orthogonal U := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact weightFamily_orthogonal β ρ hρ hp hA hpK (Ne.symm hi)
        (by rw [weightFamily_some]; exact hUW hn) hv
    rw [hgapp, hπright v hvo, map_zero, sub_zero, add_zero]
  have hWU : weightSpace ρ H.1 ≤ U := by
    intro v hv
    by_contra hvU
    have hv0 : v - π v ≠ 0 := fun h => hvU (by
      rw [sub_eq_zero] at h
      rw [h]
      exact hπU v)
    have hv0W : v - π v ∈ weightSpace ρ H.1 := (weightSpace ρ H.1).sub_mem hv (hUW (hπU v))
    have hgv0 : g (v - π v) = v - π v := by
      rw [hgapp, hπright _ (hπsub v), map_zero, sub_zero, add_zero]
    have hg1 := eq_one_of_supported_of_fixed β ρ hp hA hpK hρ hmax H g hg hgp hgA
      (fun s hs => absurd hs (Set.notMem_empty s)) hgW hv0W hv0 hgv0
    have hgw : g w = ρ x w := by
      rw [hgapp, hπleft w hwU, sub_self, zero_add]
    rw [hg1] at hgw
    exact hw0 (hfix w hwW hgw.symm)
  have hUeq : weightSpace ρ H.1 = U := le_antisymm hWU hUW
  rw [hUeq, hU, finrank_span_eq_card hli, Fintype.card_fin]

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
