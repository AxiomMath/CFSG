module

public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.OddSolvableUnitary

open Polynomial Module Subgroup
open scoped commutatorElement

section Eigenspaces

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

theorem ker_aeval_prod_X_sub_C (b : Module.End F W) (s : Finset F) :
    LinearMap.ker (aeval b (∏ μ ∈ s, (X - C μ))) = ⨆ μ ∈ s, b.eigenspace μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, map_one]
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot]
    exact LinearMap.ker_id
  | insert a s has ih =>
    rw [Finset.prod_insert has, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih,
      Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun μ hμ =>
        isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 fun h => has (by rw [h]; exact hμ)).isUnit

theorem iSup_eigenspace_nthRootsFinset {r : ℕ} (hr : 0 < r) {ζ : F} (hζ : IsPrimitiveRoot ζ r)
    {b : Module.End F W} (hb : b ^ r = 1) :
    ⨆ μ ∈ nthRootsFinset r (1 : F), b.eigenspace μ = ⊤ := by
  rw [← ker_aeval_prod_X_sub_C, ← X_pow_sub_one_eq_prod hr hζ, map_sub, map_pow, aeval_X,
    map_one, hb, sub_self, LinearMap.ker_zero]

theorem finrank_eq_sum_finrank_eigenspace [FiniteDimensional F W] {r : ℕ} (hr : 0 < r) {ζ : F}
    (hζ : IsPrimitiveRoot ζ r) {b : Module.End F W} (hb : b ^ r = 1) :
    finrank F W = ∑ μ ∈ nthRootsFinset r (1 : F), finrank F (b.eigenspace μ) := by
  classical
  set s := nthRootsFinset r (1 : F)
  let E : s → Submodule F W := fun μ => b.eigenspace μ
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep b).comp Subtype.val_injective
  have htop : iSup E = ⊤ := by
    rw [← iSup_eigenspace_nthRootsFinset hr hζ hb, iSup_subtype']
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap E) hint).finrank_eq,
    Module.finrank_directSum, ← Finset.sum_coe_sort s]

theorem finrank_eq_mul_finrank_eigenspace_one [FiniteDimensional F W] {r : ℕ} (hr : 0 < r)
    {ζ : F} (hζ : IsPrimitiveRoot ζ r) {b c : Module.End F W} (hb : b ^ r = 1)
    (hc : Function.Injective c) (hcb : c * b = ζ • (b * c)) :
    finrank F W = r * finrank F (b.eigenspace 1) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hr.ne'
  have hmaps : ∀ μ : F, ∀ v ∈ b.eigenspace μ, c v ∈ b.eigenspace (ζ⁻¹ * μ) := by
    intro μ v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := congrArg (fun f : Module.End F W => f v) hcb
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hv, map_smul] at h
    rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  have hle : ∀ μ : F, finrank F (b.eigenspace μ) ≤ finrank F (b.eigenspace (ζ⁻¹ * μ)) := by
    intro μ
    refine LinearMap.finrank_le_finrank_of_injective (f := c.restrict (hmaps μ)) ?_
    intro v w hvw
    exact Subtype.ext (hc (congrArg Subtype.val hvw))
  have hmono : Monotone fun k : ℕ => finrank F (b.eigenspace (ζ⁻¹ ^ k)) :=
    monotone_nat_of_le_succ fun k => by
      have h := hle (ζ⁻¹ ^ k)
      rwa [← pow_succ'] at h
  have hall : ∀ μ ∈ nthRootsFinset r (1 : F),
      finrank F (b.eigenspace μ) = finrank F (b.eigenspace 1) := by
    intro μ hμ
    have : NeZero r := ⟨hr.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hζ.inv.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hr 1).1 hμ)
    have h1 : finrank F (b.eigenspace (ζ⁻¹ ^ i)) ≤ finrank F (b.eigenspace (ζ⁻¹ ^ r)) :=
      hmono hi.le
    have h2 : finrank F (b.eigenspace (ζ⁻¹ ^ 0)) ≤ finrank F (b.eigenspace (ζ⁻¹ ^ i)) :=
      hmono (Nat.zero_le i)
    rw [hζ.inv.pow_eq_one] at h1
    rw [pow_zero] at h2
    exact le_antisymm h1 h2
  rw [finrank_eq_sum_finrank_eigenspace hr hζ hb, Finset.sum_congr rfl hall, Finset.sum_const,
    hζ.card_nthRootsFinset, smul_eq_mul]

theorem finrank_eq_mul_finrank_inf_eigenspace_one [FiniteDimensional F W] {r : ℕ} (hr : 0 < r)
    {ζ : F} (hζ : IsPrimitiveRoot ζ r) {b c : Module.End F W} (hb : b ^ r = 1)
    (hc : Function.Injective c) (hcb : c * b = ζ • (b * c)) {U : Submodule F W}
    (hbU : ∀ u ∈ U, b u ∈ U) (hcU : ∀ u ∈ U, c u ∈ U) :
    finrank F U = r * finrank F (U ⊓ b.eigenspace 1 : Submodule F W) := by
  have h := finrank_eq_mul_finrank_eigenspace_one hr hζ (b := b.restrict hbU)
    (c := c.restrict hcU) ?_ ?_ ?_
  · rw [h]
    congr 1
    have heq : Module.End.eigenspace (b.restrict hbU) 1 =
        (U ⊓ b.eigenspace 1).comap U.subtype := by
      ext u
      rw [Module.End.mem_eigenspace_iff, one_smul, Submodule.mem_comap, Submodule.mem_inf,
        Module.End.mem_eigenspace_iff, one_smul, Subtype.ext_iff, LinearMap.coe_restrict_apply]
      exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
    rw [heq]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  · ext u
    rw [Module.End.pow_restrict, LinearMap.restrict_apply, Module.End.one_apply]
    simp [hb]
  · intro u v huv
    exact Subtype.ext (hc (congrArg Subtype.val huv))
  · ext u
    have h := congrArg (fun f : Module.End F W => f u) hcb
    simpa using h

end Eigenspaces

section Arithmetic

theorem two_mul_le_sub_one_mul_pow {r a : ℕ} (hr : 3 ≤ r) (ha : 1 ≤ a) :
    2 * a ≤ (r - 1) * r ^ (a - 1) := by
  induction a, ha using Nat.le_induction with
  | base => simp; omega
  | succ a ha ih =>
    rw [Nat.add_sub_cancel, show a = a - 1 + 1 by omega, pow_succ]
    rw [show a - 1 + 1 = a by omega] at *
    nlinarith

theorem pow_le_sub_one_mul_succ_pow {r a : ℕ} (hr : 2 ≤ r) (ha : 1 ≤ a) :
    r ^ (2 * a + 1) ≤ (r - 1) * (r + 1) ^ (2 * a) := by
  induction a, ha using Nat.le_induction with
  | base =>
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega]
    ring_nf
    nlinarith
  | succ a ha ih =>
    have h1 : r ^ (2 * (a + 1) + 1) = r ^ (2 * a + 1) * r ^ 2 := by ring
    have h2 : (r - 1) * (r + 1) ^ (2 * (a + 1)) = (r - 1) * (r + 1) ^ (2 * a) * (r + 1) ^ 2 := by
      ring
    rw [h1, h2]
    exact Nat.mul_le_mul ih (Nat.pow_le_pow_left (by omega) 2)

theorem card_bound {r a s Q : ℕ} (hr : 3 ≤ r) (ha : 1 ≤ a) (hs : r ^ (a - 1) ≤ s)
    (hQ : r + 1 ≤ Q) :
    r * (r ^ (2 * a) - 1) / (r - 1) * (Q ^ s - 1) < Q ^ (r * s) - 1 := by
  set M := r * (r ^ (2 * a) - 1) / (r - 1) with hM
  have hdvd : r - 1 ∣ r * (r ^ (2 * a) - 1) := by
    have := Nat.sub_dvd_pow_sub_pow r 1 (2 * a)
    rw [one_pow] at this
    exact this.mul_left r
  have hMr : (r - 1) * M = r * (r ^ (2 * a) - 1) := Nat.mul_div_cancel' hdvd
  have hr1 : 1 ≤ r ^ (2 * a) := Nat.one_le_pow _ _ (by omega)
  have hM1 : M < (r + 1) ^ (2 * a) := by
    have h := pow_le_sub_one_mul_succ_pow (r := r) (a := a) (by omega) ha
    have : (r - 1) * M < (r - 1) * (r + 1) ^ (2 * a) := by
      rw [hMr]
      calc r * (r ^ (2 * a) - 1) < r * r ^ (2 * a) := by
            apply Nat.mul_lt_mul_of_pos_left _ (by omega)
            omega
        _ = r ^ (2 * a + 1) := by ring
        _ ≤ _ := h
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have hexp : 2 * a ≤ (r - 1) * s :=
    (two_mul_le_sub_one_mul_pow hr ha).trans (Nat.mul_le_mul_left _ hs)
  have hQ1 : 1 ≤ Q := by omega
  have hM2 : M < Q ^ ((r - 1) * s) :=
    hM1.trans_le ((Nat.pow_le_pow_left hQ _).trans (Nat.pow_le_pow_right hQ1 hexp))
  have hs1 : 1 ≤ s := (Nat.one_le_pow _ _ (by omega)).trans hs
  have hQs : 2 ≤ Q ^ s := (Nat.pow_le_pow_left (show 2 ≤ Q by omega) s).trans' (by
    simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hs1)
  have hsplit : Q ^ (r * s) = Q ^ ((r - 1) * s) * Q ^ s := by
    rw [← pow_add]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hpos : 1 ≤ Q ^ ((r - 1) * s) := Nat.one_le_pow _ _ (by omega)
  calc M * (Q ^ s - 1) < Q ^ ((r - 1) * s) * (Q ^ s - 1) :=
        Nat.mul_lt_mul_of_pos_right hM2 (by omega)
    _ = Q ^ ((r - 1) * s) * Q ^ s - Q ^ ((r - 1) * s) := by rw [Nat.mul_sub, mul_one]
    _ ≤ Q ^ (r * s) - 1 := by rw [hsplit]; omega

end Arithmetic

section Module

variable {r : ℕ} {D : Type*} [Group D] {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
  [Module F V]

theorem exists_isPrimitiveRoot_of_mem_center [Nontrivial V] (hr : r.Prime)
    (hDexp : ∀ x : D, x ^ r = 1) (ρ : D →* Module.End F V) (hρ : Function.Injective ρ)
    (hscalar : ∀ z ∈ center D, ∃ c : F, ∀ v, ρ z v = c • v) {z : D} (hz : z ∈ center D)
    (hz1 : z ≠ 1) : ∃ ζ : F, IsPrimitiveRoot ζ r ∧ ρ z = ζ • 1 := by
  obtain ⟨c, hc⟩ := hscalar z hz
  have hρz : ρ z = c • 1 := LinearMap.ext fun v => by rw [hc]; rfl
  refine ⟨c, ?_, hρz⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hcr : c ^ r = 1 := by
    have h : ρ (z ^ r) v = v := by rw [hDexp, map_one]; rfl
    rw [map_pow, hρz, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at h
    have h' : (c ^ r - 1) • v = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hv)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hz1 (hρ (by rw [hρz, one_smul, map_one]))
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hcr hc1)

theorem injective_apply (ρ : D →* Module.End F V) (d : D) : Function.Injective (ρ d) := by
  intro u v huv
  have h := congrArg (ρ d⁻¹) huv
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Module.End.one_apply] at h

theorem mul_eq_smul_mul_of_commutatorElement (ρ : D →* Module.End F V) {x y : D} {ζ : F}
    (hζ : ρ ⁅y, x⁆ = ζ • 1) : ρ y * ρ x = ζ • (ρ x * ρ y) := by
  have e : y * x = ⁅y, x⁆ * (x * y) := by rw [commutatorElement_def]; group
  rw [← map_mul, e, map_mul, hζ, smul_mul_assoc, one_mul, map_mul]

end Module

theorem odd_extraspecial_binary_module_mixed_stabilizer_orbits {r a : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (ha : 1 ≤ a) {D : Type*} [Group D] [Finite D]
    (hDcard : Nat.card D = r ^ (1 + 2 * a)) (hDexp : ∀ x : D, x ^ r = 1)
    (hZ : center D = commutator D) (hZr : Nat.card (center D) = r)
    {F : Type*} [Field F] [Finite F] {Q : ℕ} (hQ : Nat.card F = Q)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V] {m : ℕ}
    (hm : finrank F V = m) (ρ : D →* Module.End F V) (hρ : Function.Injective ρ)
    (hscalar : ∀ z ∈ center D, ∃ c : F, ∀ v, ρ z v = c • v) :
    r ∣ Q - 1 ∧ r ^ a ∣ m ∧
      (∀ x : D, x ∉ center D → Nat.card {v : V // ρ x v = v} = Q ^ (m / r)) ∧
      (∃ v : V, v ≠ 0 ∧ ∀ d : D, ρ d v = v → d = 1) ∧
      (∃ w : V, w ≠ 0 ∧ ∃ d : D, d ≠ 1 ∧ ρ d w = w) ∧
      Nat.card {v : V // v ≠ 0 ∧ ∃ d : D, d ≠ 1 ∧ ρ d v = v} ≤
        r * (r ^ (2 * a) - 1) / (r - 1) * (Q ^ (m / r) - 1) ∧
      r * (r ^ (2 * a) - 1) / (r - 1) * (Q ^ (m / r) - 1) < Q ^ m - 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hr0 : 0 < r := hr.pos
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have : Fintype F := Fintype.ofFinite F
  have : Finite V := Module.finite_of_finite F
  have : Fintype V := Fintype.ofFinite V
  have : Fintype D := Fintype.ofFinite D
  have hprim := fun z (hz : z ∈ center D) (hz1 : z ≠ 1) =>
    exists_isPrimitiveRoot_of_mem_center hr hDexp ρ hρ hscalar hz hz1
  have hpow : ∀ x : D, ρ x ^ r = 1 := fun x => by rw [← map_pow, hDexp, map_one]
  have hcomm1 : ∀ x y : D, ⁅y, x⁆ = 1 → ρ y * ρ x = ρ x * ρ y := fun x y h => by
    rw [← map_mul, ← map_mul, commutatorElement_eq_one_iff_mul_comm.1 h]
  have hshift : ∀ x y : D, ⁅y, x⁆ ≠ 1 →
      ∃ ζ : F, IsPrimitiveRoot ζ r ∧ ρ y * ρ x = ζ • (ρ x * ρ y) := by
    intro x y h
    obtain ⟨ζ, hζ, hρζ⟩ := hprim _ (commutatorElement_mem_center hZ y x) h
    exact ⟨ζ, hζ, mul_eq_smul_mul_of_commutatorElement ρ hρζ⟩
  have hZnt : Nontrivial (center D) := Finite.one_lt_card_iff_nontrivial.1 (hZr ▸ hr.one_lt)
  obtain ⟨z, hz1⟩ := exists_ne (1 : center D)
  obtain ⟨ζ₀, hζ₀, -⟩ := hprim z z.2 fun h => hz1 (Subtype.ext h)
  have h1 : r ∣ Q - 1 := by
    apply hζ₀.dvd_of_pow_eq_one
    rw [← hQ, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one ζ₀ (hζ₀.ne_zero hr0.ne')
  have hfix : ∀ x : D, x ∉ center D → finrank F ((ρ x).eigenspace 1) * r = m := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : D, ⁅y, x⁆ ≠ 1 := by
      by_contra! h
      exact hx (mem_center_iff.2 fun y => commutatorElement_eq_one_iff_mul_comm.1 (h y))
    obtain ⟨ζ, hζ, hcb⟩ := hshift x y hy
    rw [← hm, finrank_eq_mul_finrank_eigenspace_one hr0 hζ (hpow x) (injective_apply ρ y) hcb,
      mul_comm]
  have hcardfix : ∀ x : D,
      Nat.card {v : V // ρ x v = v} = Q ^ finrank F ((ρ x).eigenspace 1) := by
    intro x
    rw [← hQ, ← Module.natCard_eq_pow_finrank]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      rw [Module.End.mem_eigenspace_iff, one_smul])
  obtain ⟨b, c, hbb, hcb, hcbi⟩ := exists_symplectic_lifts hDexp hZ hZr hDcard
  have h2 : r ^ a ∣ m := by
    let W : ℕ → Submodule F V := fun k =>
      ⨅ i : {i : Fin a // (i : ℕ) < k}, (ρ (b i)).eigenspace 1
    have hmemW : ∀ k v, v ∈ W k ↔ ∀ i : Fin a, (i : ℕ) < k → ρ (b i) v = v := by
      intro k v
      simp only [W, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul, Subtype.forall]
    have hstep : ∀ k (hk : k < a), finrank F (W k) = r * finrank F (W (k + 1)) := by
      intro k hk
      set i₀ : Fin a := ⟨k, hk⟩
      obtain ⟨ζ, hζ, hcbk⟩ := hshift (b i₀) (c i₀) (hcbi i₀)
      have hW : W (k + 1) = W k ⊓ (ρ (b i₀)).eigenspace 1 := by
        ext v
        rw [Submodule.mem_inf, hmemW, hmemW, Module.End.mem_eigenspace_iff, one_smul]
        constructor
        · intro h
          exact ⟨fun i hi => h i (by omega), h i₀ (by simp [i₀])⟩
        · rintro ⟨h, h'⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact h i hi
          · rw [show i = i₀ from Fin.ext hi]
            exact h'
      rw [hW]
      refine finrank_eq_mul_finrank_inf_eigenspace_one hr0 hζ (hpow _) (injective_apply ρ _)
        hcbk ?_ ?_
      · intro u hu
        rw [hmemW] at hu ⊢
        intro i hi
        rw [← Module.End.mul_apply, hcomm1 _ _ (hbb i i₀), Module.End.mul_apply, hu i hi]
      · intro u hu
        rw [hmemW] at hu ⊢
        intro i hi
        have hne : i₀ ≠ i := fun h => by rw [← h] at hi; simp [i₀] at hi
        rw [← Module.End.mul_apply, ← hcomm1 _ _ (hcb i₀ i hne), Module.End.mul_apply, hu i hi]
    have hind : ∀ k, k ≤ a → m = r ^ k * finrank F (W k) := by
      intro k
      induction k with
      | zero =>
        intro _
        have hW0 : W 0 = ⊤ := by
          ext v
          simp only [hmemW, Submodule.mem_top, iff_true]
          intro i hi
          omega
        rw [hW0, finrank_top, pow_zero, one_mul, hm]
      | succ k ih =>
        intro hk
        rw [ih (by omega), hstep k (by omega), pow_succ, mul_assoc]
    exact ⟨_, hind a le_rfl⟩
  have hmpos : 0 < m := hm ▸ Module.finrank_pos
  obtain ⟨t, ht⟩ := h2
  have hra : r ^ a = r * r ^ (a - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ha]
  have hms : m / r = r ^ (a - 1) * t := by
    rw [ht, hra, mul_assoc, Nat.mul_div_cancel_left _ hr0]
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; omega
    · exact h
  have hs : r ^ (a - 1) ≤ m / r := by
    rw [hms]
    exact Nat.le_mul_of_pos_right _ ht0
  have hmr : m = r * (m / r) := by rw [hms, ht, hra, mul_assoc]
  have hQ2 : 2 ≤ Q := hQ ▸ Finite.one_lt_card
  have hQr : r + 1 ≤ Q := by
    have := Nat.le_of_dvd (by omega) h1
    omega
  have h6 := card_bound hr3 ha hs hQr
  rw [← hmr] at h6
  have hfixs : ∀ x : D, x ∉ center D → Nat.card {v : V // ρ x v = v} = Q ^ (m / r) := by
    intro x hx
    rw [hcardfix x, ← hfix x hx, Nat.mul_div_cancel _ hr0]
  set M := r * (r ^ (2 * a) - 1) / (r - 1) with hM
  have hMr : (r - 1) * M = r ^ (1 + 2 * a) - r := by
    have hdvd : r - 1 ∣ r * (r ^ (2 * a) - 1) := by
      have := Nat.sub_dvd_pow_sub_pow r 1 (2 * a)
      rw [one_pow] at this
      exact this.mul_left r
    rw [Nat.mul_div_cancel' hdvd, Nat.mul_sub, mul_one, ← pow_succ', add_comm]
  set bad := (Finset.univ : Finset V).filter fun v => v ≠ 0 ∧ ∃ d : D, d ≠ 1 ∧ ρ d v = v
  set Dnc := (Finset.univ : Finset D).filter fun d => d ∉ center D
  have hDnc : Dnc.card = r ^ (1 + 2 * a) - r := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D))
      (fun d => d ∈ center D)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hDcard] at h
    have hc : ((Finset.univ : Finset D).filter fun d => d ∈ center D).card = r := by
      rw [← hZr, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    have hD' : Dnc.card = ((Finset.univ : Finset D).filter fun d => ¬d ∈ center D).card := rfl
    omega
  have hcount : bad.card * (r - 1) ≤ Dnc.card * (Q ^ (m / r) - 1) := by
    refine Finset.card_mul_le_card_mul (fun v d => ρ d v = v) (fun v hv => ?_) (fun d hd => ?_)
    · obtain ⟨hv0, d₀, hd₀, hd₀v⟩ := (Finset.mem_filter.1 hv).2
      let S : Subgroup D :=
        { carrier := {d | ρ d v = v}
          mul_mem' := fun {d d'} (h : ρ d v = v) (h' : ρ d' v = v) => by
            change ρ (d * d') v = v
            rw [map_mul, Module.End.mul_apply, h', h]
          one_mem' := by change ρ 1 v = v; rw [map_one, Module.End.one_apply]
          inv_mem' := fun {d} (h : ρ d v = v) => by
            change ρ d⁻¹ v = v
            conv_lhs => rw [← h]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
      have hSZ : ∀ d ∈ S, d ∈ center D → d = 1 := by
        intro d hdS hdZ
        by_contra hd1
        obtain ⟨ζ, hζ, hρζ⟩ := hprim d hdZ hd1
        have h : ρ d v = v := hdS
        rw [hρζ, LinearMap.smul_apply, Module.End.one_apply] at h
        have h' : (ζ - 1) • v = 0 := by rw [sub_smul, one_smul, h, sub_self]
        exact hζ.ne_one hr.one_lt (sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hv0))
      have hScard : r ≤ Nat.card S := by
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 (hDcard ▸ S.card_subgroup_dvd_card)
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hk
          exact hd₀ ((Subgroup.eq_bot_of_card_eq S hk) ▸ (show d₀ ∈ S from hd₀v) :)
        rw [hk]
        exact le_self_pow hr.one_lt.le hk0
      have hsub : ((Finset.univ : Finset D).filter fun d => ρ d v = v).erase 1 ⊆
          Dnc.bipartiteAbove (fun v d => ρ d v = v) v := by
        intro d hd
        rw [Finset.mem_erase, Finset.mem_filter] at hd
        rw [Finset.mem_bipartiteAbove, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, fun hdZ => hd.1 (hSZ d hd.2.2 hdZ)⟩, hd.2.2⟩
      refine le_trans ?_ (Finset.card_le_card hsub)
      rw [Finset.card_erase_of_mem
        (by simp : (1 : D) ∈ (Finset.univ : Finset D).filter fun d => ρ d v = v)]
      have hS : ((Finset.univ : Finset D).filter fun d => ρ d v = v).card = Nat.card S := by
        rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
        rfl
      omega
    · have hdZ : d ∉ center D := (Finset.mem_filter.1 hd).2
      have hsub : bad.bipartiteBelow (fun v d => ρ d v = v) d ⊆
          ((Finset.univ : Finset V).filter fun v => ρ d v = v).erase 0 := by
        intro v hv
        rw [Finset.mem_bipartiteBelow, Finset.mem_filter] at hv
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨hv.1.2.1, Finset.mem_univ _, hv.2⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_erase_of_mem
        (by simp : (0 : V) ∈ (Finset.univ : Finset V).filter fun v => ρ d v = v)]
      have h := hfixs d hdZ
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      rw [h]
  have h5 : bad.card ≤ M * (Q ^ (m / r) - 1) := by
    rw [hDnc, ← hMr, mul_assoc, mul_comm] at hcount
    exact Nat.le_of_mul_le_mul_left hcount (by omega)
  have hbad : Nat.card {v : V // v ≠ 0 ∧ ∃ d : D, d ≠ 1 ∧ ρ d v = v} = bad.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hV : (Finset.univ.filter fun v : V => v ≠ 0).card = Q ^ m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F), hQ, hm]
  obtain ⟨v, hv, hvbad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := bad) (t := Finset.univ.filter fun v : V => v ≠ 0) (by rw [hV]; omega)
  have hv0 : v ≠ 0 := (Finset.mem_filter.1 hv).2
  have hvreg : ∀ d : D, ρ d v = v → d = 1 := by
    intro d hdv
    by_contra hd1
    exact hvbad (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv0, d, hd1, hdv⟩)
  obtain ⟨x, hx⟩ : ∃ x : D, x ∉ center D := by
    by_contra! h
    have htop : center D = ⊤ := eq_top_iff.2 fun x _ => h x
    have := Nat.card_congr (Subgroup.topEquiv (G := D)).toEquiv
    rw [← htop, hZr, hDcard] at this
    have hlt : r < r ^ (1 + 2 * a) :=
      lt_self_pow₀ hr.one_lt (by omega)
    omega
  have hx1 : x ≠ 1 := fun h => hx (h ▸ one_mem _)
  have hfixx := hfixs x hx
  have hQs : 1 < Q ^ (m / r) :=
    Nat.one_lt_pow (by have := Nat.one_le_pow (a - 1) r hr0; omega) (by omega)
  rw [← hfixx] at hQs
  have : Nontrivial {v : V // ρ x v = v} := Finite.one_lt_card_iff_nontrivial.1 hQs
  obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (⟨0, map_zero _⟩ : {v : V // ρ x v = v})
  refine ⟨h1, ⟨t, ht⟩, hfixs, ⟨v, hv0, hvreg⟩, ⟨w, fun h => hw0 (Subtype.ext h), x, hx1, hw⟩,
    hbad ▸ h5, h6⟩

end CFSG.OddSolvableUnitary
