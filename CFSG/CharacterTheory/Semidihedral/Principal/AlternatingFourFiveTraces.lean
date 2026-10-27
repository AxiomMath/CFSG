module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicMultiplicity
public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.TraceGap
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.CosetConstantKernel

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u w

namespace AlternatingFourFive

theorem alternatingFour_classify {A : Type*} [Group A] (e : A ≃* alternatingGroup (Fin 4))
    (a : A) : a = 1 ∨ (a ≠ 1 ∧ a ^ 2 = 1) ∨ (a ≠ 1 ∧ a ^ 3 = 1) := by
  have h : ∀ x : alternatingGroup (Fin 4), x = 1 ∨ (x ≠ 1 ∧ x ^ 2 = 1) ∨ (x ≠ 1 ∧ x ^ 3 = 1) := by
    decide
  have he1 : ∀ y : A, e y = 1 ↔ y = 1 := fun y => by
    rw [← map_one e, e.injective.eq_iff]
  rcases h (e a) with h1 | ⟨h1, h2⟩ | ⟨h1, h3⟩
  · exact Or.inl ((he1 a).mp h1)
  · refine Or.inr (Or.inl ⟨fun ha => h1 ((he1 a).mpr ha), ?_⟩)
    rw [← he1, map_pow, h2]
  · refine Or.inr (Or.inr ⟨fun ha => h1 ((he1 a).mpr ha), ?_⟩)
    rw [← he1, map_pow, h3]

theorem alternatingFour_card_involutions {A : Type*} [Group A] [Fintype A]
    (e : A ≃* alternatingGroup (Fin 4)) :
    (Finset.univ.filter fun a : A => a ≠ 1 ∧ a ^ 2 = 1).card = 3 := by
  have h : (Finset.univ.filter fun x : alternatingGroup (Fin 4) => x ≠ 1 ∧ x ^ 2 = 1).card = 3 := by
    decide
  rw [← h, ← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr (e.toEquiv.subtypeEquiv fun a => ?_)
  have he1 : ∀ y : A, e y = 1 ↔ y = 1 := fun y => by
    rw [← map_one e, e.injective.eq_iff]
  change a ≠ 1 ∧ a ^ 2 = 1 ↔ e a ≠ 1 ∧ e a ^ 2 = 1
  rw [ne_eq, ne_eq, ← map_pow, he1, he1]

theorem alternatingFour_card {A : Type*} [Group A] [Fintype A]
    (e : A ≃* alternatingGroup (Fin 4)) : Nat.card A = 12 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem trace_idempotent_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (P : Module.End ℂ V) (hP : IsIdempotentElem P) :
    ∃ m : ℕ, LinearMap.trace ℂ V P = m :=
  ⟨Module.finrank ℂ (LinearMap.range P), (LinearMap.IsIdempotentElem.isProj_range P hP).trace⟩

theorem range_finiteOrderEigenprojection {V : Type*} [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (hn : 0 < n) (T : Module.End ℂ V) (hT : T ^ n = 1) (μ : ℂˣ) (hμ : μ ^ n = 1) :
    LinearMap.range (finiteOrderEigenprojection n
      (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')) μ T) =
      Module.End.eigenspace T (μ : ℂ) := by
  set P := finiteOrderEigenprojection n (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')) μ T
    with hP
  have heig := finiteOrderEigenprojection_eigenvalue n
    (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')) μ hμ T hT
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have e := congrArg (fun F : Module.End ℂ V => F v) heig
    simpa only [Module.End.mul_apply, LinearMap.smul_apply] using e
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨v, ?_⟩
    have hpow : ∀ j : ℕ, ((((μ⁻¹ : ℂˣ) : ℂ) • T) ^ j) v = v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, LinearMap.smul_apply, hv, smul_smul,
          Units.inv_mul, one_smul]
    rw [hP, finiteOrderEigenprojection, cyclicOperatorAverage, LinearMap.smul_apply,
      LinearMap.sum_apply, Finset.sum_congr rfl fun j _ => hpow j, Finset.sum_const,
      Finset.card_range, Units.val_inv_eq_inv_val, Units.val_mk0, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul]

theorem sum_pow_of_pow_five_eq_one {μ : ℂ} (h5 : μ ^ 5 = 1) (h1 : μ ≠ 1) :
    μ + μ ^ 2 + μ ^ 3 + μ ^ 4 = -1 := by
  have hgeom := geom_sum_mul μ 5
  rw [h5, sub_self] at hgeom
  have hsum : ∑ i ∈ Finset.range 5, μ ^ i = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr h1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hsum
  linear_combination hsum

theorem order_five_rational_multiplicities {G : Type*} [Group G]
    (θ : FiniteComplexRepresentation G) (w₀ : G) (hw₀ : orderOf w₀ = 5) (q : ℚ)
    (hq : θ.character w₀ = q) :
    ∃ n₀ m : ℕ, (∀ j : ℕ, j % 5 ≠ 0 → θ.character (w₀ ^ j) = (n₀ : ℂ) - m) ∧
      (Module.finrank ℂ θ.vector : ℂ) = n₀ + 4 * m := by
  have h5 : w₀ ^ 5 = 1 := by rw [← hw₀]; exact pow_orderOf_eq_one w₀
  choose n hn using fun k : ℕ =>
    cyclicMultiplicity_natural θ w₀ (M := 5) (by norm_num) h5 (k : ℤ)
  have hinv : ∀ j : ℕ, j < 5 → θ.character (w₀ ^ j) =
      n 0 + n 1 * cyclicRoot 5 ^ j + n 2 * cyclicRoot 5 ^ (2 * j) +
        n 3 * cyclicRoot 5 ^ (3 * j) + n 4 * cyclicRoot 5 ^ (4 * j) := by
    intro j hj
    rw [cyclicMultiplicity_inversion θ.character w₀ (by norm_num) hj]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hn 0, hn 1, hn 2, hn 3, hn 4]
    have hz : ∀ k : ℕ, cyclicRoot 5 ^ ((k : ℤ) * j) = cyclicRoot 5 ^ (k * j) := fun k => by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [show ((0 : ℕ) : ℤ) = 0 from rfl, zero_mul, zpow_zero, hz 1, hz 2, hz 3, hz 4, one_mul,
      mul_comm 2 j, mul_comm 3 j, mul_comm 4 j]
    ring_nf
  have hζp : IsPrimitiveRoot (cyclicRoot 5) (5 ^ (0 + 1)) := by
    simpa using cyclicRoot_isPrimitiveRoot (M := 5) (by norm_num)
  set c : ℕ → ℚ := fun k => (n k : ℚ) - if k = 0 then q else 0 with hc
  have hrel : ∑ k ∈ Finset.range (5 ^ (0 + 1)), (c k : ℂ) * cyclicRoot 5 ^ k = 0 := by
    have e := hinv 1 (by norm_num)
    rw [pow_one, hq] at e
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    norm_num [hc]
    linear_combination -e
  have hper : ∀ k : ℕ, k < 5 → c k = c 0 := fun k hk => by
    have h := CFSG.LyonsUnitaryFour.periodic_of_sum_pow_eq_zero Nat.prime_five 0 hζp c hrel
      (by simpa using hk)
    simpa [Nat.mod_one] using h
  have hc0 : c 0 = (n 0 : ℚ) - q := by simp [hc]
  have hck : ∀ k : ℕ, 0 < k → k < 5 → (n k : ℚ) = n 0 - q := by
    intro k hk0 hk5
    have h := hper k hk5
    rw [hc0] at h
    simpa [hc, Nat.pos_iff_ne_zero.mp hk0] using h
  have hn1 : n 2 = n 1 ∧ n 3 = n 1 ∧ n 4 = n 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> exact_mod_cast
      (hck _ (by norm_num) (by norm_num)).trans (hck 1 (by norm_num) (by norm_num)).symm
  have hq' : (q : ℂ) = (n 0 : ℂ) - n 1 := by
    have h := hck 1 (by norm_num) (by norm_num)
    have : (q : ℚ) = n 0 - n 1 := by linarith
    exact_mod_cast this
  refine ⟨n 0, n 1, fun j hj => ?_, ?_⟩
  ·
    have hjw : w₀ ^ j = w₀ ^ (j % 5) := by
      rw [← hw₀, pow_mod_orderOf]
    have hj5 : j % 5 < 5 := Nat.mod_lt _ (by norm_num)
    rw [hjw, hinv _ hj5, hn1.1, hn1.2.1, hn1.2.2]
    have hμ5 : (cyclicRoot 5 ^ (j % 5)) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, cyclicRoot_pow_self 5, one_pow]
    have hμ1 : cyclicRoot 5 ^ (j % 5) ≠ 1 := by
      intro h1
      have := (cyclicRoot_isPrimitiveRoot (M := 5) (by norm_num)).dvd_of_pow_eq_one _ h1
      exact hj (Nat.eq_zero_of_dvd_of_lt this hj5)
    have hs := sum_pow_of_pow_five_eq_one hμ5 hμ1
    rw [show 2 * (j % 5) = (j % 5) * 2 by ring, show 3 * (j % 5) = (j % 5) * 3 by ring,
      show 4 * (j % 5) = (j % 5) * 4 by ring, pow_mul, pow_mul, pow_mul]
    linear_combination (n 1 : ℂ) * hs
  · have e := hinv 0 (by norm_num)
    simp only [pow_zero, mul_zero, mul_one] at e
    rw [hn1.1, hn1.2.1, hn1.2.2] at e
    have h1 : θ.character 1 = (Module.finrank ℂ θ.vector : ℂ) := Representation.char_one _
    rw [← h1, e]
    ring

theorem trace_mul_finiteOrderEigenprojection {G : Type*} [Group G]
    (θ : FiniteComplexRepresentation G) (y w₀ : G) (n : ℕ) (hn : 0 < n) (μ : ℂˣ) :
    LinearMap.trace ℂ θ.vector (θ.representation y * finiteOrderEigenprojection n
      (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')) μ (θ.representation w₀)) =
      (n : ℂ)⁻¹ * ∑ j ∈ Finset.range n, ((μ⁻¹ : ℂˣ) : ℂ) ^ j * θ.character (y * w₀ ^ j) := by
  rw [finiteOrderEigenprojection, cyclicOperatorAverage, mul_smul_comm, Finset.mul_sum,
    map_smul, map_sum, smul_eq_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_pow, mul_smul_comm, map_smul, smul_eq_mul]
  congr 1
  change LinearMap.trace ℂ θ.vector (θ.representation y * θ.representation w₀ ^ j) =
    LinearMap.trace ℂ θ.vector (θ.representation (y * w₀ ^ j))
  rw [map_mul θ.representation, map_pow θ.representation]

theorem sum_range_five_twisted {μ : ℂ} (h5 : μ ^ 5 = 1) (h1 : μ ≠ 1) (F : ℕ → ℂ) (c : ℂ)
    (hF : ∀ j, 0 < j → j < 5 → F j = c) :
    ∑ j ∈ Finset.range 5, μ ^ j * F j = F 0 - c := by
  have hs := sum_pow_of_pow_five_eq_one h5 h1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul]
  rw [hF 1 (by norm_num) (by norm_num), hF 2 (by norm_num) (by norm_num),
    hF 3 (by norm_num) (by norm_num), hF 4 (by norm_num) (by norm_num)]
  linear_combination c * hs

theorem alternatingFour_sum_ite {A : Type*} [Group A] [Fintype A] [DecidableEq A]
    (e : A ≃* alternatingGroup (Fin 4)) (X Y : ℂ) :
    ∑ a : A, (if a = 1 then X else if a ^ 2 = 1 then Y else 0) = X + 3 * Y := by
  have he1 : ∀ y : A, e y = 1 ↔ y = 1 := fun y => by
    rw [← map_one e, e.injective.eq_iff]
  have he2 : ∀ y : A, e y ^ 2 = 1 ↔ y ^ 2 = 1 := fun y => by
    rw [← map_pow, he1]
  rw [← e.symm.toEquiv.sum_comp]
  have hF : ∀ x : alternatingGroup (Fin 4),
      (if e.symm.toEquiv x = 1 then X else if e.symm.toEquiv x ^ 2 = 1 then Y else 0) =
        if x = 1 then X else if x ^ 2 = 1 then Y else 0 := by
    intro x
    have h1 : e.symm.toEquiv x = 1 ↔ x = 1 := by
      rw [← he1]
      simp
    have h2 : e.symm.toEquiv x ^ 2 = 1 ↔ x ^ 2 = 1 := by
      rw [← he2]
      simp
    by_cases hx1 : x = 1
    · rw [ite_eq_left (h1.mpr hx1), ite_eq_left hx1]
    · rw [ite_eq_right (fun h => hx1 (h1.mp h)), ite_eq_right hx1]
      by_cases hx2 : x ^ 2 = 1
      · rw [ite_eq_left (h2.mpr hx2), ite_eq_left hx2]
      · rw [ite_eq_right (fun h => hx2 (h2.mp h)), ite_eq_right hx2]
  rw [Finset.sum_congr rfl fun x _ => hF x, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have c1 : (Finset.univ.filter fun x : alternatingGroup (Fin 4) => x = 1).card = 1 := by
    decide
  have c3 : ((Finset.univ.filter fun x : alternatingGroup (Fin 4) => ¬x = 1).filter
      fun x => x ^ 2 = 1).card = 3 := by
    decide
  rw [c1, c3]
  push_cast
  ring

end AlternatingFourFive

open AlternatingFourFive

theorem alternating_four_central_five_eigenspace_traces_mod_sixty
    {G : Type u} [Group G] [Fintype G] (A W : Subgroup G)
    (hA : Nonempty (A ≃* alternatingGroup (Fin 4)))
    (hWA : W ≤ Subgroup.centralizer (A : Set G)) (hWcyc : IsCyclic W) (hW5 : Nat.card W = 5)
    (θ : FiniteComplexRepresentation.{u, w} G) (hrat : ∀ w ∈ W, ∃ q : ℚ, θ.character w = q)
    (a b : ℤ) (ha : ∀ v ∈ A, orderOf v = 2 → θ.character v = a)
    (hb : ∀ v ∈ A, orderOf v = 2 → ∀ w ∈ W, w ≠ 1 → θ.character (v * w) = b)
    (hz : ∀ z ∈ A, orderOf z = 3 → ∀ w ∈ W, θ.character (z * w) = 0) :
    ∃ x : ℤ, (∀ w ∈ W, w ≠ 1 → θ.character w = x) ∧
      x ≡ Module.finrank ℂ θ.vector + 3 * (a - b) [ZMOD 60] ∧
      ∃ (m : ℕ) (e : ℤ), 5 * (m : ℤ) = Module.finrank ℂ θ.vector - x ∧ a - b = 5 * e ∧
        (∀ w ∈ W, w ≠ 1 → ∀ μ : ℂ, μ ^ 5 = 1 → μ ≠ 1 →
          Module.finrank ℂ (Module.End.eigenspace (θ.representation w) μ) = m) ∧
        ∃ k : ℕ, (m : ℤ) + 3 * e = 12 * k := by
  obtain ⟨eA⟩ := hA
  obtain ⟨g, hg⟩ := hWcyc.exists_generator
  have hgord : orderOf g = 5 := by rw [← hW5]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hw₀ : orderOf (g : G) = 5 := by rw [Subgroup.orderOf_coe, hgord]
  have hw₀W : (g : G) ∈ W := g.2
  have hWpow : ∀ w ∈ W, ∃ j : ℕ, j < 5 ∧ w = (g : G) ^ j := by
    intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, hw⟩)
    have hkG : (g : G) ^ k = w := congrArg Subtype.val hk
    have hnn : 0 ≤ k % 5 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 5 < 5 := Int.emod_lt_of_pos k (by norm_num)
    refine ⟨(k % 5).toNat, by omega, ?_⟩
    rw [← hkG, ← zpow_mod_orderOf, hw₀, ← zpow_natCast, Int.toNat_of_nonneg hnn]
    rfl
  have hWord : ∀ w ∈ W, w ≠ 1 → orderOf w = 5 := by
    intro w hw hw1
    have hdvd : orderOf w ∣ 5 := by
      have h := Subgroup.orderOf_dvd_natCard W hw
      rwa [hW5] at h
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h5
  have hpowW : ∀ j : ℕ, 0 < j → j < 5 → (g : G) ^ j ∈ W ∧ (g : G) ^ j ≠ 1 := fun j hj0 hj5 =>
    ⟨W.pow_mem hw₀W j, pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hw₀]; exact hj5)⟩
  obtain ⟨q, hq⟩ := hrat _ hw₀W
  obtain ⟨n₀, m, hval, hdeg⟩ := order_five_rational_multiplicities θ (g : G) hw₀ q hq
  have hxW : ∀ w ∈ W, w ≠ 1 → θ.character w = (((n₀ : ℤ) - m : ℤ) : ℂ) := by
    intro w hw hw1
    obtain ⟨j, hj5, rfl⟩ := hWpow w hw
    have hj : j % 5 ≠ 0 := by
      intro h
      rw [Nat.mod_eq_of_lt hj5] at h
      exact hw1 (by rw [h, pow_zero])
    rw [hval j hj]
    push_cast
    ring
  have hf : (Module.finrank ℂ θ.vector : ℤ) = n₀ + 4 * m := by exact_mod_cast hdeg
  have hfx : 5 * (m : ℤ) = Module.finrank ℂ θ.vector - ((n₀ : ℤ) - m) := by rw [hf]; ring
  have h1C : θ.character 1 = (Module.finrank ℂ θ.vector : ℂ) := Representation.char_one _
  have hfxC : (Module.finrank ℂ θ.vector : ℂ) - (((n₀ : ℤ) - m : ℤ) : ℂ) = 5 * (m : ℂ) := by
    rw [hdeg]
    push_cast
    ring
  have h5u : (0 : ℕ) < 5 := by norm_num
  have hdim : ∀ w ∈ W, w ≠ 1 → ∀ μ : ℂ, μ ^ 5 = 1 → μ ≠ 1 →
      Module.finrank ℂ (Module.End.eigenspace (θ.representation w) μ) = m := by
    intro w hw hw1 μ hμ5 hμ1
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hμ5
    obtain ⟨μu, rfl⟩ : ∃ u : ℂˣ, (u : ℂ) = μ := ⟨Units.mk0 μ hμ0, rfl⟩
    have hμu5 : μu ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hμ5, Units.val_one])
    have hT : θ.representation w ^ 5 = 1 := by
      rw [← map_pow, ← hWord w hw hw1, pow_orderOf_eq_one, map_one]
    have hrange := range_finiteOrderEigenprojection 5 h5u (θ.representation w) hT μu hμu5
    have hidem := finiteOrderEigenprojection_idempotent 5
      (Units.mk0 ((5 : ℕ) : ℂ) (Nat.cast_ne_zero.mpr h5u.ne')) μu rfl hμu5 _ hT
    have htrace := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
    rw [hrange] at htrace
    have hinv5 : ((μu⁻¹ : ℂˣ) : ℂ) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, hμu5, inv_one, Units.val_one]
    have hinv1 : ((μu⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro h
      apply hμ1
      have h' : μu⁻¹ = 1 := Units.ext (by rw [h, Units.val_one])
      rw [inv_eq_one.mp h', Units.val_one]
    have hcomp := trace_mul_finiteOrderEigenprojection θ 1 w 5 h5u μu
    rw [map_one, one_mul, sum_range_five_twisted hinv5 hinv1 (fun j => θ.character (1 * w ^ j))
      (((n₀ : ℤ) - m : ℤ) : ℂ) (fun j hj0 hj5 => by
        rw [one_mul]
        exact hxW _ (W.pow_mem hw j) (pow_ne_one_of_lt_orderOf hj0.ne' (by
          rw [hWord w hw hw1]; exact hj5))), pow_zero, mul_one, h1C, hfxC] at hcomp
    rw [hcomp] at htrace
    have hval' : (Module.finrank ℂ (Module.End.eigenspace (θ.representation w) μu) : ℂ) = m := by
      rw [← htrace]
      field_simp
      norm_num
    exact_mod_cast hval'
  obtain ⟨ζu, hζu⟩ : ∃ u : ℂˣ, (u : ℂ) = cyclicRoot 5 := ⟨Units.mk0 _ (cyclicRoot_ne_zero 5), rfl⟩
  have hζu5 : ζu ^ 5 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hζu, cyclicRoot_pow_self, Units.val_one])
  have hT0 : θ.representation (g : G) ^ 5 = 1 := by
    rw [← map_pow, ← hw₀, pow_orderOf_eq_one, map_one]
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ θ.vector, P = finiteOrderEigenprojection 5
      (Units.mk0 ((5 : ℕ) : ℂ) (Nat.cast_ne_zero.mpr h5u.ne')) ζu (θ.representation (g : G)) :=
    ⟨_, rfl⟩
  obtain ⟨PA, hPA⟩ : ∃ P : Module.End ℂ θ.vector,
      P = CFSG.LyonsUnitaryFour.subgroupAverage θ.representation A := ⟨_, rfl⟩
  have hcommA : ∀ h : A, Commute (θ.representation h) (θ.representation (g : G)) := by
    intro h
    have hc : (h : G) * g = g * h := Subgroup.mem_centralizer_iff.mp (hWA hw₀W) h h.2
    change θ.representation h * θ.representation g = θ.representation g * θ.representation h
    rw [← map_mul, ← map_mul, hc]
  have hcomm : Commute PA P := by
    rw [hPA, hP, CFSG.LyonsUnitaryFour.subgroupAverage, finiteOrderEigenprojection,
      cyclicOperatorAverage]
    apply Commute.smul_left
    apply Commute.sum_left
    intro h _
    apply Commute.smul_right
    apply Commute.sum_right
    intro j _
    exact ((hcommA h).smul_right _).pow_right j
  have hidemQ : IsIdempotentElem (PA * P) := by
    refine IsIdempotentElem.mul_of_commute hcomm ?_ ?_
    · rw [hPA]
      exact CFSG.LyonsUnitaryFour.subgroupAverage_idempotent θ.representation A
    · rw [hP]
      exact finiteOrderEigenprojection_idempotent 5
        (Units.mk0 ((5 : ℕ) : ℂ) (Nat.cast_ne_zero.mpr h5u.ne')) ζu rfl hζu5 _ hT0
  obtain ⟨N, hN⟩ := trace_idempotent_natural (PA * P) hidemQ
  have htraceQ : LinearMap.trace ℂ θ.vector (PA * P) = (Nat.card A : ℂ)⁻¹ *
      ∑ h : A, ((5 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range 5,
        ((ζu⁻¹ : ℂˣ) : ℂ) ^ j * θ.character (h * (g : G) ^ j) := by
    rw [hPA, CFSG.LyonsUnitaryFour.subgroupAverage, smul_mul_assoc, Finset.sum_mul, map_smul,
      map_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hP]
    exact trace_mul_finiteOrderEigenprojection θ h g 5 h5u ζu
  have hzinv5 : ((ζu⁻¹ : ℂˣ) : ℂ) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hζu5, inv_one, Units.val_one]
  have hzinv1 : ((ζu⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    have h' : ζu⁻¹ = 1 := Units.ext (by rw [h, Units.val_one])
    have h'' : cyclicRoot 5 = 1 := by rw [← hζu, inv_eq_one.mp h', Units.val_one]
    exact (cyclicRoot_isPrimitiveRoot (M := 5) (by norm_num)).ne_one (by norm_num) h''
  have hinner : ∀ h : A, ∑ j ∈ Finset.range 5,
      ((ζu⁻¹ : ℂˣ) : ℂ) ^ j * θ.character (h * (g : G) ^ j) =
        if h = 1 then 5 * (m : ℂ) else if h ^ 2 = 1 then ((a - b : ℤ) : ℂ) else 0 := by
    intro h
    rcases alternatingFour_classify eA h with h1 | ⟨h1, h2⟩ | ⟨h1, h3⟩
    · subst h1
      rw [ite_eq_left rfl, sum_range_five_twisted hzinv5 hzinv1
        (fun j => θ.character (((1 : A) : G) * (g : G) ^ j)) (((n₀ : ℤ) - m : ℤ) : ℂ)
        (fun j hj0 hj5 => by
          rw [OneMemClass.coe_one, one_mul]
          exact hxW _ (hpowW j hj0 hj5).1 (hpowW j hj0 hj5).2),
        OneMemClass.coe_one, one_mul, pow_zero, h1C, hfxC]
    · have hord : orderOf (h : G) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime h2 h1
      rw [ite_eq_right h1, ite_eq_left h2, sum_range_five_twisted hzinv5 hzinv1
        (fun j => θ.character ((h : G) * (g : G) ^ j)) (b : ℂ)
        (fun j hj0 hj5 => hb h h.2 hord _ (hpowW j hj0 hj5).1 (hpowW j hj0 hj5).2),
        pow_zero, mul_one, ha h h.2 hord]
      push_cast
      ring
    · have hn2 : ¬h ^ 2 = 1 := by
        intro h2
        have e3 : h ^ 3 = h ^ 2 * h := pow_succ h 2
        rw [h3, h2, one_mul] at e3
        exact h1 e3.symm
      have hord : orderOf (h : G) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime h3 h1
      rw [ite_eq_right h1, ite_eq_right hn2]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hz h h.2 hord _ (W.pow_mem hw₀W j), mul_zero]
  simp only [hinner] at htraceQ
  rw [← Finset.mul_sum, alternatingFour_sum_ite eA, alternatingFour_card eA, hN] at htraceQ
  have hNZ : 5 * (m : ℤ) + 3 * (a - b) = 60 * N := by
    have e : ((5 * (m : ℤ) + 3 * (a - b) : ℤ) : ℂ) = ((60 * N : ℤ) : ℂ) := by
      push_cast
      rw [htraceQ]
      field_simp
      push_cast
      ring
    exact_mod_cast e
  obtain ⟨e, he⟩ : (5 : ℤ) ∣ a - b := by omega
  refine ⟨(n₀ : ℤ) - m, hxW, Int.modEq_iff_dvd.mpr ⟨N, by linarith⟩, m, e, hfx, he, hdim, N,
    by omega⟩

end CFSG.Semidihedral.Principal
