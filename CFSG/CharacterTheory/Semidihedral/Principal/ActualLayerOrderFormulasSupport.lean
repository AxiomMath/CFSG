module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProductSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.LyonsUnitaryFour CFSG.Open

theorem order_formula_global_bracket {f q δ e : ℚ} (hδ : δ = 1 ∨ δ = -1) (he : e = 1 ∨ e = -1)
    (hf : f ≠ 0) (hfδ : f + δ ≠ 0) :
    1 + δ * q ^ 2 / f - δ * (1 + e * q) ^ 2 / (f + δ) =
      (f - e * δ * q) ^ 2 / (f * (f + δ)) := by
  rcases hδ with rfl | rfl <;> rcases he with rfl | rfl <;> field_simp <;> ring

theorem order_formula_local_bracket {c d q e : ℚ} (he : e = 1 ∨ e = -1) (hc : c ≠ 0)
    (hd : d ≠ 0) (hq : q ≠ 0) :
    (1 / c + 1 / d) ^ 2 + e / q * (q / c - e / d) ^ 2 - e * (q + e) / c ^ 2 =
      (q + e) / (q * d ^ 2) := by
  rcases he with rfl | rfl <;> field_simp <;> ring

theorem order_formula_solve {g c d q e δ f : ℚ} (he : e = 1 ∨ e = -1) (hδ : δ = 1 ∨ δ = -1)
    (hf : 1 < f) (hq : 1 < q) (hc : 0 < c) (hd : 0 < d)
    (h : g * ((f - e * δ * q) ^ 2 / (f * (f + δ))) = c ^ 3 * ((q + e) / (q * d ^ 2))) :
    f - e * δ * q ≠ 0 ∧
      g = c ^ 3 / d ^ 2 * (f * (f + δ) / (f - e * δ * q) ^ 2) * ((q + e) / q) := by
  have hfδ : 0 < f + δ := by rcases hδ with rfl | rfl <;> linarith
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> linarith
  have hrhs : 0 < c ^ 3 * ((q + e) / (q * d ^ 2)) := by positivity
  have hne : f - e * δ * q ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, zero_div, mul_zero] at h
    linarith
  refine ⟨hne, ?_⟩
  have hf0 : f ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  have hd0 : d ≠ 0 := by linarith
  have hfδ0 : f + δ ≠ 0 := hfδ.ne'
  field_simp at h ⊢
  linear_combination h

theorem order_formula_second {q e a b : ℚ} (he : e = 1 ∨ e = -1) (hq : 1 < q)
    (hab : a * b + q ^ 2 * (1 + a + b) = 0) (hae : a - e * q ≠ 0) :
    b + e * q ≠ 0 ∧
      b * (b + 1) / (b + e * q) ^ 2 = a * (a + 1) / (a - e * q) ^ 2 * ((q + e) / (q - e)) := by
  have hq0 : q ≠ 0 := by linarith
  set D := a + q ^ 2 with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have ha : a = -q ^ 2 := by linarith
    rw [ha] at hab
    have h1 : q ^ 2 * (1 - q ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact hq0 (pow_eq_zero_iff (by norm_num) |>.mp h)
    · nlinarith
  have hbD : b * D = -q ^ 2 * (a + 1) := by rw [hD]; linarith
  have hbeD : (b + e * q) * D = e * q * (1 - e * q) * (a - e * q) := by
    rcases he with rfl | rfl <;> linear_combination hbD
  have h1eq : 1 - e * q ≠ 0 := by
    rcases he with rfl | rfl <;> intro h <;> linarith
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hbe0 : b + e * q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hbeD
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero he0 hq0) h1eq) hae) hbeD.symm
  refine ⟨hbe0, ?_⟩
  have hqe : q - e ≠ 0 := by rcases he with rfl | rfl <;> intro h <;> linarith
  have hcross : b * (b + 1) * ((a - e * q) ^ 2 * (q - e)) =
      a * (a + 1) * (q + e) * (b + e * q) ^ 2 := by
    have hmain : D ^ 2 * (b * (b + 1) * ((a - e * q) ^ 2 * (q - e))) =
        D ^ 2 * (a * (a + 1) * (q + e) * (b + e * q) ^ 2) := by
      rcases he with rfl | rfl
      · linear_combination ((b * D + (-q ^ 2 * (a + 1)) + D) * (a - 1 * q) ^ 2 * (q - 1) -
          a * (a + 1) * (q + 1) * (b * D + (-q ^ 2 * (a + 1)) + 2 * 1 * q * D)) * hab
      · linear_combination ((b * D + (-q ^ 2 * (a + 1)) + D) * (a - (-1) * q) ^ 2 * (q - (-1)) -
          a * (a + 1) * (q + (-1)) * (b * D + (-q ^ 2 * (a + 1)) + 2 * (-1) * q * D)) * hab
    exact mul_left_cancel₀ (pow_ne_zero 2 hD0) hmain
  rw [div_mul_div_comm, div_eq_div_iff (pow_ne_zero 2 hbe0)
    (mul_ne_zero (pow_ne_zero 2 hae) hqe)]
  linear_combination hcross

section ClassWeights

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem centered_z_eq {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) :
    ((e' (z n) : S) : G) = (e' (r n) : G) ^ (modulus n / 2) := by
  rw [z, map_pow, Subgroup.coe_pow, modulus_div_two n (by omega)]

omit [Fintype G] in
theorem centered_sylow_le_centralizer {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) : (S : Subgroup G) ≤ C t := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨a, ha⟩ := e'.surjective ⟨x, hx⟩
  have hc := Subgroup.mem_center_iff.mp (z_mem_center n hn) a
  have h2 := congrArg (fun y => ((e' y : S) : G)) hc
  simp only [map_mul, Subgroup.coe_mul, ha] at h2
  rw [← hcent, ← centered_z_eq hn e']
  exact h2

theorem isConj_orderOf_eq {H : Type*} [Group H] {x y : H} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

@[expose] noncomputable def centeredReflection {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) : C t :=
  ⟨(e' (s n) : G), centered_sylow_le_centralizer hn e' hcent (e' (s n)).2⟩

omit [Fintype G] in
theorem coe_centeredReflection {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) :
    ((centeredReflection hn e' hcent : C t) : G) = (e' (s n) : G) := rfl

theorem isConj_centered_involution_iff {n : ℕ} (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) (x : C t) :
    IsConj (x : G) t ↔ x = tInC t ∨ IsConj x (centeredReflection hn e' hcent) := by
  have hSC := centered_sylow_le_centralizer hn e' hcent
  let φ : SemidihedralGroup n →* C t := (Subgroup.inclusion hSC).comp e'.toMonoidHom
  have hφ : ∀ a, ((φ a : C t) : G) = ((e' a : S) : G) := fun a => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply e'.injective
    apply Subtype.ext
    have := congrArg (fun y : C t => (y : G)) hab
    simpa [hφ] using this
  have ht2 : orderOf t = 2 := by
    rw [← hcent, ← centered_z_eq hn e', Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
      orderOf_z n (by omega)]
  have hs2 : orderOf ((e' (s n) : S) : G) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_s n (by omega)]
  have hinvconj : ∀ y : G, orderOf y = 2 → IsConj y t := fun y hy =>
    (InvolutionFusion.ambient_involution_isConj_z n hn S0 f0 hG y hy).trans
      (InvolutionFusion.ambient_involution_isConj_z n hn S0 f0 hG t ht2).symm
  constructor
  · intro hx
    by_cases hxt : x = tInC t
    · exact Or.inl hxt
    right
    have hx2 : orderOf x = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact (isConj_orderOf_eq hx).trans ht2
    have hpx : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
    obtain ⟨y, hxy⟩ :=
      InvolutionFusion.exists_ambient_conjugate_mem_sylow (S.subtype hSC) x hpx
    have hyS : ((y : C t) : G) ∈ (S : Subgroup G) := by
      have hy : (y : C t) ∈ ((S.subtype hSC : Sylow 2 (C t)) : Subgroup (C t)) := y.2
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hy
      exact hy
    set a : SemidihedralGroup n := e'.symm ⟨((y : C t) : G), hyS⟩ with ha
    have hφa : φ a = (y : C t) := by
      apply Subtype.ext
      rw [hφ, ha, MulEquiv.apply_symm_apply]
    have ha2 : orderOf a = 2 := by
      rw [← orderOf_injective φ hφinj a, hφa, ← isConj_orderOf_eq hxy, hx2]
    rcases (involution_iff n (by omega) a).mp ha2 with hz | ⟨j, hj⟩
    · exfalso
      apply hxt
      have hyt : (y : C t) = tInC t := by
        rw [← hφa, hz]
        apply Subtype.ext
        rw [hφ, centered_z_eq hn e', hcent]
        rfl
      rw [hyt] at hxy
      obtain ⟨c, hc⟩ := hxy
      have hct : ((c : C t) : G) * t = t * ((c : C t) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (c : C t).2
      have hc' : ((c : C t) : G) * (x : G) = t * ((c : C t) : G) := by
        have := congrArg (fun w : C t => (w : G)) hc
        simpa [SemiconjBy, tInC] using this
      apply Subtype.ext
      have : ((c : C t) : G) * (x : G) = ((c : C t) : G) * t := by rw [hc', hct]
      simpa [tInC] using mul_left_cancel this
    · have hsj := (even_outside_conjugate n hn (j.val : ℤ))
      have hsj' : IsConj (s n) (r n ^ (2 * j.val) * s n) := by
        rw [show ((2 : ℤ) * (j.val : ℤ)) = ((2 * j.val : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast] at hsj
        exact hsj
      have h1 := φ.map_isConj hsj'
      rw [← hj, hφa] at h1
      exact hxy.trans h1.symm
  · rintro (rfl | hx)
    · exact IsConj.refl _
    · have hxG : IsConj (x : G) ((e' (s n) : S) : G) := (C t).subtype.map_isConj hx
      exact hxG.trans (hinvconj _ hs2)

theorem card_isConj_filter_mul_card_centralizer {H : Type*} [Group H] [Fintype H] (g : H)
    [DecidablePred fun x : H => IsConj x g] :
    (Finset.univ.filter fun x : H => IsConj x g).card *
      Nat.card (Subgroup.centralizer ({g} : Set H)) = Nat.card H := by
  rw [Nat.card_eq_fintype_card (α := H), ← MulAction.card_conjClass_mul_card_centralizer g]
  congr 1
  have horb : MulAction.orbit (ConjAct H) g = {x | IsConj x g} := by
    ext x
    exact ConjAct.mem_orbit_conjAct
  rw [horb, Nat.card_eq_card_toFinset]
  congr 1
  ext x
  simp

theorem classWeight_centered {n : ℕ} (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) (α : C t → ℂ)
    (hα : ∀ x y : C t, α (y * x * y⁻¹) = α x) :
    classWeight (C t) α t = α (tInC t) / Nat.card (C t) +
      α (centeredReflection hn e' hcent) /
        Nat.card (Subgroup.centralizer ({centeredReflection hn e' hcent} : Set (C t))) := by
  set sC := centeredReflection hn e' hcent with hsC
  have hts : ¬ IsConj (tInC t) sC := by
    intro h
    obtain ⟨c, hc⟩ := h
    have hct : ((c : C t) : G) * t = t * ((c : C t) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (c : C t).2
    have hc' := congrArg (fun w : C t => (w : G)) hc
    simp only [Subgroup.coe_mul, tInC] at hc'
    have hst : ((e' (s n) : S) : G) = t := by
      have : ((e' (s n) : S) : G) * ((c : C t) : G) = t * ((c : C t) : G) := by
        rw [← hct]
        exact hc'.symm
      exact mul_right_cancel this
    rw [← hcent, ← centered_z_eq hn e'] at hst
    have hsz := e'.injective (Subtype.ext hst)
    have hz1 := r_zpow_mul_s_ne_one n (by omega) (-(half n : ℤ))
    apply hz1
    rw [hsz, z, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero]
  have hsplit : ∀ x : C t, (if IsConj (x : G) t then α x else 0) =
      (if x = tInC t then α (tInC t) else 0) + (if IsConj x sC then α sC else 0) := by
    intro x
    have hiff := isConj_centered_involution_iff hn S0 f0 hG e' hcent x
    by_cases hxt : x = tInC t
    · subst hxt
      rw [ite_eq_left (hiff.mpr (Or.inl rfl)), ite_eq_left rfl, ite_eq_right hts, add_zero]
    · by_cases hxs : IsConj x sC
      · have hαx : α x = α sC := by
          obtain ⟨c, hc⟩ := hxs
          rw [← hα x (c : C t)]
          congr 1
          have hc' : (c : C t) * x = sC * (c : C t) := hc
          rw [hc']
          group
        rw [ite_eq_left (hiff.mpr (Or.inr hxs)), ite_eq_right hxt, ite_eq_left hxs, zero_add, hαx]
      · rw [ite_eq_right (fun h => (hiff.mp h).elim hxt hxs), ite_eq_right hxt, ite_eq_right hxs,
          add_zero]
  have hsum : (∑ x : C t, if IsConj (x : G) t then α x else 0) =
      α (tInC t) + ((Finset.univ.filter fun x : C t => IsConj x sC).card : ℂ) * α sC := by
    rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (tInC t) (fun _ => α (tInC t)),
      ite_eq_left (Finset.mem_univ _), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_isConj_filter_mul_card_centralizer sC
  have hC0 : (Nat.card (C t) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hZ0 : (Nat.card (Subgroup.centralizer ({sC} : Set (C t))) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcardC : ((Finset.univ.filter fun x : C t => IsConj x sC).card : ℂ) =
      Nat.card (C t) / Nat.card (Subgroup.centralizer ({sC} : Set (C t))) := by
    rw [eq_div_iff hZ0]
    exact_mod_cast hcard
  rw [classWeight, hsum, hcardC]
  field_simp

end ClassWeights

theorem actual_principal_theta_of_family {G : Type} [Group G] [Fintype G]
    (hindex : ∀ H : Subgroup G, H.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1) (k : ℕ)
    (φ : C t → ℂ) (hφ1 : φ 1 = q) (hφnc : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ q)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e k φ
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) (e' (r n) : G) (fun x => 1 - cyclicLinearCharacter (e' (r n) : G) (modulus n)
          ((modulus n / 2 : ℕ) : ℤ) x) =
      1 + (δ₁ : ℂ) • (basis.representation χ₁).character +
        (δ₂ : ℂ) • (basis.representation χ₂).character +
          (δ₃ : ℂ) • (basis.representation χ₃).character := by
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, hnd, -, -, -, -, -, hB, -, hodd, hsec, hrel⟩ := hfam
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := hnd
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  have hf₁ : (basis.representation χ₁).character 1 = f₁ := (basis_character_one basis χ₁).1
  have hf₂ : (basis.representation χ₂).character 1 = f₂ := (basis_character_one basis χ₂).1
  have hf₃ : (basis.representation χ₃).character 1 = f₃ := (basis_character_one basis χ₃).1
  have hoddF : ∀ c ∈ B, (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
      (c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃) := by
    intro c hc
    rw [← hodd c hc, (basis_character_one basis c).1]
    constructor
    · rintro ⟨d, hd, hcd⟩
      rwa [Nat.cast_injective hcd]
    · intro h
      exact ⟨_, h, rfl⟩
  let Φ : G → ℂ := fun g => if h : g ∈ C t then φ ⟨g, h⟩ else 0
  have hΦC : ∀ (y : G) (hy : y ∈ C t), Φ y = φ ⟨y, hy⟩ := fun y hy => by
    simp only [Φ, hy, dite_true]
  have hΦ1 : Φ 1 = q := by
    rw [hΦC 1 (one_mem _)]
    exact hφ1
  have hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂ := by
    rw [hcent]
    obtain ⟨y, hy, hyq⟩ := hφnc
    refine ⟨1, one_mem _, y, y.2, by simp, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hy
    · rw [hΦ1, hΦC y y.2]
      exact fun h => hyq h.symm
  have hχ₁t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₁).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy]
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).1
  have hχ₂t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₂).character ((e' (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * e * Φ y := by
    rw [hcent]
    intro y hy hyo
    rw [hΦC y hy, (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.1]
    ring
  have hχ₃t : ∀ y ∈ Subgroup.centralizer {(e' (r n) : G) ^ (modulus n / 2)},
      Odd (orderOf y) →
      (basis.representation χ₃).character ((e' (r n) : G) ^ (modulus n / 2) * y) = -δ₃ := by
    rw [hcent]
    intro y hy hyo
    exact (hsec ⟨y, hy⟩ (by rw [Subgroup.orderOf_mk]; exact hyo)).2.2.1
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by simp)
  rw [hf₁, hf₂, hf₃] at hrel1
  have hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 := by
    exact_mod_cast hrel1
  exact (nonsimple_principal_Fourier_odd_degree_product hindex hn e' basis ideal principal
    hprincipal χ₁ χ₂ χ₃ hχ₁B hχ₂B hχ₃B h01 h02 h03 h12 h13 h23 hoddF f₁ f₂ f₃ hf₁ hf₂ hf₃ q hq3
    hqodd e δ₁ δ₂ δ₃ he hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1 hχ₁t hχ₂t hχ₃t hdeg).2.1


theorem block_coefficients_eq {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index} (k l : basis.index → ℂ)
    (h : ∀ g, ∑ d ∈ B, k d * (basis.representation d).character g =
      ∑ d ∈ B, l d * (basis.representation d).character g) {c : basis.index} (hc : c ∈ B) :
    k c = l c := by
  rw [← basis_combination_coefficient basis hc k, ← basis_combination_coefficient basis hc l]
  congr 1
  funext g
  exact h g

theorem actual_global_principal_column {G : Type} [Group G] [Fintype G]
    (hindex : ∀ H : Subgroup G, H.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq3 : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1) (k : ℕ)
    (φ : C t → ℂ) (hφ1 : φ 1 = q) (hφnc : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ q)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e k φ
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄) :
    ∃ ξ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ξ ≠ principal ∧ ξ ≠ χ₁ ∧ ξ ≠ χ₂ ∧ ξ ≠ χ₃ ∧
      (basis.representation ξ).character 1 =
        (Module.finrank ℂ (basis.representation χ₁).vector : ℂ) + δ₁ ∧
      (basis.representation ξ).character t = δ₁ * (1 + e * q) ∧
      ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        characterPairing (fun x : Subgroup.zpowers (e' (r n) : G) =>
            (basis.representation c).character x)
          (fun x => 1 - cyclicLinearCharacter (e' (r n) : G) (modulus n) 2 x) =
        ((if c = principal then 1 else 0) + δ₁ * (if c = χ₁ then 1 else 0) -
          δ₁ * (if c = ξ then 1 else 0) : ℤ) := by
  have hΘ := actual_principal_theta_of_family hindex hn e' hcent basis ideal principal hprincipal
    localBasis localPrincipal q hq3 hqodd e he k φ hφ1 hφnc δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam
  obtain ⟨hf₁1, hf₂1, hf₃1, hf₄1, hsign, hδ₄₂, hf₄₂, -, -⟩ := hdeg
  obtain ⟨hcoefΘ, hcoefE, hΘsum, hEsum, -, hE1, -, -, -, -, -, -, -, -, -, -,
      c₁, c₂, c₃, δ₁', δ₂', δ₃', ε, ψ', hc₁B, hc₂B, hc₃B, hc12, hc13, hc23, hc₁p, hc₂p, hc₃p,
      hδ₁', hδ₂', hδ₃', hε, -, hψ', -, hEform, hθform, hηform, -, -, -, -, -⟩ :=
    even_cyclic_principal_Fourier_family hn e' basis ideal principal hprincipal
  beta_reduce at hcoefΘ hcoefE hΘsum hEsum hθform hηform
  obtain ⟨-, hδ₁, hδ₂, hδ₃, hδ₄, hnd, -, -, -, -, -, hB, -, hodd, hsec, -⟩ := hfam
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  set M := modulus n with hMdef
  set ρ : G := (e' (r n) : G) with hρ
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hpB : principal ∈ B := hmem principal (by simp)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₃B : χ₃ ∈ B := hmem χ₃ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := hnd
  have hM8 : 8 ≤ M := by
    have : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hMdef, modulus] using this
  have hmatch : ∀ d ∈ B,
      (multiplicityColumn basis ρ M 0 d - multiplicityColumn basis ρ M ((M / 2 : ℕ) : ℤ) d) =
        (if d = principal then 1 else 0) + δ₁ * (if d = χ₁ then 1 else 0) +
          δ₂ * (if d = χ₂ then 1 else 0) + δ₃ * (if d = χ₃ then 1 else 0) := by
    intro d hd
    have h := block_coefficients_eq basis
      (fun c => ((multiplicityColumn basis ρ M 0 c -
        multiplicityColumn basis ρ M ((M / 2 : ℕ) : ℤ) c : ℤ) : ℂ))
      (fun c => (((if c = principal then 1 else 0) + δ₁ * (if c = χ₁ then 1 else 0) +
          δ₂ * (if c = χ₂ then 1 else 0) + δ₃ * (if c = χ₃ then 1 else 0) : ℤ) : ℂ))
      (fun g => by
        rw [← hΘsum g, hΘ, basis_combination_four basis hpB hχ₁B hχ₂B hχ₃B, hprincipal]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]) hd
    exact_mod_cast h
  have hδne : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → δ ≠ 0 := by
    rintro δ (rfl | rfl) <;> norm_num
  have hc₁eq : δ₁' = (if c₁ = χ₁ then δ₁ else 0) + (if c₁ = χ₂ then δ₂ else 0) +
      (if c₁ = χ₃ then δ₃ else 0) := by
    have h1 := hθform c₁ hc₁B
    have h2 := hmatch c₁ hc₁B
    rw [h1] at h2
    simp only [ite_eq_right hc₁p, ite_eq_right hc12, ite_eq_right hc13] at h2
    split_ifs at h2 ⊢ <;> linarith
  have hχc : ∀ (χ : basis.index) (δ : ℤ), χ ∈ B → χ ≠ principal → (δ = 1 ∨ δ = -1) →
      (if χ = principal then 1 else 0) + δ₁ * (if χ = χ₁ then 1 else 0) +
        δ₂ * (if χ = χ₂ then 1 else 0) + δ₃ * (if χ = χ₃ then 1 else 0) = δ →
      χ = c₁ ∨ χ = c₂ ∨ χ = c₃ := by
    intro χ δ hχB hp hδ hval
    by_contra hcon
    simp only [not_or] at hcon
    have h1 := hθform χ hχB
    have h2 := hmatch χ hχB
    rw [h1, hval] at h2
    simp only [ite_eq_right hp, ite_eq_right hcon.1, ite_eq_right hcon.2.1,
      ite_eq_right hcon.2.2] at h2
    exact hδne δ hδ (by linarith)
  have hχ₁c := hχc χ₁ δ₁ hχ₁B (Ne.symm h01) hδ₁ (by simp [Ne.symm h01, h12, h13])
  have hχ₂c := hχc χ₂ δ₂ hχ₂B (Ne.symm h02) hδ₂ (by simp [Ne.symm h02, Ne.symm h12, h23])
  have hχ₃c := hχc χ₃ δ₃ hχ₃B (Ne.symm h03) hδ₃ (by
    simp [Ne.symm h03, Ne.symm h13, Ne.symm h23])
  have hM4 : 1 ≤ M / 4 - 1 := by omega
  obtain ⟨hξB, hξp, hξc₁, hξc₂, hξc₃⟩ := hψ' 1 le_rfl hM4
  have hξχ : ψ' 1 ≠ χ₁ ∧ ψ' 1 ≠ χ₂ ∧ ψ' 1 ≠ χ₃ := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases hχ₁c with h' | h' | h'
      exacts [hξc₁ (h.trans h'), hξc₂ (h.trans h'), hξc₃ (h.trans h')]
    · rcases hχ₂c with h' | h' | h'
      exacts [hξc₁ (h.trans h'), hξc₂ (h.trans h'), hξc₃ (h.trans h')]
    · rcases hχ₃c with h' | h' | h'
      exacts [hξc₁ (h.trans h'), hξc₂ (h.trans h'), hξc₃ (h.trans h')]
  have hE := hEform 1 le_rfl hM4
  have hEone := hE1 1 le_rfl hM4
  have ht2 : orderOf t = 2 := by
    rw [← hcent]
    have hz : ((e' (z n) : S) : G) = (e' (r n) : G) ^ (modulus n / 2) := by
      rw [z, map_pow, Subgroup.coe_pow, modulus_div_two n (by omega)]
    rw [← hz, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_z n (by omega)]
  have hEt := ((cyclic_principal_Fourier_projection_values hn e' basis ideal principal
    hprincipal).2.2 t t 1 (mul_one t) (Commute.one_right t) ht2 (by simp)).2.1 1 le_rfl hM4
  beta_reduce at hE hEone hEt
  have hvE1 := congrFun hE 1
  have hvEt := congrFun hE t
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at hvE1 hvEt
  rw [hEone] at hvE1
  rw [hEt] at hvEt
  obtain ⟨hv1, hv2, hv3, hv4, hvψ, hvν⟩ := hsec 1 (by simp)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hv1 hv2 hv3 hv4 hvψ hvν
  have hξcases : ψ' 1 = χ₄ ∨ (∃ j ∈ Finset.Icc 1 (k - 1), ψ j = ψ' 1) ∨
      (∃ i ∈ Finset.range k, ν i = ψ' 1) := by
    have h := hξB
    rw [hB] at h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at h
    rcases h with ((h | h | h | h | h) | h) | h
    · exact absurd h hξp
    · exact absurd h hξχ.1
    · exact absurd h hξχ.2.1
    · exact absurd h hξχ.2.2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hc₁cases : c₁ = χ₁ ∨ c₁ = χ₂ ∨ c₁ = χ₃ := by
    by_contra h
    simp only [not_or] at h
    rw [ite_eq_right h.1, ite_eq_right h.2.1, ite_eq_right h.2.2] at hc₁eq
    exact hδne δ₁' hδ₁' (by linarith)
  have hfξpos : 0 < Module.finrank ℂ (basis.representation (ψ' 1)).vector :=
    (basis_character_one basis (ψ' 1)).2
  rw [(basis_character_one basis (ψ' 1)).1] at hvE1
  obtain ⟨X, hX, hXcases⟩ : ∃ X : ℤ, (basis.representation (ψ' 1)).character t = X ∧
      ((ψ' 1 = χ₄ ∧ X = δ₄ * (1 - e * q)) ∨ X = δ₁ * (1 + e * q) ∨
        X = -(δ₁ * (1 + e * q))) := by
    rcases hξcases with h | ⟨j, hj, h⟩ | ⟨i, hi, h⟩
    · refine ⟨δ₄ * (1 - e * q), ?_, Or.inl ⟨h, rfl⟩⟩
      rw [h, hv4]
      push_cast
      ring
    · refine ⟨δ₁ * (1 + e * q), ?_, Or.inr (Or.inl rfl)⟩
      rw [← h, hvψ j hj]
      push_cast
      ring
    · refine ⟨-(δ₁ * (1 + e * q)), ?_, Or.inr (Or.inr rfl)⟩
      rw [← h, hvν i hi]
      push_cast
      ring
  rw [hX] at hvEt
  set fξ := Module.finrank ℂ (basis.representation (ψ' 1)).vector with hfξ
  have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  rcases hc₁cases with hc | hc | hc
  ·
    rw [hc, ite_eq_left rfl, ite_eq_right h12, ite_eq_right h13] at hc₁eq
    rw [hc, (basis_character_one basis χ₁).1] at hvE1
    rw [hc, hv1] at hvEt
    have hA : (0 : ℤ) = 1 + δ₁' * (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) +
        ε * fξ := by exact_mod_cast hvE1
    have hT : (0 : ℤ) = 1 + δ₁' * (δ₁ * e * q) + ε * X := by exact_mod_cast hvEt
    have hf₁1' : (1 : ℤ) < Module.finrank ℂ (basis.representation χ₁).vector := by
      exact_mod_cast hf₁1
    have hfξ1 : (0 : ℤ) < fξ := by exact_mod_cast hfξpos
    have key : ε = -δ₁ ∧ (fξ : ℤ) = Module.finrank ℂ (basis.representation χ₁).vector + δ₁ ∧
        X = δ₁ * (1 + e * q) := by
      subst hc₁eq
      rcases hδ₁ with rfl | rfl <;> rcases hε with rfl | rfl <;> rcases he with rfl | rfl <;>
        omega
    obtain ⟨hεδ, hfξeq, hXeq⟩ := key
    refine ⟨ψ' 1, hξB, hξp, hξχ.1, hξχ.2.1, hξχ.2.2, ?_, ?_, ?_⟩
    · rw [(basis_character_one basis (ψ' 1)).1]
      exact_mod_cast hfξeq
    · rw [hX, hXeq]
      push_cast
      ring
    · intro c hcB
      have h1 := hcoefE 1 c
      have h2 := hηform 1 le_rfl hM4 c hcB
      simp only [Nat.cast_one, mul_one] at h1 h2
      rw [h1, h2, hc, hc₁eq, hεδ]
      push_cast
      ring
  ·
    exfalso
    rw [hc, ite_eq_right (Ne.symm h12), ite_eq_left rfl, ite_eq_right h23] at hc₁eq
    rw [hc, (basis_character_one basis χ₂).1] at hvE1
    rw [hc, hv2] at hvEt
    have hA : (0 : ℤ) = 1 + δ₁' * (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) +
        ε * fξ := by exact_mod_cast hvE1
    have hT : (0 : ℤ) = 1 + δ₁' * (-(δ₂ * e * q)) + ε * X := by exact_mod_cast hvEt
    have hf₂1' : (1 : ℤ) < Module.finrank ℂ (basis.representation χ₂).vector := by
      exact_mod_cast hf₂1
    have hfξ1 : (0 : ℤ) < fξ := by exact_mod_cast hfξpos
    subst hc₁eq
    rcases hXcases with ⟨-, hXv⟩ | hXv | hXv <;> subst hXv <;>
      rcases hδ₁ with rfl | rfl <;> rcases hδ₂ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      rcases he with rfl | rfl <;> try (rcases hδ₄ with rfl | rfl) <;> omega
  ·
    exfalso
    rw [hc, ite_eq_right (Ne.symm h13), ite_eq_right (Ne.symm h23), ite_eq_left rfl] at hc₁eq
    rw [hc, (basis_character_one basis χ₃).1] at hvE1
    rw [hc, hv3] at hvEt
    have hT : (0 : ℤ) = 1 + δ₁' * (-δ₃) + ε * X := by exact_mod_cast hvEt
    subst hc₁eq
    rcases hXcases with ⟨-, hXv⟩ | hXv | hXv <;> subst hXv <;>
      rcases hδ₁ with rfl | rfl <;> rcases hδ₃ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      rcases he with rfl | rfl <;> try (rcases hδ₄ with rfl | rfl) <;> omega

theorem extendedCentralizer_le_centralizer_of_pow {G : Type*} [Group G] {x t : G}
    (ht2 : t * t = 1) {m : ℕ} (hm : x ^ m = t) :
    extendedCentralizer x ≤ Subgroup.centralizer {t} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : g⁻¹ * t * g = t := by
    have hmap : ∀ y : G, g⁻¹ * y ^ m * g = (g⁻¹ * y * g) ^ m := fun y => by
      have := map_pow (MulAut.conj g⁻¹) y m
      simpa [MulAut.conj_apply] using this
    rw [← hm, hmap x]
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg, inv_pow, hm, htinv]
  have htg : t * g = g * t := by
    calc t * g = g * (g⁻¹ * t * g) := by group
      _ = g * t := by rw [hconj]
  exact htg.symm

theorem sum_weighted_powers_comm {ι : Type*} (A : Finset ι) (K : ℂ) (a b : ι → ℂ)
    (g : ι → ℕ → ℂ) (M : ℕ) (w : ℕ → ℂ) :
    K * ∑ i ∈ A, a i * (∑ v ∈ Finset.range M, w v * g i v) / b i =
      ∑ v ∈ Finset.range M, w v * (K * ∑ i ∈ A, a i * g i v / b i) := by
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fourier_summed_brauer_order_formula {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {t : G} (ht2 : t * t = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (ρ : C t) {M : ℕ} (hM : ∃ m, M = 2 ^ m) (hρM : orderOf (ρ : G) = M)
    (hρt : (ρ : G) ^ (M / 2) = t) (w : ℕ → ℂ) (hw0 : w 0 = 0) :
    (Nat.card G : ℂ) * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character t * (basis.representation χ).character t *
        (∑ v ∈ Finset.range M, w v * (basis.representation χ).character ((ρ : G) ^ v)) /
          (basis.representation χ).character 1 =
    (Nat.card (C t) : ℂ) * Nat.card (C t) * Nat.card (C t) *
      ∑ α ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        classWeight (C t) (localBasis.representation α).character t *
          classWeight (C t) (localBasis.representation α).character t *
          (∑ v ∈ Finset.range M, w v * (localBasis.representation α).character (ρ ^ v)) /
            (localBasis.representation α).character 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := hM
  have hper : ∀ v ∈ Finset.range (2 ^ m), w v ≠ 0 →
      (Nat.card G : ℂ) *
          ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation χ).character t * (basis.representation χ).character t *
              (basis.representation χ).character ((ρ : G) ^ v) /
                (basis.representation χ).character 1 =
        (Nat.card (C t) : ℂ) * Nat.card (C t) * Nat.card (C t) *
          ∑ α ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
            classWeight (C t) (localBasis.representation α).character t *
              classWeight (C t) (localBasis.representation α).character t *
                (localBasis.representation α).character (ρ ^ v) /
                  (localBasis.representation α).character 1 := by
    intro v hv hwv
    have hv0 : v ≠ 0 := fun h => hwv (h ▸ hw0)
    have hvM : (ρ : G) ^ v ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hρM] at this
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) this
      exact absurd (Finset.mem_range.mp hv) (by omega)
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_half ⟨m, rfl⟩ hρM hvM
    rw [hρt] at hk
    have hord : orderOf (((ρ ^ v : C t)) : G) ∣ 2 ^ m := by
      rw [Subgroup.coe_pow, ← hρM]
      exact orderOf_pow_dvd v
    have hEH : extendedCentralizer (((ρ ^ v : C t)) : G) ≤ C t := by
      rw [Subgroup.coe_pow]
      exact extendedCentralizer_le_centralizer_of_pow ht2 hk
    have hform := (brauer_principal_order_formula basis ideal 2 principal hprincipal ht2 ht2
      (C t) (ρ ^ v) m hord hEH localBasis localPrincipal hlocalPrincipal).1 1
      (one_mem _) (by simp)
    simpa only [mul_one, Subgroup.coe_pow] using hform
  rw [sum_weighted_powers_comm, sum_weighted_powers_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  by_cases hwv : w v = 0
  · rw [hwv, zero_mul, zero_mul]
  · rw [hper v hv hwv]

end CFSG.Semidihedral.Principal
