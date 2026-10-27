module

public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerTorusColumnSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFivePowerDefectColumn
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizer

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_pure_five_power_alternating_five_torus_column_aligns_two_odd_principal_characters
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (a : ℕ) (ha : 1 ≤ a) (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (ideal₂ ideal₅ : Ideal ComplexAlgebraicIntegers) [ideal₂.IsMaximal] [ideal₅.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] [CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5] :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let J : Subgroup G := ⁅K, K⁆
    let θ : J → ℂ := fun j => (Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1
    let B₂ := coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal
    ((q : ℤ) + e) / 2 = 5 ^ a →
    Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) →
    IsCyclic W ∧ Nat.card W = 5 ^ a ∧ W ⊔ J = K ∧ W ⊓ J = ⊥ ∧
      (∀ w ∈ W, ∀ j ∈ J, w * j = j * w) ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧ t ∈ J ∧
      Nat.card (C t) = 2 * q * (q ^ 2 - 1) ∧
      (∃ (E : Subgroup G) (σ : E ≃* Equiv.Perm (Fin 5)), E ≤ H ∧ J ≤ E ∧ W ⊔ E = H ∧ W ⊓ E = ⊥ ∧
        (∀ x : E, (x : G) ∈ J ↔ σ x ∈ alternatingGroup (Fin 5)) ∧
        ∀ x : E, ∀ w ∈ W, (x : G) * w * (x : G)⁻¹ = w ^ ((Equiv.Perm.sign (σ x) : ℤˣ) : ℤ)) ∧
      Nat.card H = 120 * 5 ^ a ∧
      (∀ basisJ : FiniteIrreducibleCharacterBasis J,
        (∃ l : basisJ.index, (basisJ.representation l).character = θ) ∧
        ∀ l : basisJ.index, Module.finrank ℂ (basisJ.representation l).vector = 5 →
          (basisJ.representation l).character = θ) ∧ θ 1 = 5 ∧
      ∀ lam : W →* ℂˣ, orderOf lam = 5 →
        (∃ ψ : K → ℂ, ∀ (k : K) (w : W) (j : J), (k : G) = w * j →
          ψ k = θ j * ((lam w : ℂ) - 1)) ∧
        ∀ ψ : K → ℂ, (∀ (k : K) (w : W) (j : J), (k : G) = w * j →
          ψ k = θ j * ((lam w : ℂ) - 1)) →
        ∃ (χ₁ χ₂ χ₃ χB : basis.index) (δ₁ δ₂ δ₃ η : ℤ),
          let f₁ := Module.finrank ℂ (basis.representation χ₁).vector
          let f₂ := Module.finrank ℂ (basis.representation χ₂).vector
          let f₃ := Module.finrank ℂ (basis.representation χ₃).vector
          let B₅ := coefficientBlock basis (localizedComplexIntegerRing ideal₅) χ₂
          [χ₁, χ₂, χ₃].Nodup ∧ χ₁ ∈ B₂ ∧ χ₂ ∈ B₂ ∧ χ₃ ∈ B₂ ∧ Odd f₁ ∧ Odd f₂ ∧ Odd f₃ ∧
          1 < f₁ ∧ 1 < f₂ ∧ 1 < f₃ ∧
          ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
            (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
          χB ≠ χ₂ ∧ χB ≠ χ₃ ∧ (η = 1 ∨ η = -1) ∧
          1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 ∧ f₁ * f₂ = q ^ 2 * f₃ ∧
          5 ∣ f₂ ∧ 5 ∣ f₃ ∧ ¬ 5 ∣ f₁ ∧
          padicValNat 5 (Nat.card G) = a + padicValNat 5 f₂ ∧
          padicValNat 5 (Nat.card G) = a + padicValNat 5 f₃ ∧
          coefficientBlockDefect basis ideal₅ 5 χ₂ W ∧
          (∀ other : basis.index, coefficientBlockDefect basis ideal₅ 5 other W → other ∈ B₅) ∧
          χ₂ ∈ B₅ ∧ χ₃ ∈ B₅ ∧ χB ∈ B₅ ∧
          inducedFunction K ψ = (fun g => -(δ₂ : ℂ) * (basis.representation χ₂).character g +
            δ₃ * (basis.representation χ₃).character g +
              η * (basis.representation χB).character g) ∧
          (∀ g : G, inducedFunction K ψ g ≠ 0 → ∀ x y : G, x * y = g → Commute x y →
            (∃ k : ℕ, orderOf x = 5 ^ k) → ¬ 5 ∣ orderOf y →
              ∃ w ∈ W, Subgroup.zpowers w = W ∧ IsConj x w) ∧
          (basis.representation χ₂).character t = -(e * δ₂ * q) ∧
          (basis.representation χ₃).character t = -δ₃ ∧
          (basis.representation χB).character t = η * (1 - e * q) ∧
          (basis.representation χB).character 1 = η * (δ₂ * f₂ - δ₃ * f₃) ∧
          0 < η * (δ₂ * (f₂ : ℤ) - δ₃ * f₃) ∧
          (f₁ : ℚ) - e * δ₁ * q ≠ 0 ∧
          (Nat.card G : ℚ) / (Nat.card (C t) : ℚ) ^ 2 =
            ((q - e) / 2) * (f₁ * (f₁ + δ₁)) / (f₁ - e * δ₁ * q) ^ 2 := by
  intro q e s₀ V D W H K J θ B₂ hqa hK5
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hzt, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hC, hW1, hWcyc, hWodd, hWm, ⟨hsup, hdisj, -⟩, hcentw, -, -, ⟨d, -, -, -, -, -, ⟨eD⟩,
      -, P, hP⟩, -, -, -, hKH, hinvH, -, -, -, hR, -, -, -, -, -, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have : IsCyclic W := hWcyc
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have he : e = 1 ∨ e = -1 := by
    change (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hqodd : Odd q := hpodd.pow
  have hqe : (q : ℤ) + e = 2 * 5 ^ a := by
    have heven : (2 : ℤ) ∣ (q : ℤ) + e := by
      obtain ⟨k, hk⟩ := hqodd
      have hk' : (q : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      rcases he with h | h
      · exact ⟨k + 1, by rw [h, hk']; ring⟩
      · exact ⟨k, by rw [h, hk']; ring⟩
    have h := Int.ediv_mul_cancel heven
    rw [hqa] at h
    linarith
  have hWcard : Nat.card W = 5 ^ a := by
    have h : (Nat.card W : ℤ) = 5 ^ a := by rw [hWm, hqa]
    exact_mod_cast h
  have hdih' : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4) :=
    ⟨P, ⟨(Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP).trans eD)⟩⟩
  obtain ⟨hWJ, hWJinf, hcomm, hJH, hJiso, hEσ, hHcard⟩ :=
    cyclic_torus_alternating_five_structure W hWodd hKH hinvH hR hK5 hdih'
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hWD : W ≤ D := le_sup_right.trans hsup.le
  have htK : t ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWD hw) t htV).symm
  have hWleCJ : W ≤ Subgroup.centralizer (J : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hcomm w hw j hj).symm
  have htJ : t ∈ J := by
    have hKle : K ≤ W ⊔ J := hWJ.ge
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mul_eq_of_mem_sup_of_le_centralizer hWleCJ (hKle htK)
    have hwjc : w * j = j * w := hcomm w hw j hj
    have ht1 : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
    have hw2 : w ^ 2 = (j ^ 2)⁻¹ := by
      rw [← hwj, (Commute.mul_pow hwjc 2)] at ht1
      exact eq_inv_of_mul_eq_one_left ht1
    have hw2W : w ^ 2 ∈ W ⊓ J := ⟨W.pow_mem hw 2, hw2 ▸ J.inv_mem (J.pow_mem hj 2)⟩
    rw [hWJinf, Subgroup.mem_bot] at hw2W
    have hw1 : w = 1 := by
      have hodd' : Odd (orderOf w) := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw)
      have h2 := orderOf_dvd_of_pow_eq_one hw2W
      have h1 : orderOf w = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact h
        · rw [h] at hodd'
          exact absurd hodd' (by decide)
      exact orderOf_eq_one_iff.mp h1
    rw [← hwj, hw1, one_mul]
    exact hj
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hDcard, -, -, -, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hDeq : D = C t ⊓ Subgroup.centralizer {s₀} := centralizer_zpowers_sup_zpowers t s₀
  have hDcard' : Nat.card D = 4 * 5 ^ a := by rw [hDcard, hWcard]
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hGa : 5 ^ (a + 1) ∣ Nat.card G := by
    have h := Subgroup.card_subgroup_dvd_card H
    rw [hHcard, hWcard] at h
    exact (show 5 ^ (a + 1) ∣ 120 * 5 ^ a from ⟨24, by ring⟩).trans h
  have hWC : W ≤ C t := hWD.trans (fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx t htV).symm)
  have htw : ∀ w ∈ W, Commute t w := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (hWD hw) t htV)
  have hgenord : ∀ w : W, Subgroup.zpowers (w : G) = W → orderOf (w : G) = 5 ^ a := by
    intro w hw
    rw [← Nat.card_zpowers, hw, hWcard]
  have hgen1 : ∀ w : W, Subgroup.zpowers (w : G) = W → (w : G) ≠ 1 := by
    intro w hw h1
    have h := hgenord w hw
    rw [h1, orderOf_one] at h
    have : 1 < 5 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hcentgen : ∀ w : W, Subgroup.zpowers (w : G) = W →
      Subgroup.centralizer {t * (w : G)} = D := by
    intro w hw
    rw [centralizer_mul_eq_inf_of_coprime (htw w w.2) (by
      rw [ht2, hgenord w hw]
      exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 2 5)))]
    exact hcentw w w.2 (hgen1 w hw)
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψf, νf, hfam,
      hdeg, -, hOF⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f hp
      hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal hlocalPrincipal
  obtain ⟨hX₁, hX₂, hO₁, hO₂⟩ := hOF S fS hcent
  obtain ⟨hlφ, hδ₁s, hδ₂s, hδ₃s, -, hnd, -, -, -, -, -, hB, -, hoddB, hsec, hrel⟩ := hfam
  obtain ⟨hf1gt, hf2gt, hf3gt, -, hsigns, hδ₄, hf₄, hprod, -⟩ := hdeg
  have hcard' : Nat.card F = q := hcard
  have heF : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = e := by rw [hcard']
  rw [heF] at hsec hX₁ hX₂ hO₁ hO₂
  rw [hcard'] at hX₁ hX₂ hO₁ hO₂ hprod hφ1
  obtain ⟨lφ, hlφB, -, hφchar, hφdeg, hφker⟩ := hlφ
  rw [hcard'] at hφdeg
  have hφgen : ∀ w : W, Subgroup.zpowers (w : G) = W →
      (localBasis.representation lφ).character ⟨w, hWC w.2⟩ = -e := by
    intro w hw
    have hy : orderOf (⟨w, hWC w.2⟩ : C t) = 5 ^ a := by
      rw [Subgroup.orderOf_mk]
      exact hgenord w hw
    have hyY : (⟨w, hWC w.2⟩ : C t) ∈
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) :=
      mem_of_index_eq_two_of_odd_orderOf hY (by rw [hy]; exact Odd.pow (by decide))
    exact local_degree_q_value_of_five_power n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd
      hf hmodel hN ha he hqe ideal₂ localBasis localPrincipal hlocalPrincipal lφ hlφB hφdeg hφker
      ⟨w, hWC w.2⟩ hy hyY
  rw [← hφchar] at hsec
  have hoddgen : ∀ w : W, Subgroup.zpowers (w : G) = W → Odd (orderOf (⟨w, hWC w.2⟩ : C t)) := by
    intro w hw
    rw [Subgroup.orderOf_mk, hgenord w hw]
    exact Odd.pow (by decide)
  have he2 : (e : ℂ) * e = 1 := by rcases he with h | h <;> rw [h] <;> norm_num
  have hχ₂gen : ∀ w : W, Subgroup.zpowers (w : G) = W →
      (basis.representation χ₂).character (t * w) = δ₂ := by
    intro w hw
    have h : (basis.representation χ₂).character (t * w) =
        -(δ₂ * e * (localBasis.representation lφ).character ⟨w, hWC w.2⟩) :=
      (hsec ⟨w, hWC w.2⟩ (hoddgen w hw)).2.1
    rw [h, hφgen w hw]
    linear_combination (δ₂ : ℂ) * he2
  have hχ₃gen : ∀ w : W, Subgroup.zpowers (w : G) = W →
      (basis.representation χ₃).character (t * w) = -δ₃ := by
    intro w hw
    exact (hsec ⟨w, hWC w.2⟩ (hoddgen w hw)).2.2.1
  have hχ₄gen : ∀ w : W, Subgroup.zpowers (w : G) = W →
      (basis.representation χ₄).character (t * w) = -2 * δ₂ := by
    intro w hw
    have h : (basis.representation χ₄).character (t * w) =
        δ₄ * (1 - e * (localBasis.representation lφ).character ⟨w, hWC w.2⟩) :=
      (hsec ⟨w, hWC w.2⟩ (hoddgen w hw)).2.2.2.1
    rw [h, hφgen w hw, hδ₄]
    push_cast
    linear_combination (-(δ₂ : ℂ)) * he2
  have hφq : (localBasis.representation lφ).character 1 = q := by
    rw [(basis_character_one localBasis lφ).1, hφdeg]
  have hχ₂t : (basis.representation χ₂).character t = -(e * δ₂ * q) := by
    have h := (hsec 1 (by rw [orderOf_one]; exact odd_one)).2.1
    rw [OneMemClass.coe_one, mul_one, hφq] at h
    rw [h]
    ring
  have hχ₃t : (basis.representation χ₃).character t = -δ₃ := by
    have h := (hsec 1 (by rw [orderOf_one]; exact odd_one)).2.2.1
    rwa [OneMemClass.coe_one, mul_one] at h
  have hdC : Nat.card (C t ⊓ Subgroup.centralizer {s₀} : Subgroup G) = 4 * 5 ^ a := by
    rw [← hDeq]
    exact hDcard'
  rw [hC, hdC] at hO₁ hO₂
  have hcases := five_adic_degree_of_order_formula ha he hδ₂s hqe hf₄ hf2gt hGpos hX₂ hO₂ hGa
  have hidx : padicValNat 5 D.index + a = padicValNat 5 (Nat.card G) := by
    have h := Subgroup.index_mul_card D
    rw [hDcard'] at h
    rw [← h, padicValNat.mul Subgroup.index_ne_zero_of_finite (by positivity),
      padicValNat.mul (by norm_num) (by positivity), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (show ¬ 5 ∣ 4 by norm_num), zero_add]
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := W)
  have hg₀W : Subgroup.zpowers (g₀ : G) = W := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact g₀.2
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨x, hx⟩)
      exact ⟨k, by
        show (g₀ : G) ^ k = x
        rw [← Subgroup.coe_zpow, hk]⟩
  obtain ⟨localBasisK⟩ := finiteIrreducibleCharacterBasis_exists (G := K)
  have hdefect : ∀ (χ : basis.index) (c : ℤ), ¬ (5 : ℤ) ∣ c →
      (basis.representation χ).character (t * g₀) = c →
      padicValNat 5 (Nat.card G) =
        a + padicValNat 5 (Module.finrank ℂ (basis.representation χ).vector) →
      coefficientBlockDefect basis ideal₅ 5 χ W := by
    intro χ c hc hχc hv
    exact coefficientBlockDefect_of_torus_generator basis ideal₅ χ W D hg₀W (htw g₀ g₀.2) ht2
      hWcard (hcentgen g₀ hg₀W) hWD hDcard' c hc hχc (by omega)
  have hcolumn := fun (label : basis.index)
      (hlabel : coefficientBlockDefect basis ideal₅ 5 label W) =>
    cyclic_five_power_alternating_five_centralizer_generator_supported_defect_column basis ideal₅
      a ha W hWcard J hWJinf hWJ hJiso hJH hKH hinvH localBasisK label hlabel
  have hnot4 : ¬ 5 ∣ Module.finrank ℂ (basis.representation χ₄).vector := by
    intro h4
    have hv4 : padicValNat 5 (Nat.card G) =
        a + padicValNat 5 (Module.finrank ℂ (basis.representation χ₄).vector) := by
      rcases hcases with ⟨-, h, -⟩ | ⟨-, -, h⟩
      · exact absurd h4 h
      · exact h
    have hdef4 := hdefect χ₄ (-2 * δ₂) (by rcases hδ₂s with rfl | rfl <;> norm_num)
      (by rw [hχ₄gen g₀ hg₀W]; push_cast; ring) hv4
    obtain ⟨-, -, -, -, hcol⟩ := hcolumn χ₄ hdef4
    obtain ⟨lam, hlam⟩ := exists_linear_character_orderOf_five W ha hWcard
    obtain ⟨⟨ψ, hψ⟩, hall⟩ := hcol t htJ ht2 lam hlam
    obtain ⟨-, -, -, ⟨s3, -, hs3⟩, hcoeffB⟩ := hall ψ hψ
    have hc4 := hcoeffB χ₄ (coefficientBlock_self_mem _ _ _)
    have hF := generator_column_coefficient W a hWcard lam hlam
      (fun w : W => (basis.representation χ₄).character (t * w)) (-2 * δ₂) hχ₄gen
    rw [hF] at hc4
    by_cases hmem : χ₄ ∈ s3
    · rcases (hs3 χ₄).1 hmem with h | h <;> rw [hc4] at h <;> rcases hδ₂s with rfl | rfl <;>
        norm_num at h
    · have h := (hs3 χ₄).2 hmem
      rw [hc4] at h
      rcases hδ₂s with rfl | rfl <;> norm_num at h
  obtain ⟨h5f₂, hv₂⟩ : 5 ∣ Module.finrank ℂ (basis.representation χ₂).vector ∧
      padicValNat 5 (Nat.card G) =
        a + padicValNat 5 (Module.finrank ℂ (basis.representation χ₂).vector) := by
    rcases hcases with ⟨h, -, hv⟩ | ⟨h, -, -⟩
    · exact ⟨h, hv⟩
    · exact absurd h hnot4
  have hdef2 := hdefect χ₂ δ₂ (by rcases hδ₂s with rfl | rfl <;> norm_num)
    (by rw [hχ₂gen g₀ hg₀W]) hv₂
  obtain ⟨hθcert, hθ1, -, huniqB, hcol⟩ := hcolumn χ₂ hdef2
  have hdeg1 : ∀ c : basis.index, (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
    fun c => (basis_character_one basis c).1
  have hrel1 := (hrel 1 (by rw [orderOf_one]; exact odd_one)).2.2.1
  rw [hdeg1, hdeg1, hdeg1] at hrel1
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  have hrelZ : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0 := by exact_mod_cast hrel1
  obtain ⟨k₅, hk₅⟩ : (5 : ℤ) ∣ 5 ^ a := dvd_pow_self 5 (by omega)
  have hq5 : ¬ 5 ∣ q := by
    intro h
    obtain ⟨j, hj⟩ := h
    have hj' : (q : ℤ) = 5 * j := by exact_mod_cast hj
    rcases he with h' | h' <;> rw [h'] at hqe <;> omega
  have h5f₃ : 5 ∣ f₃ := by
    have h : 5 ∣ q ^ 2 * f₃ := hprod ▸ Dvd.dvd.mul_left h5f₂ f₁
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h' | h'
    · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h') hq5
    · exact h'
  have hnot1 : ¬ 5 ∣ f₁ := by
    intro h1
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h5f₂
    obtain ⟨k, hk⟩ := h5f₃
    rw [hi, hj, hk] at hrelZ
    push_cast at hrelZ
    rcases hδ₁s with rfl | rfl <;> rcases hδ₂s with rfl | rfl <;> rcases hδ₃s with rfl | rfl <;>
      omega
  have hf₁0 : f₁ ≠ 0 := by omega
  have hf₂0 : f₂ ≠ 0 := by omega
  have hf₃0 : f₃ ≠ 0 := by omega
  have hv₃ : padicValNat 5 f₃ = padicValNat 5 f₂ := by
    have h := congrArg (padicValNat 5) hprod
    rw [padicValNat.mul hf₁0 hf₂0, padicValNat.mul (by positivity) hf₃0, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd hnot1, padicValNat.eq_zero_of_not_dvd hq5] at h
    omega
  have hdef3 := hdefect χ₃ (-δ₃) (by rcases hδ₃s with rfl | rfl <;> norm_num)
    (by rw [hχ₃gen g₀ hg₀W]; push_cast; ring) (by rw [← hf₃def, hv₃]; exact hv₂)
  have hχ₃B : χ₃ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₅) χ₂ :=
    huniqB χ₃ hdef3
  have hmemB₂ : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B₂ := by
    intro c hc
    change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₂) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B₂ : χ₁ ∈ B₂ := hmemB₂ χ₁ (by simp)
  have hχ₂B₂ : χ₂ ∈ B₂ := hmemB₂ χ₂ (by simp)
  have hχ₃B₂ : χ₃ ∈ B₂ := hmemB₂ χ₃ (by simp)
  have hnd3 : [χ₁, χ₂, χ₃].Nodup :=
    hnd.sublist (List.Sublist.cons principal (List.Sublist.cons_cons χ₁ (List.Sublist.cons_cons χ₂
      (List.Sublist.cons_cons χ₃ (List.nil_sublist [χ₄])))))
  have hodd₁ : Odd f₁ := (hoddB χ₁ hχ₁B₂).mpr (Or.inr (Or.inl rfl))
  have hodd₂ : Odd f₂ := (hoddB χ₂ hχ₂B₂).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hodd₃ : Odd f₃ := (hoddB χ₃ hχ₃B₂).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hOF1 : (Nat.card G : ℚ) / (Nat.card (C t) : ℚ) ^ 2 =
      ((q - e) / 2) * (f₁ * (f₁ + δ₁)) / (f₁ - e * δ₁ * q) ^ 2 := by
    have hq1 : 1 ≤ q := by omega
    have hE2 : (e : ℚ) ^ 2 = 1 := by rcases he with h | h <;> rw [h] <;> norm_num
    have hQE : (q : ℚ) + e = 2 * 5 ^ a := by exact_mod_cast hqe
    have hT : (5 : ℚ) ^ a = ((q : ℚ) + e) / 2 := by rw [hQE]; ring
    have hQ2 : ((q : ℚ) ^ 2 - 1) = ((q : ℚ) - e) * ((q : ℚ) + e) := by
      linear_combination hE2
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hqpe : (q : ℚ) + e ≠ 0 := by
      rw [hQE]
      positivity
    have hqme : (q : ℚ) - e ≠ 0 := by
      have h3 : (3 : ℚ) < q := by exact_mod_cast hq
      rcases he with h | h <;> rw [h] <;> push_cast <;> linarith
    have hcC : ((2 * q * (q ^ 2 - 1) : ℕ) : ℚ) = 2 * (q : ℚ) * (((q : ℚ) - e) * ((q : ℚ) + e)) := by
      rw [← hQ2]
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))]
      ring
    have hcD : ((4 * 5 ^ a : ℕ) : ℚ) = 2 * ((q : ℚ) + e) := by
      push_cast
      rw [hT]
      ring
    rw [hC, hO₁, hcC, hcD]
    field_simp
  refine ⟨hWcyc, hWcard, hWJ, hWJinf, hcomm, hJiso, htJ, hC, hEσ, by rw [hHcard, hWcard], hθcert,
    hθ1, fun lam hlam => ?_⟩
  obtain ⟨hψex, hall⟩ := hcol t htJ ht2 lam hlam
  refine ⟨hψex, fun ψ hψ => ?_⟩
  obtain ⟨hAlat, -, hsupp, ⟨s3, hs3card, hs3⟩, hcoeffB⟩ := hall ψ hψ
  have hc2 : characterPairing (inducedFunction K ψ) (basis.representation χ₂).character =
      -δ₂ := by
    rw [hcoeffB χ₂ (coefficientBlock_self_mem _ _ _)]
    exact generator_column_coefficient W a hWcard lam hlam
      (fun w : W => (basis.representation χ₂).character (t * w)) δ₂ hχ₂gen
  have hc3 : characterPairing (inducedFunction K ψ) (basis.representation χ₃).character =
      δ₃ := by
    rw [hcoeffB χ₃ hχ₃B]
    exact (generator_column_coefficient W a hWcard lam hlam
      (fun w : W => (basis.representation χ₃).character (t * w)) (-δ₃) hχ₃gen).trans (neg_neg _)
  have hne0 : ∀ z : ℤ, (z = 1 ∨ z = -1) → (z : ℂ) ≠ 0 := by
    intro z hz
    rcases hz with rfl | rfl <;> norm_num
  have hχ₂s : χ₂ ∈ s3 := by
    by_contra h
    have h' := (hs3 χ₂).2 h
    rw [hc2] at h'
    exact hne0 δ₂ hδ₂s (neg_eq_zero.mp h')
  have hχ₃s : χ₃ ∈ s3 := by
    by_contra h
    have h' := (hs3 χ₃).2 h
    rw [hc3] at h'
    exact hne0 δ₃ hδ₃s h'
  have h23 : χ₂ ≠ χ₃ := fun h => by
    have := hnd3
    rw [h] at this
    simp at this
  obtain ⟨χB, hχBs, hχB2, hχB3⟩ : ∃ χB ∈ s3, χB ≠ χ₂ ∧ χB ≠ χ₃ := by
    by_contra! hall'
    have hsub : s3 ⊆ {χ₂, χ₃} := fun x hx => by
      by_cases h2 : x = χ₂
      · simp [h2]
      · simp [hall' x hx h2]
    have h1 := Finset.card_le_card hsub
    rw [hs3card] at h1
    have h2 : ({χ₂, χ₃} : Finset basis.index).card ≤ 2 := Finset.card_le_two
    omega
  have hs3eq : s3 = {χ₂, χ₃, χB} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hχ₂s
      · exact hχ₃s
      · exact hχBs
    · rw [hs3card, Finset.card_insert_of_notMem (by simp [h23, hχB2.symm]),
        Finset.card_insert_of_notMem (by simp [hχB3.symm]), Finset.card_singleton]
  obtain ⟨η, hη, hcB⟩ : ∃ η : ℤ, (η = 1 ∨ η = -1) ∧
      characterPairing (inducedFunction K ψ) (basis.representation χB).character = η := by
    rcases (hs3 χB).1 hχBs with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  have hAclass : ∀ x g : G, inducedFunction K ψ (g * x * g⁻¹) = inducedFunction K ψ x :=
    fun x g => inducedFunction_conjugate _ _ x g
  have hAexp : inducedFunction K ψ = (fun g => -(δ₂ : ℂ) * (basis.representation χ₂).character g +
      δ₃ * (basis.representation χ₃).character g + η * (basis.representation χB).character g) := by
    funext g
    rw [finiteIrreducibleCharacterBasis_reconstruction basis _ hAclass g]
    rw [← Finset.sum_subset (Finset.subset_univ s3) (fun x _ hx => by
      rw [(hs3 x).2 hx, zero_mul])]
    rw [hs3eq, Finset.sum_insert (by simp [h23, hχB2.symm]),
      Finset.sum_insert (by simp [hχB3.symm]), Finset.sum_singleton, hc2, hc3, hcB]
    ring
  have hspace := coefficientVirtualLattice_le_complex_space basis _ hAlat
  have hχBB : χB ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₅) χ₂ := by
    by_contra h
    have h' := coefficientCharacterSpace_pairing_zero_outside basis _ _ hspace χB h
    rw [hcB] at h'
    exact hne0 η hη h'
  have hW5 : ∀ w ∈ W, Subgroup.zpowers w = W → ¬ IsConj (1 : G) w := by
    intro w _ hw hconj
    rw [isConj_one_right] at hconj
    rw [hconj, Subgroup.zpowers_one_eq_bot] at hw
    rw [← hw, Subgroup.card_bot] at hWcard
    have : 1 < 5 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hA1 : inducedFunction K ψ 1 = 0 := by
    by_contra h
    obtain ⟨w, hwW, hw, hconj⟩ := hsupp 1 h 1 1 (mul_one 1) (Commute.one_left 1)
      ⟨0, by rw [orderOf_one, pow_zero]⟩ (by rw [orderOf_one]; norm_num)
    exact hW5 w hwW hw hconj
  have hAt : inducedFunction K ψ t = 0 := by
    by_contra h
    obtain ⟨w, hwW, hw, hconj⟩ := hsupp t h 1 t (one_mul t) (Commute.one_left t)
      ⟨0, by rw [orderOf_one, pow_zero]⟩ (by rw [ht2]; norm_num)
    exact hW5 w hwW hw hconj
  have hη2 : (η : ℂ) * η = 1 := by rcases hη with rfl | rfl <;> norm_num
  have hδ₂2 : (δ₂ : ℂ) * δ₂ = 1 := by rcases hδ₂s with rfl | rfl <;> norm_num
  have hδ₃2 : (δ₃ : ℂ) * δ₃ = 1 := by rcases hδ₃s with rfl | rfl <;> norm_num
  have hB1 : (basis.representation χB).character 1 = η * (δ₂ * f₂ - δ₃ * f₃) := by
    have h := congrFun hAexp 1
    rw [hA1, hdeg1 χ₂, hdeg1 χ₃, ← hf₂def, ← hf₃def] at h
    linear_combination (-(η : ℂ)) * h - (basis.representation χB).character 1 * hη2
  have hBt : (basis.representation χB).character t = η * (1 - e * q) := by
    have h := congrFun hAexp t
    rw [hAt, hχ₂t, hχ₃t] at h
    linear_combination (-(η : ℂ)) * h - (basis.representation χB).character t * hη2 -
      ((η : ℂ) * e * q) * hδ₂2 + (η : ℂ) * hδ₃2
  have hBpos : 0 < η * (δ₂ * (f₂ : ℤ) - δ₃ * f₃) := by
    have h : ((Module.finrank ℂ (basis.representation χB).vector : ℤ) : ℂ) =
        ((η * (δ₂ * (f₂ : ℤ) - δ₃ * f₃) : ℤ) : ℂ) := by
      push_cast
      rw [← hB1, hdeg1]
    have h' := Int.cast_injective (α := ℂ) h
    rw [← h']
    exact_mod_cast (basis_character_one basis χB).2
  exact ⟨χ₁, χ₂, χ₃, χB, δ₁, δ₂, δ₃, η, hnd3, hχ₁B₂, hχ₂B₂, hχ₃B₂, hodd₁, hodd₂, hodd₃, hf1gt,
    hf2gt, hf3gt, hsigns, hχB2, hχB3, hη, hrelZ, hprod, h5f₂, h5f₃, hnot1, hv₂,
    by rw [hv₃]; exact hv₂,
    hdef2, huniqB, coefficientBlock_self_mem _ _ _, hχ₃B, hχBB, hAexp, hsupp, hχ₂t, hχ₃t, hBt, hB1,
    hBpos, hX₁, hOF1⟩

end CFSG.Semidihedral.Principal
