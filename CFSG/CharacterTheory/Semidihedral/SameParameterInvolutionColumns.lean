module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.Principal.SpectrumRestrictionRigiditySupport
public import CFSG.CharacterTheory.Semidihedral.SameParameterSections
public import CFSG.CharacterTheory.Semidihedral.KleinFourOddKernel

public noncomputable section

namespace CFSG.Semidihedral.StationaryOddLocalization

open scoped Classical Pointwise IsKleinFour

section RegularInvolutionColumns

open CFSG.Semidihedral.Principal CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour CFSG.Open
open scoped BigOperators

universe w

theorem integral_odd_row_unique {X : Type*} [Group X] (φ : X → ℂ) (q : ℕ) (e : ℤ)
    (he : (e : ℂ) ≠ 0) (hφ1 : φ 1 = q)
    (hex : ∃ y : X, Odd (orderOf y) ∧ φ y ≠ q) {a b a' b' : ℤ}
    (h : ∀ y : X, Odd (orderOf y) →
      (a : ℂ) + b * (1 + e * φ y) = a' + b' * (1 + e * φ y)) :
    a = a' ∧ b = b' := by
  obtain ⟨h0, h1⟩ := eq_zero_of_forall_odd_add_mul φ q e he hφ1 hex
    (a := (a : ℂ) - a') (b := (b : ℂ) - b') fun y hy => by
      linear_combination h y hy
  exact ⟨Int.cast_injective (sub_eq_zero.mp h0),
    Int.cast_injective (sub_eq_zero.mp h1)⟩

@[expose] def regularInvolutionU {H : Type} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (e : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) : H → ℂ := fun x =>
  1 - e * (basis.representation χ₁).character x -
    (basis.representation χ₂).character x + e * (basis.representation χ₃).character x +
    2 * (basis.representation χ₄).character x

@[expose] def regularInvolutionV {H : Type} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (e : ℤ) (k : ℕ)
    (χ₁ χ₂ χ₄ : basis.index) (ψ ν : ℕ → basis.index) : H → ℂ := fun x =>
  e * (basis.representation χ₁).character x + (basis.representation χ₂).character x -
    (basis.representation χ₄).character x +
    e * ∑ j ∈ Finset.Icc 1 (k - 1), (basis.representation (ψ j)).character x -
    e * ∑ i ∈ Finset.range k, (basis.representation (ν i)).character x

theorem actual_local_degree_q_odd_restriction_eq {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (C t)) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (α β : basis.index)
    (hαB : α ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hβB : β ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hαdeg : Module.finrank ℂ (basis.representation α).vector = p ^ f)
    (hβdeg : Module.finrank ℂ (basis.representation β).vector = p ^ f)
    (hαker : MonoidHom.ker (basis.representation α).representation = NZ t)
    (hβker : MonoidHom.ker (basis.representation β).representation = NZ t) :
    ∀ y : C t, Odd (orderOf y) →
      (basis.representation α).character y = (basis.representation β).character y := by
  intro y hy
  rw [local_degree_q_principal_odd_restriction_rigidity n hn S fS hH t ht hnonab hcentral
    hnc p f hp hpodd hf hmodel ideal basis principal hprincipal α hαB hαdeg hαker y hy,
    local_degree_q_principal_odd_restriction_rigidity n hn S fS hH t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal basis principal hprincipal β hβB hβdeg hβker y hy]

theorem actual_regular_involution_columns_of_family {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    ∃ u : basis.index → Fin 2 → ℤ,
      (∀ c ∈ B, ∀ y : C t, Odd (orderOf y) →
        (basis.representation c).character (t * y) =
          u c 0 + u c 1 * (1 + (e : ℂ) * φ y)) ∧
      (∑ c ∈ B, u c 0 * u c 0 = 8) ∧ (∑ c ∈ B, u c 0 * u c 1 = -4) ∧
      (∑ c ∈ B, u c 1 * u c 1 = 2 ^ (n - 2) + 2) ∧
      u principal 0 = 1 ∧ u principal 1 = 0 ∧
      (u χ₁ 0 = -e ∧ u χ₁ 1 = e) ∧ (u χ₂ 0 = -1 ∧ u χ₂ 1 = 1) ∧
      (u χ₃ 0 = e ∧ u χ₃ 1 = 0) ∧ (u χ₄ 0 = 2 ∧ u χ₄ 1 = -1) ∧
      (∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), u (ψ j) 0 = 0 ∧ u (ψ j) 1 = e) ∧
      (∀ i ∈ Finset.range (2 ^ (n - 3)), u (ν i) 0 = 0 ∧ u (ν i) 1 = -e) ∧
      (∀ x : H,
        (∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) =
          regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄ x ∧
        (∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) =
          regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν x) ∧
      ∀ x : H, x ∉ SameParameterSections.twoSection t →
        regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄ x = 0 ∧
        regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν x = 0 := by
  intro B
  obtain ⟨F, hF, hFfinite, ρ, hcard, -, -, -, hnative⟩ :=
    actual_simple_layer_principal_involution_columns n hn S fS hH t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal
  let := hF
  let := hFfinite
  obtain ⟨⟨l', hl'B, -, hl'char, hl'deg, hl'ker⟩, u, hrows, h00, h01, h11,
    hpr0, hpr1, hvanish, -⟩ := hnative
  obtain ⟨hlφ, -, -, -, -, hnd, hψinj, hνinj, hψavoid, hνavoid, hdisjoint,
    hB, -, -, hty, -⟩ := hfam
  change B = ({principal, χ₁, χ₂, χ₃, χ₄} ∪
    (Finset.Icc 1 (2 ^ (n - 3) - 1)).image ψ ∪
    (Finset.range (2 ^ (n - 3))).image ν) at hB
  obtain ⟨l, hlB, -, hlchar, hldeg, hlker⟩ := hlφ
  have hφeq : ∀ y : C t, Odd (orderOf y) →
      (localBasis.representation l').character y = φ y := by
    intro y hy
    rw [← hlchar]
    exact actual_local_degree_q_odd_restriction_eq n hn S fS hH t ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal localBasis localPrincipal hlocalPrincipal l' l hl'B hlB
        (hl'deg.trans hcard) (hldeg.trans hq) hl'ker hlker y hy
  have he' : (if Nat.card F % 4 = 1 then 1 else -1 : ℤ) = e := by
    rw [hcard, ← hq, ← he]
  have hrows' : ∀ c ∈ B, ∀ y : C t, Odd (orderOf y) →
      (basis.representation c).character (t * y) =
        u c 0 + u c 1 * (1 + (e : ℂ) * φ y) := by
    intro c hc y hy
    have h := hrows c hc y hy
    rw [← hl'char, he', hφeq y hy] at h
    exact h
  have hδ₁ := hregular.1
  have hδ₂ := hregular.2.1
  have hδ₃ := hregular.2.2.1
  have hδ₄ := hregular.2.2.2.1
  have hene : (e : ℂ) ≠ 0 := by
    rw [he]
    split_ifs <;> norm_num
  obtain ⟨hφ1, hφnc⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal
    q φ ⟨l, hlB, (localBasis.irreducible l), hlchar, hldeg, hlker⟩
  have identify (c : basis.index) (hc : c ∈ B) (a b : ℤ)
      (hv : ∀ y : C t, Odd (orderOf y) →
        (basis.representation c).character (t * y) = a + b * (1 + (e : ℂ) * φ y)) :
      u c 0 = a ∧ u c 1 = b :=
    integral_odd_row_unique φ q e hene hφ1 hφnc fun y hy =>
      (hrows' c hc y hy).symm.trans (hv y hy)
  have hχ₁ := identify χ₁ (by rw [hB]; simp) (-e) e fun y hy => by
    rw [(hty y hy).1, hδ₁]
    push_cast
    ring
  have hχ₂ := identify χ₂ (by rw [hB]; simp) (-1) 1 fun y hy => by
    rw [(hty y hy).2.1, hδ₂]
    push_cast
    ring
  have hχ₃ := identify χ₃ (by rw [hB]; simp) e 0 fun y hy => by
    rw [(hty y hy).2.2.1, hδ₃]
    push_cast
    ring
  have hχ₄ := identify χ₄ (by rw [hB]; simp) 2 (-1) fun y hy => by
    rw [(hty y hy).2.2.2.1, hδ₄]
    norm_num
    ring
  have hψ : ∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1), u (ψ j) 0 = 0 ∧ u (ψ j) 1 = e := by
    intro j hj
    apply identify (ψ j) (by rw [hB]; simp [Finset.mem_image_of_mem ψ hj]) 0 e
    intro y hy
    rw [(hty y hy).2.2.2.2.1 j hj, hδ₁]
    simp
  have hν : ∀ i ∈ Finset.range (2 ^ (n - 3)), u (ν i) 0 = 0 ∧ u (ν i) 1 = -e := by
    intro i hi
    apply identify (ν i) (by rw [hB]; simp [Finset.mem_image_of_mem ν hi]) 0 (-e)
    intro y hy
    rw [(hty y hy).2.2.2.2.2 i hi, hδ₁]
    push_cast
    ring
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h0χ₁, h0χ₂, h0χ₃, h0χ₄⟩, ⟨hχ₁χ₂, hχ₁χ₃, hχ₁χ₄⟩,
    ⟨hχ₂χ₃, hχ₂χ₄⟩, hχ₃χ₄, -⟩ := hnd
  have hsum (x : H) (i : Fin 2) :
      (∑ c ∈ B, (u c i : ℂ) * (basis.representation c).character x) =
        (u principal i : ℂ) * (basis.representation principal).character x +
        (u χ₁ i : ℂ) * (basis.representation χ₁).character x +
        (u χ₂ i : ℂ) * (basis.representation χ₂).character x +
        (u χ₃ i : ℂ) * (basis.representation χ₃).character x +
        (u χ₄ i : ℂ) * (basis.representation χ₄).character x +
        ∑ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
          (u (ψ j) i : ℂ) * (basis.representation (ψ j)).character x +
        ∑ j ∈ Finset.range (2 ^ (n - 3)),
          (u (ν j) i : ℂ) * (basis.representation (ν j)).character x := by
    rw [hB]
    exact sum_listed (2 ^ (n - 3)) h0χ₁ h0χ₂ h0χ₃ h0χ₄ hχ₁χ₂ hχ₁χ₃ hχ₁χ₄
      hχ₂χ₃ hχ₂χ₄ hχ₃χ₄ hψinj hνinj hψavoid hνavoid hdisjoint _
  have hexpand (x : H) :
      (∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) =
        regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄ x ∧
      (∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) =
        regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν x := by
    have hψ0 : (∑ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
        (u (ψ j) 0 : ℂ) * (basis.representation (ψ j)).character x) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [(hψ j hj).1]; simp
    have hν0 : (∑ i ∈ Finset.range (2 ^ (n - 3)),
        (u (ν i) 0 : ℂ) * (basis.representation (ν i)).character x) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [(hν i hi).1]; simp
    have hψ1 : (∑ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
        (u (ψ j) 1 : ℂ) * (basis.representation (ψ j)).character x) =
        e * ∑ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
          (basis.representation (ψ j)).character x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j hj => by rw [(hψ j hj).2]
    have hν1 : (∑ i ∈ Finset.range (2 ^ (n - 3)),
        (u (ν i) 1 : ℂ) * (basis.representation (ν i)).character x) =
        (-e : ℤ) * ∑ i ∈ Finset.range (2 ^ (n - 3)),
          (basis.representation (ν i)).character x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by rw [(hν i hi).2]
    constructor
    · rw [hsum x 0, hpr0, hχ₁.1, hχ₂.1, hχ₃.1, hχ₄.1, hψ0, hν0, hprincipal]
      simp only [regularInvolutionU, Pi.one_apply]
      push_cast
      ring
    · rw [hsum x 1, hpr1, hχ₁.2, hχ₂.2, hχ₃.2, hχ₄.2, hψ1, hν1]
      simp only [regularInvolutionV]
      push_cast
      ring
  refine ⟨u, hrows', h00, h01, h11, hpr0, hpr1, hχ₁, hχ₂, hχ₃, hχ₄, hψ, hν,
    hexpand, fun x hx => ?_⟩
  have hord (i : Fin 2) :
      (∑ c ∈ B, (u c i : ℂ) * (basis.representation c).character x) = 0 := by
    have h := hvanish x (fun a c hac hcomm ⟨k, hk⟩ hodd hconj =>
      hx ⟨a, c, k, hac, hcomm, hk, hodd, hconj⟩) i
    have h' := congrArg (starRingEnd ℂ) h
    simpa only [map_sum, map_mul, map_intCast, starRingEnd_self_apply, map_zero] using h'
  exact ⟨(hexpand x).1.symm.trans (hord 0), (hexpand x).2.symm.trans (hord 1)⟩

theorem integral_involution_column_value {H : Type*} [Group H] [Fintype H]
    (t : H) (basis : FiniteIrreducibleCharacterBasis H) (B : Finset basis.index)
    (u : basis.index → Fin 2 → ℤ) (e : ℤ) (φ : C t → ℂ)
    (hrows : ∀ c ∈ B, ∀ y : C t, Odd (orderOf y) →
      (basis.representation c).character (t * y) =
        u c 0 + u c 1 * (1 + (e : ℂ) * φ y))
    (y : C t) (hy : Odd (orderOf y)) (i : Fin 2) :
    (∑ c ∈ B, (u c i : ℂ) * (basis.representation c).character (t * y)) =
      (∑ c ∈ B, u c i * u c 0 : ℤ) +
        (∑ c ∈ B, u c i * u c 1 : ℤ) * (1 + (e : ℂ) * φ y) := by
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hrows c hc y hy]
  ring

theorem actual_regular_involution_values_of_family {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    ∀ y : C t, Odd (orderOf y) →
      regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄ (t * y) = 4 * (1 - (e : ℂ) * φ y) ∧
      regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν (t * y) =
        (2 : ℂ) ^ (n - 2) - 2 + (e : ℂ) * ((2 : ℂ) ^ (n - 2) + 2) * φ y := by
  let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  obtain ⟨u, hrows, h00, h01, h11, -, -, -, -, -, -, -, -, hexpand, -⟩ :=
    actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
  have h10 : ∑ c ∈ B, u c 1 * u c 0 = -4 := by
    calc
      _ = ∑ c ∈ B, u c 0 * u c 1 := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = -4 := h01
  intro y hy
  have hU := integral_involution_column_value t basis B u e φ hrows y hy 0
  have hV := integral_involution_column_value t basis B u e φ hrows y hy 1
  rw [h00, h01, (hexpand (t * y)).1] at hU
  rw [h10, h11, (hexpand (t * y)).2] at hV
  constructor
  · rw [hU]
    push_cast
    ring
  · rw [hV]
    push_cast
    ring

theorem integral_character_column_virtual {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (B : Finset basis.index)
    (u : basis.index → ℤ) :
    (fun x => ∑ c ∈ B, (u c : ℂ) * (basis.representation c).character x) ∈
      virtualCharacters H := by
  have hsum : (fun x => ∑ c ∈ B, (u c : ℂ) * (basis.representation c).character x) =
      ∑ c ∈ B, u c • (basis.representation c).character := by
    funext x
    simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ (u c) (character_mem_virtualCharacters (basis.representation c))

theorem integral_character_column_pairing {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (B : Finset basis.index)
    (u v : basis.index → ℤ) :
    characterPairing (fun x => ∑ c ∈ B, (u c : ℂ) * (basis.representation c).character x)
      (fun x => ∑ c ∈ B, (v c : ℂ) * (basis.representation c).character x) =
        (∑ c ∈ B, u c * v c : ℤ) := by
  let ρ : B → FiniteComplexRepresentation H := fun c => basis.representation c
  have hirr : ∀ c : B, (ρ c).IsIrreducible := fun c => basis.irreducible c
  have hdistinct : Function.Injective (fun c : B => (ρ c).character) := by
    intro c d h
    exact Subtype.ext (basis.distinct h)
  have hsum (a : basis.index → ℤ) :
      (fun x => ∑ c ∈ B, (a c : ℂ) * (basis.representation c).character x) =
        (fun x => ∑ c : B, (a c : ℂ) * (ρ c).character x) := by
    funext x
    exact (Finset.sum_coe_sort B _).symm
  rw [hsum u, hsum v, characterPairing_expansion_right]
  simp_rw [characterPairing_distinct_expansion_coefficient ρ hirr hdistinct]
  push_cast
  simpa only [mul_comm] using
    (Finset.sum_coe_sort B (fun c => (u c : ℂ) * (v c : ℂ)))

theorem actual_regular_involution_gram_of_family {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let U := regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄
    let V := regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν
    U ∈ virtualCharacters H ∧ V ∈ virtualCharacters H ∧
      characterPairing U U = 8 ∧ characterPairing U V = -4 ∧
        characterPairing V V = (2 : ℂ) ^ (n - 2) + 2 := by
  intro U V
  let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  obtain ⟨u, -, h00, h01, h11, -, -, -, -, -, -, -, -, hexpand, -⟩ :=
    actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
  have hU : (fun x => ∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) = U :=
    funext fun x => (hexpand x).1
  have hV : (fun x => ∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) = V :=
    funext fun x => (hexpand x).2
  have hUvirtual := integral_character_column_virtual basis B (fun c => u c 0)
  have hVvirtual := integral_character_column_virtual basis B (fun c => u c 1)
  rw [hU] at hUvirtual
  rw [hV] at hVvirtual
  refine ⟨hUvirtual, hVvirtual, ?_, ?_, ?_⟩
  · rw [← hU, integral_character_column_pairing, h00]
    norm_num
  · rw [← hU, ← hV, integral_character_column_pairing, h01]
    norm_num
  · rw [← hV, integral_character_column_pairing, h11]
    push_cast
    rfl

theorem integral_character_column_coefficient {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (B : Finset basis.index)
    (u : basis.index → ℤ) {c : basis.index} (hc : c ∈ B) :
    characterPairing (fun x => ∑ d ∈ B, (u d : ℂ) * (basis.representation d).character x)
      (basis.representation c).character = (u c : ℂ) :=
  basis_combination_coefficient basis hc (fun d => (u d : ℂ))

theorem actual_regular_involution_mixed_pairings_of_family {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) :
    let U := regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄
    let V := regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν
    (characterPairing U 1 = 1 ∧ characterPairing V 1 = 0) ∧
      (characterPairing U (fun x => 1 + e * (basis.representation χ₁).character x -
        (basis.representation χ₂).character x - e * (basis.representation χ₃).character x) = 0 ∧
      characterPairing V (fun x => 1 + e * (basis.representation χ₁).character x -
        (basis.representation χ₂).character x - e * (basis.representation χ₃).character x) = 0) ∧
      (∀ j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1),
        characterPairing U (fun x => 1 + e * (basis.representation χ₁).character x -
          e * (basis.representation (ψ j)).character x) = 0 ∧
        characterPairing V (fun x => 1 + e * (basis.representation χ₁).character x -
          e * (basis.representation (ψ j)).character x) = 0) ∧
      ∀ i ∈ Finset.range (2 ^ (n - 3)), ∀ j ∈ Finset.range (2 ^ (n - 3)),
        characterPairing U (fun x => (basis.representation (ν i)).character x -
          (basis.representation (ν j)).character x) = 0 ∧
        characterPairing V (fun x => (basis.representation (ν i)).character x -
          (basis.representation (ν j)).character x) = 0 := by
  intro U V
  let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  obtain ⟨u, -, -, -, -, hpr0, hpr1, hχ₁, hχ₂, hχ₃, -, hψ, hν, hexpand, -⟩ :=
    actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hfam
  change B = ({principal, χ₁, χ₂, χ₃, χ₄} ∪
    (Finset.Icc 1 (2 ^ (n - 3) - 1)).image ψ ∪
    (Finset.range (2 ^ (n - 3))).image ν) at hB
  have hU : (fun x => ∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) = U :=
    funext fun x => (hexpand x).1
  have hV : (fun x => ∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) = V :=
    funext fun x => (hexpand x).2
  have hUcoeff (c : basis.index) (hc : c ∈ B) :
      characterPairing U (basis.representation c).character = (u c 0 : ℂ) := by
    rw [← hU]
    exact integral_character_column_coefficient basis B (fun d => u d 0) hc
  have hVcoeff (c : basis.index) (hc : c ∈ B) :
      characterPairing V (basis.representation c).character = (u c 1 : ℂ) := by
    rw [← hV]
    exact integral_character_column_coefficient basis B (fun d => u d 1) hc
  have hprB : principal ∈ B := by rw [hB]; simp
  have hχ₁B : χ₁ ∈ B := by rw [hB]; simp
  have hχ₂B : χ₂ ∈ B := by rw [hB]; simp
  have hχ₃B : χ₃ ∈ B := by rw [hB]; simp
  have hψB (j : ℕ) (hj : j ∈ Finset.Icc 1 (2 ^ (n - 3) - 1)) : ψ j ∈ B := by
    rw [hB]
    simp [Finset.mem_image_of_mem ψ hj]
  have hνB (i : ℕ) (hi : i ∈ Finset.range (2 ^ (n - 3))) : ν i ∈ B := by
    rw [hB]
    simp [Finset.mem_image_of_mem ν hi]
  have he2 : (e : ℂ) ^ 2 = 1 := by
    rw [he]
    split_ifs <;> norm_num
  have hpr : characterPairing U 1 = 1 ∧ characterPairing V 1 = 0 := by
    rw [← hprincipal, hUcoeff principal hprB, hVcoeff principal hprB, hpr0, hpr1]
    norm_num
  have hT (F : H → ℂ) :
      characterPairing F (fun x => 1 + e * (basis.representation χ₁).character x -
        (basis.representation χ₂).character x - e * (basis.representation χ₃).character x) =
      characterPairing F 1 + e * characterPairing F (basis.representation χ₁).character -
        characterPairing F (basis.representation χ₂).character -
          e * characterPairing F (basis.representation χ₃).character := by
    change characterPairing F (1 + (e : ℂ) • (basis.representation χ₁).character -
      (basis.representation χ₂).character - (e : ℂ) • (basis.representation χ₃).character) = _
    rw [SpectrumRigidity.pairing_sub_right, SpectrumRigidity.pairing_sub_right,
      SpectrumRigidity.pairing_add_right, SpectrumRigidity.pairing_smul_right,
      SpectrumRigidity.pairing_smul_right]
  have hE (F : H → ℂ) (j : ℕ) :
      characterPairing F (fun x => 1 + e * (basis.representation χ₁).character x -
        e * (basis.representation (ψ j)).character x) =
      characterPairing F 1 + e * characterPairing F (basis.representation χ₁).character -
        e * characterPairing F (basis.representation (ψ j)).character := by
    change characterPairing F (1 + (e : ℂ) • (basis.representation χ₁).character -
      (e : ℂ) • (basis.representation (ψ j)).character) = _
    rw [SpectrumRigidity.pairing_sub_right, SpectrumRigidity.pairing_add_right,
      SpectrumRigidity.pairing_smul_right, SpectrumRigidity.pairing_smul_right]
  refine ⟨hpr, ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩, fun i hi j hj => ⟨?_, ?_⟩⟩
  · rw [hT, hpr.1, hUcoeff χ₁ hχ₁B, hUcoeff χ₂ hχ₂B, hUcoeff χ₃ hχ₃B,
      hχ₁.1, hχ₂.1, hχ₃.1]
    push_cast
    linear_combination -2 * he2
  · rw [hT, hpr.2, hVcoeff χ₁ hχ₁B, hVcoeff χ₂ hχ₂B, hVcoeff χ₃ hχ₃B,
      hχ₁.2, hχ₂.2, hχ₃.2]
    linear_combination he2
  · rw [hE, hpr.1, hUcoeff χ₁ hχ₁B, hUcoeff (ψ j) (hψB j hj), hχ₁.1, (hψ j hj).1]
    push_cast
    linear_combination -he2
  · rw [hE, hpr.2, hVcoeff χ₁ hχ₁B, hVcoeff (ψ j) (hψB j hj), hχ₁.2, (hψ j hj).2]
    ring
  · rw [characterPairing_sub_right', hUcoeff (ν i) (hνB i hi),
      hUcoeff (ν j) (hνB j hj), (hν i hi).1, (hν j hj).1]
    simp
  · rw [characterPairing_sub_right', hVcoeff (ν i) (hνB i hi),
      hVcoeff (ν j) (hνB j hj), (hν i hi).2, (hν j hj).2]
    simp

theorem actual_involution_section_restriction_of_family {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) (z : basis.index → ℂ) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let F := fun x => ∑ c ∈ B, z c * (basis.representation c).character x
    let U := regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄
    let V := regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν
    let m := (2 : ℂ) ^ (n - 2)
    let a := ((m + 2) * characterPairing F U + 4 * characterPairing F V) / (8 * m)
    let b := (4 * characterPairing F U + 8 * characterPairing F V) / (8 * m)
    ∀ x ∈ SameParameterSections.twoSection t, F x = a * U x + b * V x := by
  intro B F U V m a b
  obtain ⟨u, hrows, -, -, -, -, -, -, -, -, -, -, -, hexpand, -⟩ :=
    actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
  have hU : (fun x => ∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) = U :=
    funext fun x => (hexpand x).1
  have hV : (fun x => ∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) = V :=
    funext fun x => (hexpand x).2
  have hFU : characterPairing F U = ∑ c ∈ B, z c * (u c 0 : ℂ) := by
    rw [← hU]
    exact characterPairing_basis_combination basis B z (fun c => (u c 0 : ℂ))
  have hFV : characterPairing F V = ∑ c ∈ B, z c * (u c 1 : ℂ) := by
    rw [← hV]
    exact characterPairing_basis_combination basis B z (fun c => (u c 1 : ℂ))
  have hFty (y : C t) (hy : Odd (orderOf y)) :
      F (t * y) = characterPairing F U + characterPairing F V * (1 + (e : ℂ) * φ y) := by
    rw [hFU, hFV, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hrows c hc y hy]
    ring
  have hm : m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hty (y : C t) (hy : Odd (orderOf y)) : F (t * y) = a * U (t * y) + b * V (t * y) := by
    obtain ⟨hUty, hVty⟩ := actual_regular_involution_values_of_family n hn S fS hH t s ht
      hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
        localPrincipal hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular y hy
    change U (t * y) = 4 * (1 - (e : ℂ) * φ y) at hUty
    change V (t * y) = m - 2 + (e : ℂ) * (m + 2) * φ y at hVty
    rw [hFty y hy, hUty, hVty]
    dsimp only [a, b]
    field_simp
    ring
  have hconj (w : basis.index → ℂ) (g x : H) :
      (∑ c ∈ B, w c * (basis.representation c).character (g * x * g⁻¹)) =
        ∑ c ∈ B, w c * (basis.representation c).character x := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [FiniteComplexRepresentation.character, Representation.char_conj]
  have hFconj (g x : H) : F (g * x * g⁻¹) = F x := hconj z g x
  have hUconj (g x : H) : U (g * x * g⁻¹) = U x := by
    rw [← hU]
    exact hconj (fun c => (u c 0 : ℂ)) g x
  have hVconj (g x : H) : V (g * x * g⁻¹) = V x := by
    rw [← hV]
    exact hconj (fun c => (u c 1 : ℂ)) g x
  intro x hx
  obtain ⟨g, y, hy, hxy⟩ := SameParameterSections.twoSection_normal_form hx
  have hFx : F x = F (t * y) := (hFconj g x).symm.trans (congrArg F hxy)
  have hUx : U x = U (t * y) := (hUconj g x).symm.trans (congrArg U hxy)
  have hVx : V x = V (t * y) := (hVconj g x).symm.trans (congrArg V hxy)
  rw [hFx, hUx, hVx]
  exact hty y hy

theorem actual_involution_section_vanishing_iff_pairings_zero {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν) (z : basis.index → ℂ) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let F := fun x => ∑ c ∈ B, z c * (basis.representation c).character x
    let U := regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄
    let V := regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν
    (∀ x ∈ SameParameterSections.twoSection t, F x = 0) ↔
      characterPairing F U = 0 ∧ characterPairing F V = 0 := by
  intro B F U V
  constructor
  · intro hzero
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsupport⟩ :=
      actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
        p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
          hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
    have hagree : ∀ x ∈ SameParameterSections.twoSection t,
        F x = (0 : ℂ) * (0 : H → ℂ) x := fun x hx => by simpa using hzero x hx
    constructor
    · have h := SameParameterSections.pairing_of_involution_section t ht F 0 U 0 hagree
        (fun x hx => (hsupport x hx).1)
      simpa only [zero_mul] using h
    · have h := SameParameterSections.pairing_of_involution_section t ht F 0 V 0 hagree
        (fun x hx => (hsupport x hx).2)
      simpa only [zero_mul] using h
  · rintro ⟨hU, hV⟩ x hx
    have h := actual_involution_section_restriction_of_family n hn S fS hH t s ht hnonab
      hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
        localPrincipal hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam
          hregular z x hx
    change F x =
      (((2 : ℂ) ^ (n - 2) + 2) * characterPairing F U + 4 * characterPairing F V) /
          (8 * (2 : ℂ) ^ (n - 2)) * U x +
      (4 * characterPairing F U + 8 * characterPairing F V) /
          (8 * (2 : ℂ) ^ (n - 2)) * V x at h
    simpa only [hU, hV, mul_zero, zero_add, zero_div, zero_mul] using h

theorem actual_regular_involution_pairings_of_character_row {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (θ : FiniteComplexRepresentation.{0, w} H) (a b : ℂ)
    (hrow : ∀ y : C t, Odd (orderOf y) →
      θ.character (t * y) = a + b * (1 + (e : ℂ) * φ y)) :
    characterPairing θ.character (regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄) = a ∧
      characterPairing θ.character
        (regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν) = b := by
  let U := regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄
  let V := regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν
  let g : H → ℂ := (a + b) • (1 : H → ℂ) + (b * e) • (basis.representation χ₁).character
  obtain ⟨u, -, -, -, -, hpr0, hpr1, hχ₁, -, -, -, -, -, hexpand, hsupport⟩ :=
    actual_regular_involution_columns_of_family n hn S fS hH t s ht hnonab hcentral hnc
      p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
        hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hregular
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hB, -, -, hty, -⟩ := hfam
  let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  change B = _ at hB
  have hprB : principal ∈ B := by rw [hB]; simp
  have hχ₁B : χ₁ ∈ B := by rw [hB]; simp
  have hU : (fun x => ∑ c ∈ B, (u c 0 : ℂ) * (basis.representation c).character x) = U :=
    funext fun x => (hexpand x).1
  have hV : (fun x => ∑ c ∈ B, (u c 1 : ℂ) * (basis.representation c).character x) = V :=
    funext fun x => (hexpand x).2
  have he2 : (e : ℂ) ^ 2 = 1 := by
    rw [he]
    split_ifs <;> norm_num
  have hχ₁ty (y : C t) (hy : Odd (orderOf y)) :
      (basis.representation χ₁).character (t * y) = φ y := by
    rw [(hty y hy).1, hregular.1, ← pow_two, he2, one_mul]
  have hagree : ∀ x ∈ SameParameterSections.twoSection t, θ.character x = g x := by
    intro x hx
    obtain ⟨c, y, hy, hxy⟩ := SameParameterSections.twoSection_normal_form hx
    have hθ : θ.character x = θ.character (t * y) :=
      (Representation.char_conj θ.representation x c).symm.trans (congrArg θ.character hxy)
    have hχ : (basis.representation χ₁).character x =
        (basis.representation χ₁).character (t * y) :=
      (Representation.char_conj (basis.representation χ₁).representation x c).symm.trans
        (congrArg (basis.representation χ₁).character hxy)
    change θ.character x = (a + b) * 1 + (b * e) * (basis.representation χ₁).character x
    rw [hθ, hχ, hrow y hy, hχ₁ty y hy]
    ring
  have hpairU := SameParameterSections.pairing_of_involution_section t ht θ.character g U 1
    (fun x hx => by simpa only [one_mul] using hagree x hx)
      (fun x hx => (hsupport x hx).1)
  have hpairV := SameParameterSections.pairing_of_involution_section t ht θ.character g V 1
    (fun x hx => by simpa only [one_mul] using hagree x hx)
      (fun x hx => (hsupport x hx).2)
  simp only [one_mul] at hpairU hpairV
  constructor
  · change characterPairing θ.character U = a
    rw [hpairU, characterPairing_comm]
    dsimp only [g]
    rw [SpectrumRigidity.pairing_add_right,
      SpectrumRigidity.pairing_smul_right, SpectrumRigidity.pairing_smul_right]
    rw [← hprincipal, ← hU, integral_character_column_coefficient basis B _ hprB,
      integral_character_column_coefficient basis B _ hχ₁B, hpr0, hχ₁.1]
    push_cast
    linear_combination -b * he2
  · change characterPairing θ.character V = b
    rw [hpairV, characterPairing_comm]
    dsimp only [g]
    rw [SpectrumRigidity.pairing_add_right,
      SpectrumRigidity.pairing_smul_right, SpectrumRigidity.pairing_smul_right]
    rw [← hprincipal, ← hV, integral_character_column_coefficient basis B _ hprB,
      integral_character_column_coefficient basis B _ hχ₁B, hpr1, hχ₁.2]
    push_cast
    linear_combination b * he2

theorem actual_regular_involution_pairings_of_signed_local_row {H : Type} [Group H] [Fintype H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (hH : ∀ U : Subgroup H, U.index ≠ 2) (t s : H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (δ₁ δ₂ δ₃ δ₄ : ℤ)
    (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hregular : ActualPrincipalCharacteristicValues basis t s p q (2 ^ (n - 3)) e
      δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (θ : FiniteComplexRepresentation.{0, w} H) (δ : ℤ)
    (hrow : ∀ y : C t, Odd (orderOf y) →
      θ.character (t * y) = (δ : ℂ) * e * φ y) :
    characterPairing θ.character (regularInvolutionU basis e χ₁ χ₂ χ₃ χ₄) = -(δ : ℂ) ∧
      characterPairing θ.character
        (regularInvolutionV basis e (2 ^ (n - 3)) χ₁ χ₂ χ₄ ψ ν) = (δ : ℂ) := by
  apply actual_regular_involution_pairings_of_character_row n hn S fS hH t s ht hnonab
    hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal q hq e he φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam
        hregular θ (-(δ : ℂ)) (δ : ℂ)
  intro y hy
  rw [hrow y hy]
  ring

theorem actual_involution_column_witness_unique {H : Type} [Group H] [Fintype H]
    (t : H) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (φ : C t → ℂ) (e : ℤ) (he : (e : ℂ) ≠ 0)
    (hφ : ∃ l ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      (localBasis.representation l).IsIrreducible ∧
      (localBasis.representation l).character = φ ∧
      Module.finrank ℂ (localBasis.representation l).vector = q ∧
      MonoidHom.ker (localBasis.representation l).representation = NZ t)
    (u v : basis.index → Fin 2 → ℤ)
    (hu : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ y : C t, Odd (orderOf y) → (basis.representation c).character (t * y) =
        u c 0 + u c 1 * (1 + (e : ℂ) * φ y))
    (hv : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ y : C t, Odd (orderOf y) → (basis.representation c).character (t * y) =
        v c 0 + v c 1 * (1 + (e : ℂ) * φ y)) :
    ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      u c = v c := by
  obtain ⟨hφ1, hφnc⟩ := family_character_nonconstant hnonab localBasis ideal localPrincipal q φ hφ
  intro c hc
  obtain ⟨h0, h1⟩ := integral_odd_row_unique φ q e he hφ1 hφnc fun y hy =>
    (hu c hc y hy).symm.trans (hv c hc y hy)
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem integral_column_conjugate_zero_iff {ι : Type*} (B : Finset ι)
    (u : ι → ℤ) (χ : ι → ℂ) :
    (∑ c ∈ B, (u c : ℂ) * starRingEnd ℂ (χ c)) = 0 ↔
      (∑ c ∈ B, (u c : ℂ) * χ c) = 0 := by
  constructor
  · intro h
    have h' := congrArg (starRingEnd ℂ) h
    simpa only [map_sum, map_mul, map_intCast, starRingEnd_self_apply, map_zero] using h'
  · intro h
    have h' := congrArg (starRingEnd ℂ) h
    simpa only [map_sum, map_mul, map_intCast, map_zero] using h'

end RegularInvolutionColumns

section OriginalCoverSylow

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u v

theorem odd_index_of_odd_kernel_and_image {X : Type u} {Y : Type v}
    [Group X] [Group Y] [Finite Y]
    (q : X →* Y) (hq : Function.Surjective q)
    (hker : Odd (Nat.card q.ker)) (B : Subgroup X)
    (himage : Odd (B.map q).index) : Odd B.index := by
  have hwhole := Subgroup.card_ker_mul_card_of_surjective hq
  have hpart := Subgroup.card_ker_mul_card_of_surjective (q.subgroupMap_surjective B)
  have hprod : Nat.card (q.subgroupMap B).ker * B.index =
      Nat.card q.ker * (B.map q).index := by
    apply Nat.mul_right_cancel (m := Nat.card (B.map q))
    · exact Nat.card_pos
    · calc
        (Nat.card (q.subgroupMap B).ker * B.index) * Nat.card (B.map q) =
            (Nat.card (q.subgroupMap B).ker * Nat.card (B.map q)) * B.index := by ac_rfl
        _ = Nat.card B * B.index := by rw [hpart]
        _ = Nat.card X := B.card_mul_index
        _ = Nat.card q.ker * Nat.card Y := hwhole.symm
        _ = Nat.card q.ker * ((B.map q).index * Nat.card (B.map q)) := by
          rw [(B.map q).index_mul_card]
        _ = (Nat.card q.ker * (B.map q).index) * Nat.card (B.map q) := by ac_rfl
  exact (hker.mul himage).of_dvd_nat (dvd_of_mul_left_eq _ hprod)

theorem odd_index_of_layer_cover_and_outer_element {X : Type u} [Group X]
    (Q T B : Subgroup X) (hT : T.index = 2) (hQT : Q ≤ T)
    (hQodd : Odd (Q.relIndex T)) (hQB : Q ≤ B)
    (s : X) (hsB : s ∈ B) (hsT : s ∉ T) : Odd B.index := by
  let : T.Normal := Subgroup.normal_of_index_eq_two hT
  have hTB : T.relIndex B = 2 := by
    have hdvd : T.relIndex B ∣ 2 :=
      hT ▸ Subgroup.relIndex_dvd_index_of_normal T B
    have hne : T.relIndex B ≠ 1 := by
      intro h
      exact hsT (Subgroup.relIndex_eq_one.mp h hsB)
    exact ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  have hparts := Subgroup.relIndex_inf_mul_relIndex Q T B
  rw [hTB, inf_eq_left.mpr hQT] at hparts
  have hindex := Subgroup.relIndex_mul_index hQB
  have hwhole := Subgroup.relIndex_mul_index hQT
  rw [hT] at hwhole
  have hprod : Q.relIndex (T ⊓ B) * B.index = Q.relIndex T := by
    apply Nat.mul_right_cancel (m := 2) (by decide : 0 < (2 : ℕ))
    calc
      (Q.relIndex (T ⊓ B) * B.index) * 2 =
          (Q.relIndex (T ⊓ B) * 2) * B.index := by ac_rfl
      _ = Q.relIndex B * B.index := by rw [hparts]
      _ = Q.index := hindex
      _ = Q.relIndex T * 2 := hwhole.symm
  exact hQodd.of_dvd_nat (dvd_of_mul_left_eq _ hprod)

theorem actual_covering_subgroup_centralizer_odd_index {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    Odd (H.subgroupOf (C t)).index := by
  let B := H.subgroupOf (C t)
  let Q := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  let T' := (J t).comap (barKappa t)
  obtain ⟨-, hJ, -, -, hunique, -, -⟩ := actual_quotient_inputs n hn S fS hG t ht
  have hT : T'.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ (barKappa_surjective t)]
    exact hJ
  have hQT : Q ≤ T' := Subgroup.comap_mono (simple_le_index_two _ _ hJ hnonab)
  obtain ⟨F, hF, hfin, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hfin
  obtain ⟨-, -, -, hcard⟩ := data.compatible_layer
  have hQodd : Odd (Q.relIndex T') := by
    change Odd ((Q.subgroupOf T').index)
    rw [Subgroup.index_eq_card, hcard]
    exact data.field_group_odd
  have hQB : Q ≤ B.map (nu t) := by
    change (B ⊓ Q.comap (nu t)).map (nu t) = Q at hcover
    rw [← hcover]
    exact Subgroup.map_mono inf_le_left
  let V := KleinFourOddKernel.fourSubgroup (tInC t) (⟨s, hsC⟩ : C t)
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe _).symm.trans ht
  have hsCorder : orderOf (⟨s, hsC⟩ : C t) = 2 := (Subgroup.orderOf_coe _).symm.trans hs
  have hneC : tInC t ≠ (⟨s, hsC⟩ : C t) := fun h => hts (congrArg Subtype.val h)
  have hi := KleinFourOddKernel.quotient_onFour_injective (N t) hNodd (tInC t)
    (⟨s, hsC⟩ : C t) (tInC_central t) htC hsCorder hneC
  let eV := MulEquiv.ofBijective ((nu t).subgroupMap V)
    ⟨hi, (nu t).subgroupMap_surjective V⟩
  have htV : tInC t ∈ V :=
    (show Subgroup.zpowers (tInC t) ≤ V from le_sup_left) (Subgroup.mem_zpowers _)
  have hsV : (⟨s, hsC⟩ : C t) ∈ V :=
    (show Subgroup.zpowers (⟨s, hsC⟩ : C t) ≤ V from le_sup_right) (Subgroup.mem_zpowers _)
  have hsbar : orderOf (nu t (⟨s, hsC⟩ : C t)) = 2 :=
    (Subgroup.orderOf_coe _).trans
      ((eV.orderOf_eq ⟨(⟨s, hsC⟩ : C t), hsV⟩).trans
        ((Subgroup.orderOf_coe _).symm.trans hsCorder))
  have hne : nu t (tInC t) ≠ nu t (⟨s, hsC⟩ : C t) := by
    intro h
    exact hneC (congrArg Subtype.val (hi (Subtype.ext h :
      (nu t).subgroupMap V ⟨tInC t, htV⟩ =
        (nu t).subgroupMap V ⟨(⟨s, hsC⟩ : C t), hsV⟩)))
  have hsB : (⟨s, hsC⟩ : C t) ∈ B :=
    hVH (Subgroup.mem_closure_of_mem (Set.mem_insert_of_mem t (Set.mem_singleton s)))
  have hsimage : nu t (⟨s, hsC⟩ : C t) ∈ B.map (nu t) :=
    Subgroup.mem_map_of_mem (nu t) hsB
  have hsnot : nu t (⟨s, hsC⟩ : C t) ∉ T' := by
    intro hmem
    have horder : orderOf (⟨nu t (⟨s, hsC⟩ : C t), hmem⟩ : T') = 2 :=
      (Subgroup.orderOf_coe _).symm.trans hsbar
    exact hne (hunique _ horder).symm
  have himage : Odd (B.map (nu t)).index :=
    odd_index_of_layer_cover_and_outer_element Q T' (B.map (nu t)) hT hQT hQodd hQB
      (nu t (⟨s, hsC⟩ : C t)) hsimage hsnot
  apply odd_index_of_odd_kernel_and_image (nu t) (QuotientGroup.mk'_surjective (N t)) _ B
    himage
  rw [QuotientGroup.ker_mk']
  exact hNodd

theorem original_involution_centralizer_odd_index {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    Odd (C t).index := by
  obtain ⟨St, ft, hcenter⟩ := CFSG.Semidihedral.InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S fS hG t ht
  have hSt : (St : Subgroup G) ≤ C t := by
    have hc := CFSG.Semidihedral.CentralizerResidual.sylow_le_involutionCentralizer n hn St ft
    change (St : Subgroup G) ≤ Subgroup.centralizer
      ({(ft (CFSG.Semidihedral.z n) : G)} : Set G) at hc
    simpa only [hcenter] using hc
  have hodd : Odd (St : Subgroup G).index :=
    Nat.not_even_iff_odd.mp fun h => St.not_dvd_index (even_iff_two_dvd.mp h)
  exact hodd.of_dvd_nat (Subgroup.index_dvd_of_le hSt)

theorem actual_covering_subgroup_odd_index {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    Odd H.index := by
  have hB := actual_covering_subgroup_centralizer_odd_index n hn S fS hG t s ht hs hsC hts
    hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hC := original_involution_centralizer_odd_index n hn S fS hG t ht
  have hBC : (H.subgroupOf (C t)).map (C t).subtype = H ⊓ C t := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hindex : (H ⊓ C t).index = (H.subgroupOf (C t)).index * (C t).index := by
    rw [← hBC, Subgroup.index_map_subtype]
  have hodd : Odd (H ⊓ C t).index := hindex ▸ hB.mul hC
  exact hodd.of_dvd_nat (Subgroup.index_dvd_of_le inf_le_left)

theorem actual_covering_subgroup_sylow_presentation {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          ∀ x, (fG x : G) = ((fH x : H) : G) := by
  have hodd := actual_covering_subgroup_odd_index n hn S fS hG t s ht hs hsC hts
    hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  let SH : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨SG, hSG⟩ := SameParameterSections.subgroup_sylow_of_odd_index H hodd SH
  let fG := fS.trans (Sylow.equiv S SG)
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hSG.symm)
  let fH := fG.trans eSH.symm
  refine ⟨hodd, SH, fH, SG, fG, hSG, ?_⟩
  intro x
  have h := congrArg (fun z : SG => (z : G)) (eSH.apply_symm_apply (fG x))
  exact h.symm

open CFSG.Semidihedral

theorem central_involution_eq_supplied_semidihedral_center {X : Type u} [Group X]
    (n : ℕ) (hn : 4 ≤ n) (P : Sylow 2 X)
    (f : CFSG.Open.SemidihedralGroup n ≃* P) (t : X)
    (hcentral : t ∈ Subgroup.center X) (ht : orderOf t = 2) :
    (f (CFSG.Semidihedral.z n) : X) = t := by
  let : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcentral)
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have htP : t ∈ (P : Subgroup X) :=
    hpt.le_sylow_of_normal P (Subgroup.mem_zpowers t)
  let tP : P := ⟨t, htP⟩
  have htcenter : tP ∈ Subgroup.center P := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcentral (x : X)
  have hprecenter : f.symm tP ∈ Subgroup.center (CFSG.Open.SemidihedralGroup n) := by
    rw [← Subgroup.map_center_eq f.symm]
    exact Subgroup.mem_map_of_mem f.symm.toMonoidHom htcenter
  have hpreorder : orderOf (f.symm tP) = 2 :=
    (f.symm.orderOf_eq tP).trans ((Subgroup.orderOf_coe tP).symm.trans ht)
  let : Finite (CFSG.Open.SemidihedralGroup n) :=
    Finite.of_equiv (Multiplicative (ZMod (2 ^ (n - 1))) × Multiplicative (ZMod 2))
      (CFSG.Semidihedral.coordinateEquiv n (by omega)).symm
  rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hprecenter
  rcases (KleinFourOddKernel.mem_zpowers_involution (CFSG.Semidihedral.z n)
    (f.symm tP)
    (CFSG.Semidihedral.orderOf_z n (by omega))).mp hprecenter with hone | hz
  · simp only [hone, orderOf_one] at hpreorder
    omega
  · have h := congrArg (fun x : P => (x : X)) (f.apply_symm_apply tP)
    rw [hz] at h
    exact h

theorem original_centered_sylow_of_odd_index_centralizing_subgroup
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (H K : Subgroup G) (hKH : K ≤ H) (hKodd : Odd K.index)
    (t s : G) (htK : t ∈ K) (hsK : s ∈ K)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hts : t ≠ s)
    (hcentral : (⟨t, htK⟩ : K) ∈ Subgroup.center K) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤ K.subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fH (CFSG.Semidihedral.z n) : H) = (⟨t, hKH htK⟩ : H) ∧
        (fH (CFSG.Semidihedral.r n) : H) ^ (CFSG.Semidihedral.modulus n / 2) =
          (⟨t, hKH htK⟩ : H) ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) := by
  let tK : K := ⟨t, htK⟩
  let sK : K := ⟨s, hsK⟩
  have htKorder : orderOf tK = 2 := (Subgroup.orderOf_coe tK).symm.trans ht
  have hsKorder : orderOf sK = 2 := (Subgroup.orderOf_coe sK).symm.trans hs
  have hne : tK ≠ sK := fun h => hts (congrArg Subtype.val h)
  let VK := KleinFourOddKernel.fourSubgroup tK sK
  have hVK : IsPGroup 2 VK := IsPGroup.of_card (n := 2) (by
    rw [show Nat.card VK = 4 from
      KleinFourOddKernel.fourSubgroup_card tK sK hcentral htKorder hsKorder hne]
    norm_num)
  obtain ⟨SK, hVSK⟩ := hVK.exists_le_sylow
  obtain ⟨SG, hSG⟩ := SameParameterSections.subgroup_sylow_of_odd_index K hKodd SK
  have hSGK : (SG : Subgroup G) ≤ K := by
    rw [hSG]
    exact Subgroup.map_subtype_le _
  have hSGH : (SG : Subgroup G) ≤ H := hSGK.trans hKH
  let SH : Sylow 2 H := SG.subtype hSGH
  have hSH : (SH : Subgroup H).map H.subtype = (SG : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSGH]
  let fG := fS.trans (Sylow.equiv S SG)
  let eSK := ((SK : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hSG.symm)
  let fK := fG.trans eSK.symm
  have hrepK (x : CFSG.Open.SemidihedralGroup n) :
      (fG x : G) = ((fK x : K) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSK.apply_symm_apply (fG x))
    exact h.symm
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hSH)
  let fH := fG.trans eSH.symm
  have hrepH (x : CFSG.Open.SemidihedralGroup n) :
      (fG x : G) = ((fH x : H) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSH.apply_symm_apply (fG x))
    exact h.symm
  have hcenterK := central_involution_eq_supplied_semidihedral_center n hn SK fK tK
    hcentral htKorder
  have hcenterG : (fG (CFSG.Semidihedral.z n) : G) = t :=
    (hrepK _).trans (congrArg (fun x : K => (x : G)) hcenterK)
  have hcenterH : (fH (CFSG.Semidihedral.z n) : H) = (⟨t, hKH htK⟩ : H) :=
    Subtype.ext ((hrepH _).symm.trans hcenterG)
  have hrotation : (fH (CFSG.Semidihedral.r n) : H) ^
      (CFSG.Semidihedral.modulus n / 2) = (⟨t, hKH htK⟩ : H) := by
    simpa only [CFSG.Semidihedral.z, CFSG.Semidihedral.half, map_pow,
      Subgroup.coe_pow, CFSG.Semidihedral.modulus_div_two n (by omega)] using hcenterH
  have htSK : tK ∈ (SK : Subgroup K) := hVSK
    (show tK ∈ VK from Subgroup.mem_sup_left (Subgroup.mem_zpowers tK))
  have hsSK : sK ∈ (SK : Subgroup K) := hVSK
    (show sK ∈ VK from Subgroup.mem_sup_right (Subgroup.mem_zpowers sK))
  have hVSG : Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxs
    · rw [hSG]
      exact Subgroup.mem_map_of_mem K.subtype htSK
    · have hx : x = s := Set.mem_singleton_iff.mp hxs
      rw [hx, hSG]
      exact Subgroup.mem_map_of_mem K.subtype hsSK
  refine ⟨hKodd.of_dvd_nat (Subgroup.index_dvd_of_le hKH), SH, fH, SG, fG, ?_,
    hVSG, hSH.symm, hcenterG, hcenterH, hrotation, hrepH⟩
  rw [Sylow.coe_subtype]
  exact Subgroup.subgroupOf_mono H hSGK

theorem actual_covering_subgroup_centered_sylow_presentation
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fH (CFSG.Semidihedral.z n) : H) =
          (⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩ : H) ∧
        (fH (CFSG.Semidihedral.r n) : H) ^ (CFSG.Semidihedral.modulus n / 2) =
          (⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩ : H) ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) := by
  let K := H ⊓ C t
  have hKH : K ≤ H := inf_le_left
  have htH : t ∈ H := hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))
  have hsH : s ∈ H := hVH
    (Subgroup.mem_closure_of_mem (Set.mem_insert_of_mem t (Set.mem_singleton s)))
  have htK : t ∈ K := ⟨htH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hsK : s ∈ K := ⟨hsH, hsC⟩
  have htcentral : (⟨t, htK⟩ : K) ∈ Subgroup.center K := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property.2
  have hB := actual_covering_subgroup_centralizer_odd_index n hn S fS hG t s ht hs hsC hts
    hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hC := original_involution_centralizer_odd_index n hn S fS hG t ht
  have hmap : (H.subgroupOf (C t)).map (C t).subtype = K := by
    change (H.subgroupOf (C t)).map (C t).subtype = H ⊓ C t
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hKindex : K.index = (H.subgroupOf (C t)).index * (C t).index := by
    rw [← hmap, Subgroup.index_map_subtype]
  have hodd : Odd K.index := hKindex ▸ hB.mul hC
  exact original_centered_sylow_of_odd_index_centralizing_subgroup n hn S fS H K hKH hodd
    t s htK hsK ht hs hts htcentral

theorem actual_covering_centralizer_every_sylow_presentation
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let B := H.subgroupOf (C t)
    Odd B.index ∧ Odd H.index ∧
      ∀ SB : Sylow 2 B,
        ∃ (fB : CFSG.Open.SemidihedralGroup n ≃* SB)
          (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
          (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          (fG (CFSG.Semidihedral.z n) : G) = t ∧
          (((fB (CFSG.Semidihedral.z n) : B) : C t) : G) = t ∧
          ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
          ∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
            (fG x : G) = ((fH x : H) : G) := by
  intro B
  have hB := actual_covering_subgroup_centralizer_odd_index n hn S fS hG t s ht hs hsC hts
    hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hH := actual_covering_subgroup_odd_index n hn S fS hG t s ht hs hsC hts
    hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hC := original_involution_centralizer_odd_index n hn S fS hG t ht
  refine ⟨hB, hH, ?_⟩
  intro SB
  obtain ⟨SC, hSC⟩ := SameParameterSections.subgroup_sylow_of_odd_index B hB SB
  obtain ⟨SG, hSG⟩ := SameParameterSections.subgroup_sylow_of_odd_index (C t) hC SC
  have hSGBC : (SG : Subgroup G) =
      ((SB : Subgroup B).map B.subtype).map (C t).subtype := by rw [hSG, hSC]
  have hSGHC : (SG : Subgroup G) ≤ H ⊓ C t := by
    have hSCB : (SC : Subgroup (C t)) ≤ B := by
      rw [hSC]
      exact Subgroup.map_subtype_le _
    calc
      (SG : Subgroup G) = (SC : Subgroup (C t)).map (C t).subtype := hSG
      _ ≤ B.map (C t).subtype := Subgroup.map_mono hSCB
      _ = H ⊓ C t := by
        change (H.subgroupOf (C t)).map (C t).subtype = H ⊓ C t
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hSGH : (SG : Subgroup G) ≤ H := hSGHC.trans inf_le_left
  let SH : Sylow 2 H := SG.subtype hSGH
  have hSH : (SH : Subgroup H).map H.subtype = (SG : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSGH]
  let fG := fS.trans (Sylow.equiv S SG)
  let eSC := ((SC : Subgroup (C t)).equivMapOfInjective (C t).subtype
    (C t).subtype_injective).trans (MulEquiv.subgroupCongr hSG.symm)
  let eSB := (((SB : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective).trans
    (MulEquiv.subgroupCongr hSC.symm)).trans eSC
  let fB := fG.trans eSB.symm
  have hrepB (x : CFSG.Open.SemidihedralGroup n) :
      (fG x : G) = (((fB x : B) : C t) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSB.apply_symm_apply (fG x))
    exact h.symm
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hSH)
  let fH := fG.trans eSH.symm
  have hrepH (x : CFSG.Open.SemidihedralGroup n) :
      (fG x : G) = ((fH x : H) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSH.apply_symm_apply (fG x))
    exact h.symm
  have htB : tInC t ∈ B := hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))
  let tB : B := ⟨tInC t, htB⟩
  have htBcentral : tB ∈ Subgroup.center B := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (tInC_central t) (x : C t)
  have htBorder : orderOf tB = 2 :=
    (Subgroup.orderOf_coe tB).symm.trans ((Subgroup.orderOf_coe (tInC t)).symm.trans ht)
  have hcenterB := central_involution_eq_supplied_semidihedral_center n hn SB fB tB
    htBcentral htBorder
  have hcenterG : (fG (CFSG.Semidihedral.z n) : G) = t :=
    (hrepB _).trans (congrArg (fun x : B => ((x : C t) : G)) hcenterB)
  refine ⟨fB, SH, fH, SG, fG, hSGBC, hSH.symm, ?_, hcenterG,
    (hrepB _).symm.trans hcenterG, (hrepH _).symm.trans hcenterG, ?_⟩
  · rw [Sylow.coe_subtype]
    exact Subgroup.subgroupOf_mono H hSGHC
  · exact fun x => ⟨hrepB x, hrepH x⟩

theorem noncentral_involution_isConj_standard_reflection (n : ℕ) (hn : 4 ≤ n)
    (x : CFSG.Open.SemidihedralGroup n) (hx : orderOf x = 2)
    (hxn : x ≠ CFSG.Semidihedral.z n) :
    IsConj (CFSG.Semidihedral.s n) x := by
  rcases (CFSG.Semidihedral.involution_iff n (by omega) x).mp hx with rfl | ⟨j, rfl⟩
  · exact (hxn rfl).elim
  · have h := CFSG.Semidihedral.even_outside_conjugate n hn (j.val : ℤ)
    change IsConj (CFSG.Semidihedral.s n)
      (CFSG.Semidihedral.r n ^ ((2 : ℕ) * j.val : ℤ) * CFSG.Semidihedral.s n) at h
    rw [← Int.natCast_mul, zpow_natCast] at h
    exact h

theorem original_sylow_involution_pair_presentation {X : Type u} [Group X]
    (n : ℕ) (hn : 4 ≤ n) (P : Sylow 2 X)
    (f : CFSG.Open.SemidihedralGroup n ≃* P) (t s : X)
    (hs : orderOf s = 2) (hts : t ≠ s) (hsP : s ∈ (P : Subgroup X))
    (hcenter : (f (CFSG.Semidihedral.z n) : X) = t) :
    ∃ (f' : CFSG.Open.SemidihedralGroup n ≃* P) (c : P),
      (f' (CFSG.Semidihedral.z n) : X) = t ∧
      (f' (CFSG.Semidihedral.s n) : X) = s ∧
      ∀ x, f' x = c * f x * c⁻¹ := by
  let sP : P := ⟨s, hsP⟩
  have hsorder : orderOf (f.symm sP) = 2 :=
    (f.symm.orderOf_eq sP).trans ((Subgroup.orderOf_coe sP).symm.trans hs)
  have hsne : f.symm sP ≠ CFSG.Semidihedral.z n := by
    intro heq
    have he := congrArg (fun a : P => (a : X)) (f.apply_symm_apply sP)
    rw [heq, hcenter] at he
    exact hts he
  obtain ⟨c, hc⟩ := isConj_iff.mp (f.toMonoidHom.map_isConj
    (noncentral_involution_isConj_standard_reflection n hn (f.symm sP) hsorder hsne))
  change c * f (CFSG.Semidihedral.s n) * c⁻¹ = f (f.symm sP) at hc
  rw [f.apply_symm_apply] at hc
  let f' := f.trans (MulAut.conj c)
  have hzcentral : f (CFSG.Semidihedral.z n) ∈ Subgroup.center P := by
    rw [← Subgroup.map_center_eq f]
    exact Subgroup.mem_map_of_mem f.toMonoidHom (CFSG.Semidihedral.z_mem_center n hn)
  have hzfix : c * f (CFSG.Semidihedral.z n) * c⁻¹ = f (CFSG.Semidihedral.z n) := by
    rw [Subgroup.mem_center_iff.mp hzcentral c, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨f', c, ?_, ?_, ?_⟩
  · exact (congrArg (fun a : P => (a : X)) hzfix).trans hcenter
  · exact congrArg (fun a : P => (a : X)) hc
  · exact fun _ => rfl

theorem original_pair_sylow_of_odd_index_centralizing_subgroup
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (H K : Subgroup G) (hKH : K ≤ H) (hKodd : Odd K.index)
    (t s : G) (htK : t ∈ K) (hsK : s ∈ K)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hts : t ≠ s)
    (hcentral : (⟨t, htK⟩ : K) ∈ Subgroup.center K) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤ K.subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fG (CFSG.Semidihedral.s n) : G) = s ∧
        (fH (CFSG.Semidihedral.z n) : H) = (⟨t, hKH htK⟩ : H) ∧
        (fH (CFSG.Semidihedral.s n) : H) = (⟨s, hKH hsK⟩ : H) ∧
        (fH (CFSG.Semidihedral.r n) : H) ^ (CFSG.Semidihedral.modulus n / 2) =
          (⟨t, hKH htK⟩ : H) ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) := by
  obtain ⟨hodd, SH, _, SG, fG, hSHK, hVSG, hmap, hcenter, _, _, _⟩ :=
    original_centered_sylow_of_odd_index_centralizing_subgroup n hn S fS H K hKH hKodd
      t s htK hsK ht hs hts hcentral
  have hsSG : s ∈ (SG : Subgroup G) := hVSG
    (Subgroup.mem_closure_of_mem (Set.mem_insert_of_mem t (Set.mem_singleton s)))
  obtain ⟨fG', _, hz, hs', _⟩ := original_sylow_involution_pair_presentation n hn SG fG
    t s hs hts hsSG hcenter
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap.symm)
  let fH := fG'.trans eSH.symm
  have hrep (x : CFSG.Open.SemidihedralGroup n) :
      (fG' x : G) = ((fH x : H) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSH.apply_symm_apply (fG' x))
    exact h.symm
  have hzH : (fH (CFSG.Semidihedral.z n) : H) = (⟨t, hKH htK⟩ : H) :=
    Subtype.ext ((hrep _).symm.trans hz)
  have hsH : (fH (CFSG.Semidihedral.s n) : H) = (⟨s, hKH hsK⟩ : H) :=
    Subtype.ext ((hrep _).symm.trans hs')
  refine ⟨hodd, SH, fH, SG, fG', hSHK, hVSG, hmap, hz, hs', hzH, hsH, ?_, hrep⟩
  simpa only [CFSG.Semidihedral.z, CFSG.Semidihedral.half, map_pow,
    Subgroup.coe_pow, CFSG.Semidihedral.modulus_div_two n (by omega)] using hzH

theorem actual_covering_subgroup_original_pair_sylow_presentation
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : CFSG.Open.SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting
      (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting
      (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting
      (Gamma t) :
        Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting
      (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t))
        .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap
        (barKappa t)).comap
          (nu t)).map
            (nu t) =
      (CFSG.generalizedFitting (Gamma t)).comap
        (barKappa t)) :
    Odd H.index ∧
      ∃ (SH : Sylow 2 H) (fH : CFSG.Open.SemidihedralGroup n ≃* SH)
        (SG : Sylow 2 G) (fG : CFSG.Open.SemidihedralGroup n ≃* SG),
        (SH : Subgroup H) ≤
          (H ⊓ C t).subgroupOf H ∧
        Subgroup.closure ({t, s} : Set G) ≤ (SG : Subgroup G) ∧
        (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
        (fG (CFSG.Semidihedral.z n) : G) = t ∧
        (fG (CFSG.Semidihedral.s n) : G) = s ∧
        (fH (CFSG.Semidihedral.z n) : H) =
          (⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩ : H) ∧
        (fH (CFSG.Semidihedral.s n) : H) =
          (⟨s, hVH (Subgroup.mem_closure_of_mem
            (Set.mem_insert_of_mem t (Set.mem_singleton s)))⟩ : H) ∧
        (fH (CFSG.Semidihedral.r n) : H) ^ (CFSG.Semidihedral.modulus n / 2) =
          (⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩ : H) ∧
        ∀ x, (fG x : G) = ((fH x : H) : G) := by
  obtain ⟨hodd, SH, _, SG, fG, hSHC, hVSG, hmap, hcenter, _, _, _⟩ :=
    actual_covering_subgroup_centered_sylow_presentation n hn S fS hG t s ht hs hsC hts
      hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hsSG : s ∈ (SG : Subgroup G) := hVSG
    (Subgroup.mem_closure_of_mem (Set.mem_insert_of_mem t (Set.mem_singleton s)))
  obtain ⟨fG', _, hz, hs', _⟩ := original_sylow_involution_pair_presentation n hn SG fG
    t s hs hts hsSG hcenter
  let eSH := ((SH : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap.symm)
  let fH := fG'.trans eSH.symm
  have hrep (x : CFSG.Open.SemidihedralGroup n) :
      (fG' x : G) = ((fH x : H) : G) := by
    have h := congrArg (fun y : SG => (y : G)) (eSH.apply_symm_apply (fG' x))
    exact h.symm
  have hzH : (fH (CFSG.Semidihedral.z n) : H) =
      (⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩ : H) :=
    Subtype.ext ((hrep _).symm.trans hz)
  have hsH : (fH (CFSG.Semidihedral.s n) : H) =
      (⟨s, hVH (Subgroup.mem_closure_of_mem
        (Set.mem_insert_of_mem t (Set.mem_singleton s)))⟩ : H) :=
    Subtype.ext ((hrep _).symm.trans hs')
  refine ⟨hodd, SH, fH, SG, fG', hSHC, hVSG, hmap, hz, hs', hzH, hsH, ?_, hrep⟩
  simpa only [CFSG.Semidihedral.z, CFSG.Semidihedral.half, map_pow,
    Subgroup.coe_pow, CFSG.Semidihedral.modulus_div_two n (by omega)] using hzH

end OriginalCoverSylow

end CFSG.Semidihedral.StationaryOddLocalization
