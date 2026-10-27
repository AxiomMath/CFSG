module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerOrderFormulasSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerLocalColumn
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerDegreeProduct

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.LyonsUnitaryFour CFSG.Open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Wreathed

theorem pairing_one_sub_lambda_two {H : Type*} [Group H] [Fintype H] (f : H → ℂ) {g : H} {M : ℕ}
    (hg : orderOf g = M) :
    characterPairing (fun x : Subgroup.zpowers g => f x)
        (fun x => 1 - cyclicLinearCharacter g M 2 x) =
      ∑ v ∈ Finset.range M, ((M : ℂ)⁻¹ * (1 - cyclicRoot M ^ (-(2 * (v : ℤ))))) * f (g ^ v) := by
  have h0 := characterPairing_zpowers_cyclicLinearCharacter f hg 0
  have h2 := characterPairing_zpowers_cyclicLinearCharacter f hg 2
  have hsplit : characterPairing (fun x : Subgroup.zpowers g => f x)
      (fun x => 1 - cyclicLinearCharacter g M 2 x) =
      characterPairing (fun x : Subgroup.zpowers g => f x) (cyclicLinearCharacter g M 0) -
        characterPairing (fun x : Subgroup.zpowers g => f x) (cyclicLinearCharacter g M 2) := by
    unfold characterPairing
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cyclicLinearCharacter_zero]
    ring
  rw [hsplit, h0, h2]
  unfold cyclicMultiplicity
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [zero_mul, neg_zero, zpow_zero]
  ring


@[expose] def ActualPrincipalOrderFormulas (G : Type) [Group G] (t s : G) (q : ℕ) (e δ₁ δ₂ : ℤ)
    (f₁ f₂ : ℕ) : Prop :=
  ((f₁ : ℚ) - e * δ₁ * q ≠ 0) ∧ ((f₂ : ℚ) + e * δ₂ * q ≠ 0) ∧
  (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) ^ 3 /
      (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) :
        Subgroup G) : ℚ) ^ 2 * ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q) ∧
  (Nat.card G : ℚ) = (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℚ) ^ 3 /
      (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) :
        Subgroup G) : ℚ) ^ 2 * ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q)

theorem card_centralizer_centeredReflection {G : Type} [Group G] [Fintype G] {n : ℕ}
    (hn : 4 ≤ n) {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) :
    Nat.card (Subgroup.centralizer ({centeredReflection hn e' hcent} : Set (C t))) =
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G) := by
  have h : Subgroup.centralizer ({centeredReflection hn e' hcent} : Set (C t)) =
      (Subgroup.centralizer ({(e' (s n) : G)} : Set G)).subgroupOf (C t) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
      Subgroup.coe_mul, coe_centeredReflection]
  rw [h, inf_comm, ← Subgroup.card_subtype (C t), Subgroup.subgroupOf_map_subtype]


theorem sum_three_indicators {ι : Type*} [DecidableEq ι] (B : Finset ι) (F : ι → ℂ)
    {x y z : ι} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) (b c : ℂ) :
    ∑ i ∈ B, F i * ((if i = x then 1 else 0) + b * (if i = y then 1 else 0) +
      c * (if i = z then 1 else 0)) = F x + b * F y + c * F z := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' B x, Finset.sum_ite_eq' B y, Finset.sum_ite_eq' B z,
    ite_eq_left hx, ite_eq_left hy, ite_eq_left hz]
  ring

theorem actual_principal_order_formulas_of_family
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (q : ℕ) (hq : q = p ^ f) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1)
    (φ : C t → ℂ) (hφ1 : φ 1 = q) (hφnc : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ q)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q
      e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    {S : Sylow 2 G} (e' : SemidihedralGroup n ≃* (S : Subgroup G))
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) :
    ActualPrincipalOrderFormulas G t (e' (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector) := by
  subst hq
  obtain ⟨hq3, hqodd⟩ := three_le_and_odd_of_prime_pow hp hpodd hf
  have he' : e = 1 ∨ e = -1 := by
    rw [he]
    split_ifs <;> simp
  obtain ⟨F', hF', hfin', A', rho', data, hchar⟩ :=
    actual_simple_layer_involution_centralizer_local_package n hn S0 f0 hG t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel
  let := hF'
  let : Fintype F' := Fintype.ofFinite F'
  have cdata := hchar localBasis ideal inferInstance inferInstance localPrincipal hlocalPrincipal
  obtain ⟨ldelta, lphi, ldeltaPhi, hd, hphi, hdp, -, hPl, -, -, hdegp, -⟩ := cdata.characters
  have hf' : ((e' (r n) ^ (2 ^ (n - 2)) : S) : G) = t := by
    rw [Subgroup.coe_pow, ← hcent, modulus_div_two n (by omega), half]
  obtain ⟨P, eC, heq, heC⟩ := actualLayer_exists_centralizer_presentation n hn S e' hf'
  obtain ⟨-, -, hβt, hβσ, η, hηB, hηp, -, hηβ, -, -, hη1, hηt, hησ, hcoefC⟩ :=
    actual_layer_local_principal_column n hn S0 f0 hG t ht F' A' p f hp hpodd hf rho' data
      localBasis ideal localPrincipal hlocalPrincipal cdata ldelta lphi ldeltaPhi hd hphi hdp P eC
      heC
  beta_reduce at hβt hβσ hηt hησ hη1 hcoefC
  have hε : (if Nat.card F' % 4 = 1 then (1 : ℤ) else -1) = e := by
    rw [data.field_card, he]
  rw [hε] at hβσ hη1 hηt hcoefC
  obtain ⟨ξ, hξB, hξp, hξ1', -, -, hξ1, hξt, hcoefG⟩ :=
    actual_global_principal_column hG hn e' hcent basis ideal principal hprincipal localBasis
      localPrincipal (p ^ f) hq3 hqodd e he' (2 ^ (n - 3)) φ hφ1 hφnc δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν
      hfam hdeg
  set M := modulus n with hMdef
  set ρC : C t := (eC (r n) : C t) with hρC
  have hρCG : (ρC : G) = (e' (r n) : G) := heq (r n)
  have hρM : orderOf (ρC : G) = M := by
    rw [hρCG]
    exact suppliedRotation_orderOf (by omega) e'
  have hρt : (ρC : G) ^ (M / 2) = t := by rw [hρCG, hcent]
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  let w : ℕ → ℂ := fun v => (M : ℂ)⁻¹ * (1 - cyclicRoot M ^ (-(2 * (v : ℤ))))
  have hw0 : w 0 = 0 := by simp [w]
  have hBr := fourier_summed_brauer_order_formula basis ideal principal hprincipal ht2
    localBasis localPrincipal hlocalPrincipal ρC ⟨n - 1, rfl⟩ hρM hρt w hw0
  have hglob : ∀ χ, (∑ v ∈ Finset.range M, w v * (basis.representation χ).character
      ((ρC : G) ^ v)) = characterPairing (fun x : Subgroup.zpowers (e' (r n) : G) =>
        (basis.representation χ).character x)
        (fun x => 1 - cyclicLinearCharacter (e' (r n) : G) (modulus n) 2 x) := by
    intro χ
    rw [pairing_one_sub_lambda_two _ (suppliedRotation_orderOf (by omega) e'), hρCG]
  have hloc : ∀ α, (∑ v ∈ Finset.range M, w v * (localBasis.representation α).character
      (ρC ^ v)) = characterPairing (fun x : Subgroup.zpowers ρC =>
        (localBasis.representation α).character x)
        (fun x => 1 - cyclicLinearCharacter ρC (modulus n) 2 x) := by
    intro α
    rw [pairing_one_sub_lambda_two _ (by rw [← Subgroup.orderOf_coe]; exact hρM)]
  obtain ⟨-, hδ₁, hδ₂, hδ₃, hδ₄, hnd, -, -, -, -, -, hB, -, -, hsec, hrel⟩ := hfam
  obtain ⟨hv1, hv2, -, -, -, -⟩ := hsec 1 (by simp)
  simp only [OneMemClass.coe_one, mul_one, hφ1] at hv1 hv2
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  set BC := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hBCdef
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hχ₁B : χ₁ ∈ B := by
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hpBC : localPrincipal ∈ BC := coefficientBlock_self_mem _ _ _
  have hlphiBC : lphi ∈ BC := (hPl lphi (by simp)).2.1
  set q : ℕ := p ^ f with hqdef
  set f₁ : ℕ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ : ℕ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  have hSG : ∑ χ ∈ B, (basis.representation χ).character t *
        (basis.representation χ).character t *
        (∑ v ∈ Finset.range M, w v * (basis.representation χ).character ((ρC : G) ^ v)) /
          (basis.representation χ).character 1 =
      (((1 : ℚ) + δ₁ * (q : ℚ) ^ 2 / (f₁ : ℚ) - δ₁ * (1 + e * (q : ℚ)) ^ 2 / ((f₁ : ℚ) + δ₁) :
        ℚ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hglob χ, hcoefG χ hχ])]
    have hterm : ∀ χ, (basis.representation χ).character t *
        (basis.representation χ).character t *
        ((((if χ = principal then 1 else 0) + δ₁ * (if χ = χ₁ then 1 else 0) -
          δ₁ * (if χ = ξ then 1 else 0) : ℤ)) : ℂ) / (basis.representation χ).character 1 =
        ((basis.representation χ).character t * (basis.representation χ).character t /
          (basis.representation χ).character 1) *
        ((if χ = principal then 1 else 0) + (δ₁ : ℂ) * (if χ = χ₁ then 1 else 0) +
          (-(δ₁ : ℂ)) * (if χ = ξ then 1 else 0)) := by
      intro χ
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun χ _ => hterm χ), sum_three_indicators B _ hpB hχ₁B hξB]
    rw [hprincipal, hv1, hξt, hξ1, (basis_character_one basis χ₁).1]
    simp only [Pi.one_apply]
    push_cast
    rcases hδ₁ with rfl | rfl <;> rcases he' with rfl | rfl <;> ring
  set sC := centeredReflection hn e' hcent with hsCdef
  have hσ : (eC (s n) : C t) = sC :=
    Subtype.ext ((heq (s n)).trans (coe_centeredReflection hn e' hcent).symm)
  rw [hσ] at hβσ hησ
  set c : ℕ := Nat.card (C t) with hcdef
  set d : ℕ := Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
    Subgroup.centralizer ({(e' (s n) : G)} : Set G) : Subgroup G) with hddef
  have hdC := card_centralizer_centeredReflection hn e' hcent
  have hcw : ∀ α : localBasis.index, classWeight (C t) (localBasis.representation α).character t =
      (localBasis.representation α).character (tInC t) / c +
        (localBasis.representation α).character sC / d := by
    intro α
    rw [classWeight_centered hn S0 f0 hG e' hcent _ fun x y =>
      (Representation.char_conj _ x y), hdC]
  have hSC : ∑ α ∈ BC, classWeight (C t) (localBasis.representation α).character t *
        classWeight (C t) (localBasis.representation α).character t *
        (∑ v ∈ Finset.range M, w v * (localBasis.representation α).character (ρC ^ v)) /
          (localBasis.representation α).character 1 =
      ((((1 : ℚ) / c + 1 / d) ^ 2 + e / (q : ℚ) * ((q : ℚ) / c - e / d) ^ 2 -
        e * ((q : ℚ) + e) / (c : ℚ) ^ 2 : ℚ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun α hα => by rw [hloc α, hcoefC α hα])]
    have hterm : ∀ α, classWeight (C t) (localBasis.representation α).character t *
        classWeight (C t) (localBasis.representation α).character t *
        ((if α = localPrincipal then 1 else 0) + (e : ℂ) * (if α = lphi then 1 else 0) -
          (e : ℂ) * (if α = η then 1 else 0)) / (localBasis.representation α).character 1 =
        (classWeight (C t) (localBasis.representation α).character t *
          classWeight (C t) (localBasis.representation α).character t /
          (localBasis.representation α).character 1) *
        ((if α = localPrincipal then 1 else 0) + (e : ℂ) * (if α = lphi then 1 else 0) +
          (-(e : ℂ)) * (if α = η then 1 else 0)) := by
      intro α
      ring
    rw [Finset.sum_congr rfl (fun α _ => hterm α), sum_three_indicators BC _ hpBC hlphiBC hηB,
      hcw, hcw, hcw, hlocalPrincipal]
    simp only [Pi.one_apply]
    rw [hβt, hβσ, hηt, hησ, hη1, (basis_character_one localBasis lphi).1, hdegp]
    have hq0 : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hqe : ((q : ℕ) : ℂ) + (e : ℂ) ≠ 0 := by
      rcases he' with rfl | rfl <;> push_cast <;> intro h
      · have : ((q : ℕ) : ℂ) = -1 := by linear_combination h
        have h2 : ((q : ℕ) : ℝ) = -1 := by exact_mod_cast this
        have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
        linarith
      · have : ((q : ℕ) : ℂ) = 1 := by linear_combination h
        have h2 : q = 1 := by exact_mod_cast this
        omega
    have hc0 : ((c : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hd0 : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    push_cast
    field_simp
    rcases he' with rfl | rfl <;> ring
  have hM2 : (2 : ℕ) ^ (n - 1) = M := rfl
  rw [hM2] at hBr
  rw [hSG, hSC] at hBr
  have hQ : (Nat.card G : ℚ) * ((1 : ℚ) + δ₁ * (q : ℚ) ^ 2 / (f₁ : ℚ) -
        δ₁ * (1 + e * (q : ℚ)) ^ 2 / ((f₁ : ℚ) + δ₁)) =
      (c : ℚ) ^ 3 * (((1 : ℚ) / c + 1 / d) ^ 2 + e / (q : ℚ) * ((q : ℚ) / c - e / d) ^ 2 -
        e * ((q : ℚ) + e) / (c : ℚ) ^ 2) := by
    have h' : (((Nat.card G : ℚ) * ((1 : ℚ) + δ₁ * (q : ℚ) ^ 2 / (f₁ : ℚ) -
        δ₁ * (1 + e * (q : ℚ)) ^ 2 / ((f₁ : ℚ) + δ₁)) : ℚ) : ℂ) =
        (((c : ℚ) ^ 3 * (((1 : ℚ) / c + 1 / d) ^ 2 + e / (q : ℚ) * ((q : ℚ) / c - e / d) ^ 2 -
          e * ((q : ℚ) + e) / (c : ℚ) ^ 2) : ℚ) : ℂ) := by
      rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_natCast]
      rw [hBr]
      ring
    exact_mod_cast h'
  have hδ₁Q : (δ₁ : ℚ) = 1 ∨ (δ₁ : ℚ) = -1 := by
    rcases hδ₁ with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> rfl
  have heQ : (e : ℚ) = 1 ∨ (e : ℚ) = -1 := by
    rcases he' with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> rfl
  obtain ⟨hf₁1, hf₂1, hf₃1, -, hsign, -, -, hprod, -⟩ := hdeg
  have hf₁Q : (1 : ℚ) < f₁ := by exact_mod_cast hf₁1
  have hqQ : (1 : ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hcQ : (0 : ℚ) < c := by exact_mod_cast Nat.card_pos
  have hdQ : (0 : ℚ) < d := by exact_mod_cast Nat.card_pos
  have hf₁δ : (f₁ : ℚ) + δ₁ ≠ 0 := by rcases hδ₁Q with h | h <;> rw [h] <;> linarith
  rw [order_formula_global_bracket hδ₁Q heQ (by linarith) hf₁δ,
    order_formula_local_bracket heQ hcQ.ne' hdQ.ne' (by linarith)] at hQ
  obtain ⟨hne₁, hG₁⟩ := order_formula_solve heQ hδ₁Q hf₁Q hqQ hcQ hdQ hQ
  obtain ⟨-, -, hrel1, -⟩ := hrel 1 (by simp)
  rw [(basis_character_one basis χ₁).1, (basis_character_one basis χ₂).1,
    (basis_character_one basis χ₃).1] at hrel1
  set f₃ : ℕ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  have hδ₂Q : (δ₂ : ℚ) = 1 ∨ (δ₂ : ℚ) = -1 := by
    rcases hδ₂ with h | h <;> [left; right] <;> rw [h] <;> push_cast <;> rfl
  have hdegQ : 1 + (δ₁ : ℚ) * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 := by
    have h : (((1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ : ℤ) : ℚ) : ℂ) = 0 := by
      push_cast
      exact hrel1
    exact_mod_cast h
  have hprodQ : (f₁ : ℚ) * f₂ = (q : ℚ) ^ 2 * f₃ := by exact_mod_cast hprod
  have hsignQ : (δ₁ : ℚ) * δ₂ = δ₃ := by
    rcases hsign with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> norm_num
  have hab : ((δ₁ : ℚ) * f₁) * ((δ₂ : ℚ) * f₂) + (q : ℚ) ^ 2 * (1 + δ₁ * f₁ + δ₂ * f₂) = 0 := by
    linear_combination ((δ₁ : ℚ) * δ₂) * hprodQ + (q : ℚ) ^ 2 * hdegQ +
      (q : ℚ) ^ 2 * (f₃ : ℚ) * hsignQ
  have hae : (δ₁ : ℚ) * f₁ - e * q ≠ 0 := by
    intro h
    apply hne₁
    rcases hδ₁Q with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith
  obtain ⟨hbe, hratio⟩ := order_formula_second heQ hqQ hab hae
  have hne₂ : (f₂ : ℚ) + e * δ₂ * q ≠ 0 := by
    intro h
    apply hbe
    rcases hδ₂Q with h2 | h2 <;> rw [h2] at h ⊢ <;> linarith
  have hA : (f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2 =
      ((δ₁ : ℚ) * f₁) * (δ₁ * f₁ + 1) / (δ₁ * f₁ - e * q) ^ 2 := by
    rcases hδ₁Q with h | h <;> rw [h] <;> ring
  have hB : (f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2 =
      ((δ₂ : ℚ) * f₂) * (δ₂ * f₂ + 1) / (δ₂ * f₂ + e * q) ^ 2 := by
    rcases hδ₂Q with h | h <;> rw [h] <;> ring
  have hqe : (q : ℚ) - e ≠ 0 := by rcases heQ with h | h <;> rw [h] <;> linarith
  have hq0 : (q : ℚ) ≠ 0 := by linarith
  have hG₂ : (Nat.card G : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * (((q : ℚ) - e) / q) := by
    rw [hB, hratio, hG₁, hA]
    field_simp
  exact ⟨hne₁, hne₂, hG₁, hG₂⟩

theorem actual_nonsimple_layer_principal_order_formulas
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      φ 1 = Nat.card F ∧ (∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F) ∧
      ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ∧
        (∃ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t) ∧
        ∀ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t →
          ActualPrincipalOrderFormulas G t (e' (s n) : G) (Nat.card F) e δ₁ δ₂
            (Module.finrank ℂ (basis.representation χ₁).vector)
            (Module.finrank ℂ (basis.representation χ₂).vector)) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, hrest⟩ :=
    actual_nonsimple_layer_principal_degree_product n hn S0 f0 hG t ht hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hlin, ?_⟩
  intro φ e
  obtain ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg⟩ := hrest
  refine ⟨hφ1, hφnc, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg, ?_, ?_⟩
  · obtain ⟨-, St, ft, -, hft⟩ :=
      InvolutionFusion.involution_centered_sylow_existence n hn S0 f0 hG t ht
    refine ⟨St, ft, ?_⟩
    rw [modulus_div_two n (by omega), half, ← Subgroup.coe_pow]
    exact hft
  · intro S e' hcent
    exact actual_principal_order_formulas_of_family n hn S0 f0 hG t ht hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal (Nat.card F) hcard e rfl φ hφ1 hφnc δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg e'
      hcent

theorem actual_simple_layer_principal_order_formulas
    {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      φ 1 = Nat.card F ∧ (∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F) ∧
      ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
        ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal
          (Nat.card F) e (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
        ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ∧
        (∃ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t) ∧
        ∀ (S : Sylow 2 G) (e' : SemidihedralGroup n ≃* (S : Subgroup G)),
          (e' (r n) : G) ^ (modulus n / 2) = t →
          ActualPrincipalOrderFormulas G t (e' (s n) : G) (Nat.card F) e δ₁ δ₂
            (Module.finrank ℂ (basis.representation χ₁).vector)
            (Module.finrank ℂ (basis.representation χ₂).vector)) :=
  actual_nonsimple_layer_principal_order_formulas n hn S0 f0
    (index_ne_two_of_isSimpleGroup hGnonab) t ht hnonab hcentral hnc p f hp hpodd hf hmodel ideal
    basis principal hprincipal localBasis localPrincipal hlocalPrincipal

end CFSG.Semidihedral.Principal
