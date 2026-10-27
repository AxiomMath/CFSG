module

public import CFSG.CharacterTheory.Semidihedral.Principal.FourierOddDegreeProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.SubgroupAutomorphismsFourQuaternion

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

omit [Fintype G] in
theorem sylow_normalizer_eq_sup_centralizer_of_isPGroup_mulAut [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) (hAut : IsPGroup p (MulAut (P : Subgroup G))) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) =
      (P : Subgroup G) ⊔ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
  let N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let phi : N →* MulAut (P : Subgroup G) := Subgroup.normalizerMonoidHom (H := (P : Subgroup G))
  let PN : Sylow p N := P.subtype Subgroup.le_normalizer
  let R : Subgroup (MulAut (P : Subgroup G)) := phi.range
  let PR : Sylow p R := PN.mapSurjective (f := phi.rangeRestrict) phi.rangeRestrict_surjective
  have hPRtop : (PR : Subgroup R) = ⊤ :=
    (PR.is_maximal' ((hAut.to_subgroup R).to_subgroup ⊤) le_top).symm
  let xN : N := ⟨x, hx⟩
  let y : R := ⟨phi xN, ⟨xN, rfl⟩⟩
  have hyPR : y ∈ (PR : Subgroup R) := by rw [hPRtop]; trivial
  rw [Sylow.coe_mapSurjective] at hyPR
  obtain ⟨sN, hsPN, hphis⟩ := hyPR
  have hphi : phi sN = phi xN := congrArg Subtype.val hphis
  have hker : phi.ker = (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N := by
    simpa [phi, N] using Subgroup.normalizerMonoidHom_ker (H := (P : Subgroup G))
  have hcKer : sN⁻¹ * xN ∈ phi.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hphi, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hcKer
  have hx' : x = (sN : G) * ((sN⁻¹ * xN : N) : G) := by simp [xN]
  rw [hx']
  exact Subgroup.mul_mem_sup hsPN hcKer

theorem nonsimple_principal_Fourier_odd_degree_product
    (hindex : ∀ H : Subgroup G, H.index ≠ 2) (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (c₁ c₂ c₃ : basis.index)
    (hc₁B : c₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₂B : c₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hc₃B : c₃ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (h01 : principal ≠ c₁) (h02 : principal ≠ c₂) (h03 : principal ≠ c₃) (h12 : c₁ ≠ c₂)
    (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃)
    (hodd : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∃ d : ℕ, Odd d ∧ (basis.representation c).character 1 = d) ↔
        (c = principal ∨ c = c₁ ∨ c = c₂ ∨ c = c₃))
    (f₁ f₂ f₃ : ℕ) (hf₁ : (basis.representation c₁).character 1 = f₁)
    (hf₂ : (basis.representation c₂).character 1 = f₂)
    (hf₃ : (basis.representation c₃).character 1 = f₃) (q : ℕ) (hq3 : 3 ≤ q) (_hqodd : Odd q)
    (ε δ₁ δ₂ δ₃ : ℤ) (hε : ε = 1 ∨ ε = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1)
    (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (Φ : G → ℂ)
    (hΦ : ∃ y₁ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
      ∃ y₂ ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)},
        Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧ Φ y₁ ≠ Φ y₂)
    (hΦ1 : Φ 1 = q)
    (hχ₁ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₁).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        δ₁ * ε * Φ y)
    (hχ₂ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₂).character ((e (r n) : G) ^ (modulus n / 2) * y) =
        -δ₂ * ε * Φ y)
    (hχ₃ : ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ (modulus n / 2)}, Odd (orderOf y) →
      (basis.representation c₃).character ((e (r n) : G) ^ (modulus n / 2) * y) = -δ₃)
    (hdeg : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := (e (r n) : G)
    let M : ℕ := modulus n
    let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
    let lam := cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ)
    let Θ := principalCyclicProjection basis B ρ (fun x => 1 - lam x)
    lam ⟨ρ, Subgroup.mem_zpowers ρ⟩ = -1 ∧
    Θ = 1 + (δ₁ : ℂ) • χ c₁ + (δ₂ : ℂ) • χ c₂ + (δ₃ : ℂ) • χ c₃ ∧
    1 < f₁ ∧ 1 < f₂ ∧ 1 < f₃ ∧
    ((δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1)) ∧
    (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0 ∧
    f₁ * f₂ = q ^ 2 * f₃ := by
  intro B ρ M χ lam Θ
  have hAut : IsPGroup 2 (MulAut (S : Subgroup G)) :=
    (subgroup_automorphisms_outside_four_and_quaternion_eight hn ⟨e⟩).2
  have hnormalizer := sylow_normalizer_eq_sup_centralizer_of_isPGroup_mulAut S hAut
  have hone := (principal_linear_character_prime_power_from_sylow_normalizer basis ideal 2
    principal hprincipal S hnormalizer).2 hindex
  have hf₁1 := one_lt_degree_of_ne_principal basis (Ne.symm h01) (hone c₁ hc₁B) hf₁
  have hf₂1 := one_lt_degree_of_ne_principal basis (Ne.symm h02) (hone c₂ hc₂B) hf₂
  have hf₃1 := one_lt_degree_of_ne_principal basis (Ne.symm h03) (hone c₃ hc₃B) hf₃
  obtain ⟨hΘ, hsign, hQ, hprod⟩ := principal_Fourier_odd_degree_product_of_degrees hn e basis
    ideal principal hprincipal c₁ c₂ c₃ hc₁B hc₂B hc₃B h01 h02 h03 h12 h13 h23 hodd f₁ f₂ f₃
    hf₁ hf₂ hf₃ q (by omega) ε δ₁ δ₂ δ₃ hε hδ₁ hδ₂ hδ₃ Φ hΦ hΦ1 hχ₁ hχ₂ hχ₃ hdeg hf₁1 hf₂1
    hf₃1
  have hlam : lam ⟨ρ, Subgroup.mem_zpowers ρ⟩ = -1 := by
    have h := cyclicLinearCharacter_zpow (suppliedRotation_orderOf (n := n) (by omega) e)
      ((modulus n / 2 : ℕ) : ℤ) 1
    rw [mul_one, cyclicRoot_zpow_half hn] at h
    rw [← h]
    congr 1
    exact Subtype.ext (zpow_one _).symm
  exact ⟨hlam, hΘ, hf₁1, hf₂1, hf₃1, hsign, hQ, hprod⟩

end CFSG.Semidihedral.Principal
