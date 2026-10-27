module

public import CFSG.CharacterTheory.Semidihedral.Principal.OrderOneTwentyFourInvolutionSum
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeNumerics
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.BlockBasics.LocalRing
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.LyonsUnitaryFour CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.GorensteinWalter

namespace ParameterElevenTorus

theorem card_layer_preimage_of_trivial_core {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥) :
    Nat.card (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨F₁, hF₁, hF₁fin, A₁, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hL : Nat.card ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr eta.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, data.field_card]
  have hnu : Function.Injective (nu t) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  rw [← hL, ← Subgroup.card_map_of_injective hnu,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem cleared_second_order_formula {G : Type} [Group G] [Finite G] {t s : G} {q : ℕ}
    {e δ₁ δ₂ : ℤ} {f₁ f₂ : ℕ} (hq : 0 < q)
    (h : ActualPrincipalOrderFormulas G t s q e δ₁ δ₂ f₁ f₂) :
    (Nat.card G : ℚ) * (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ^ 2 *
        (((f₂ : ℚ) + e * δ₂ * q) ^ 2 * q) =
      (Nat.card (C t) : ℚ) ^ 3 * ((f₂ : ℚ) * ((f₂ : ℚ) + δ₂) * ((q : ℚ) - e)) := by
  obtain ⟨-, hne, -, hG⟩ := h
  change (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 /
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q) at hG
  have hd : (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  generalize (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) = D at hd hG ⊢
  generalize (f₂ : ℚ) + e * δ₂ * q = Y at hne hG ⊢
  rw [hG]
  field_simp

theorem extendedCentralizer_le_normalizer_zpowers {G : Type*} [Group G] (x : G) :
    extendedCentralizer x ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro g hg
  have hy : Subgroup.zpowers (g⁻¹ * x * g) = Subgroup.zpowers x := by
    rcases (mem_extendedCentralizer x g).mp hg with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hconj : ∀ k : ℤ, (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
    intro k
    have h := conj_zpow (i := k) (a := g⁻¹) (b := x)
    rwa [inv_inv] at h
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hy]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hconj k⟩
  · intro hh
    rw [← hy] at hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hconj k] at hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa using hk

theorem brauer_sum_of_five_normalizer_order_one_twenty {G : Type} [Group G] [Fintype G]
    (t : G) (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (V W : Subgroup G) [IsKleinFour V] (hW : Nat.card W = 5)
    (hH : Nat.card (Subgroup.normalizer (W : Set G)) = 120)
    (hHV : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hD : Subgroup.centralizer (V : Set G) = V ⊔ W)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 5] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {w : G} (hwW : w ∈ W)
    (hw1 : w ≠ 1) :
    (Nat.card G : ℂ) * ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation θ).character t * (basis.representation θ).character t *
          (basis.representation θ).character w / (basis.representation θ).character 1 =
      15 * (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hwo : orderOf w = 5 := by
    have hdvd : orderOf w ∣ 5 := hW ▸ Subgroup.orderOf_dvd_natCard W hwW
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hWw : W = Subgroup.zpowers w := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW)
    rw [hW, Nat.card_zpowers, hwo]
  have ht2 : orderOf t = 2 := (hinvol t).mpr (IsConj.refl t)
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = Subgroup.normalizer (W : Set G) := ⟨_, rfl⟩
  rw [← hHdef] at hH hHV hKH
  have hWH : W ≤ H := hHdef ▸ Subgroup.le_normalizer
  have hVK : V ≤ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.le_centralizer_iff, hD]
    exact le_sup_right
  have hVH : V ≤ H := hHdef ▸ hVK.trans (Subgroup.centralizer_le_normalizer _)
  have hEH : extendedCentralizer w ≤ H := by
    rw [hHdef, hWw]
    exact extendedCentralizer_le_normalizer_zpowers w
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation H)
    (principalFiniteComplexRepresentation_isIrreducible H)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  have : (V.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mpr hHV
  have : (W.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWH, hHdef]
  have : IsKleinFour (V.subgroupOf H) :=
    let e := Subgroup.subgroupOfEquivOfLe hVH
    ⟨by rw [Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩
  have hW' : Nat.card (W.subgroupOf H) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, hW]
  have : IsCyclic (W.subgroupOf H) := isCyclic_of_prime_card hW'
  have hcent : ∀ X : Subgroup G, X ≤ H → ∀ x : H,
      x ∈ Subgroup.centralizer (X.subgroupOf H : Set H) ↔
        (x : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro X hX x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx v hv
      exact congrArg Subtype.val (hx ⟨v, hX hv⟩ hv)
    · intro hx v hv
      exact Subtype.ext (hx v hv)
  have hCV : Subgroup.centralizer (V.subgroupOf H : Set H) =
      V.subgroupOf H ⊔ W.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hVH hWH, ← hD]
    ext x
    rw [hcent V hVH x, Subgroup.mem_subgroupOf]
  have hidx : (Subgroup.centralizer (W.subgroupOf H : Set H)).index = 2 := by
    have hKW : Subgroup.centralizer (W.subgroupOf H : Set H) =
        (Subgroup.centralizer (W : Set G)).subgroupOf H := by
      ext x
      rw [hcent W hWH x, Subgroup.mem_subgroupOf]
    rw [hKW]
    exact hKH
  obtain ⟨-, -, -, hloc⟩ := order_one_twenty_four_by_five_local_principal_block_involution_sum
    hH (V.subgroupOf H) (W.subgroupOf H) hW' hCV hidx localBasis ideal localPrincipal
    hlocalPrincipal
  have hlocal := hloc ⟨w, hWH hwW⟩ hwW (fun h => hw1 (congrArg Subtype.val h))
  have hwdvd : orderOf ((⟨w, hWH hwW⟩ : H) : G) ∣ 5 ^ 1 := by
    change orderOf w ∣ 5 ^ 1
    rw [hwo, pow_one]
  have hform := (brauer_principal_order_formula basis ideal 5 principal hprincipal htt htt H
    ⟨w, hWH hwW⟩ 1 hwdvd hEH localBasis localPrincipal hlocalPrincipal).1 1 (Subgroup.one_mem _)
    (by rw [orderOf_one]; exact Nat.coprime_one_right 5)
  have hcw : ∀ ψ : H → ℂ, classWeight H ψ t =
      (Nat.card H : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : H => orderOf x = 2), ψ x := by
    intro ψ
    rw [classWeight, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : IsConj (x : G) t ↔ orderOf x = 2 := by rw [← hinvol, Subgroup.orderOf_coe]
    by_cases h : orderOf x = 2
    · rw [ite_eq_left (hx.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hx.mp h')), ite_eq_right h]
  have hlocal' : ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      localPrincipal, classWeight H (localBasis.representation label).character t *
        classWeight H (localBasis.representation label).character t *
          (localBasis.representation label).character (⟨w, hWH hwW⟩ * 1) /
            (localBasis.representation label).character 1 = 1 / 8 := by
    rw [← hlocal]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [hcw, mul_one, sq]
  rw [hlocal', hH, mul_one] at hform
  change (Nat.card G : ℂ) * ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal, (basis.representation label).character t *
        (basis.representation label).character t * (basis.representation label).character w /
          (basis.representation label).character 1 = _ at hform
  rw [hform]
  push_cast
  ring

theorem card_fixed_eq_two_of_pow_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 11)
    {σ : Equiv.Perm (Omega F)} (hσG : σ ∈ coordinateG F) (hσ1 : σ ≠ 1) (hσ5 : σ ^ 5 = 1) :
    Nat.card {x : Omega F // σ x = x} = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : Nat.card {x : Omega F // σ x = x} ≤ 2 := by
    rw [← coordinatePSLAction_range_eq_G] at hσG
    obtain ⟨g, rfl⟩ := hσG
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hσ1 (map_one _)
    let cE : Omega F ≃ PSL2ProjectiveLine F :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F
    have he : {x : Omega F // coordinatePSLAction F g x = x} ≃
        {y : PSL2ProjectiveLine F // g • y = y} :=
      cE.subtypeEquiv (fun x => by
        rw [← coordinatePSLAction_point]
        exact cE.injective.eq_iff.symm)
    rw [Nat.card_congr he]
    exact psl2_fixedPoint_card_le_two F g hg1
  have hp : IsPGroup 5 (Subgroup.zpowers σ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hσ5 hσ1
  have hmod := hp.card_modEq_card_fixedPoints (Omega F)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) (Omega F)) =
      Nat.card {x : Omega F // σ x = x} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · rintro h ⟨τ, hτ⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k
  rw [hfix, Finite.card_option, hF] at hmod
  have hmod' : 12 % 5 = Nat.card {x : Omega F // σ x = x} % 5 := hmod
  omega

theorem card_fixed_layer_element_eq_two {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 11)
    (ρ : Γ →* coordinateE F) (hρ : Function.Injective ρ) (hL : L.map ρ = specialLayer F)
    {γ : Γ} (hγL : γ ∈ L) (hγ1 : γ ≠ 1) (hγ5 : γ ^ 5 = 1) :
    Nat.card {x : Omega F // ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) x = x} = 2 := by
  have hmem : ρ γ ∈ specialLayer F := hL ▸ Subgroup.mem_map_of_mem ρ hγL
  have hG : ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) ∈ coordinateG F := hmem
  refine card_fixed_eq_two_of_pow_five hF hG ?_ ?_
  · intro h
    apply hγ1
    apply hρ
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_pow, ← map_pow, hγ5, map_one, Subgroup.coe_one]

theorem odd_and_mem_of_real_family {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (χ₁ χ₂ χ₃ : basis.index)
    (hodd : ∀ c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Odd (Module.finrank ℂ (basis.representation c).vector) ↔
        c = principal ∨ c = χ₁ ∨ c = χ₂ ∨ c = χ₃)
    (h12 : Module.finrank ℂ (basis.representation χ₁).vector ≠
      Module.finrank ℂ (basis.representation χ₂).vector)
    (h13 : Module.finrank ℂ (basis.representation χ₁).vector ≠
      Module.finrank ℂ (basis.representation χ₃).vector)
    (h23 : Module.finrank ℂ (basis.representation χ₂).vector ≠
      Module.finrank ℂ (basis.representation χ₃).vector)
    (χ ψ₁ ψ₂ : basis.index) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (hχ : χ ≠ principal)
    (hψ₁ : ψ₁ ≠ principal) (hψ₂ : ψ₂ ≠ principal) (hψ : ψ₁ ≠ ψ₂)
    (hrχ : ∀ g : G, starRingEnd ℂ ((basis.representation χ).character g) =
      (basis.representation χ).character g)
    (hr₁ : ∀ g : G, starRingEnd ℂ ((basis.representation ψ₁).character g) =
      (basis.representation ψ₁).character g)
    (hr₂ : ∀ g : G, starRingEnd ℂ ((basis.representation ψ₂).character g) =
      (basis.representation ψ₂).character g)
    (hd₁ : (Module.finrank ℂ (basis.representation ψ₁).vector : ℤ) =
      Module.finrank ℂ (basis.representation χ).vector + δ)
    (hd₂ : (Module.finrank ℂ (basis.representation ψ₂).vector : ℤ) =
      Module.finrank ℂ (basis.representation χ).vector + δ) :
    Odd (Module.finrank ℂ (basis.representation χ).vector) ∧ (χ = χ₁ ∨ χ = χ₂ ∨ χ = χ₃) := by
  have key : ∀ θ : basis.index, θ ≠ principal →
      (∀ g : G, starRingEnd ℂ ((basis.representation θ).character g) =
        (basis.representation θ).character g) →
      Odd (Module.finrank ℂ (basis.representation θ).vector) → θ = χ₁ ∨ θ = χ₂ ∨ θ = χ₃ := by
    intro θ hθ hr ho
    have hB := real_valued_odd_degree_irreducible_mem_principal_two_block basis ideal principal
      hprincipal θ hr ho
    rcases (hodd θ hB).mp ho with h | h
    · exact absurd h hθ
    · exact h
  set f := Module.finrank ℂ (basis.representation χ).vector with hfdef
  by_cases hpar : Odd f
  · exact ⟨hpar, key χ hχ hrχ hpar⟩
  · exfalso
    have hfe : Even f := Nat.not_odd_iff_even.mp hpar
    obtain ⟨m, hm⟩ := hfe
    have ho₁ : Odd (Module.finrank ℂ (basis.representation ψ₁).vector) := by
      have h : (Module.finrank ℂ (basis.representation ψ₁).vector : ℤ) = 2 * m + δ := by
        rw [hd₁, hm]
        push_cast
        ring
      rcases hδ with rfl | rfl
      · exact ⟨m, by omega⟩
      · exact ⟨m - 1, by omega⟩
    have ho₂ : Odd (Module.finrank ℂ (basis.representation ψ₂).vector) := by
      have h : (Module.finrank ℂ (basis.representation ψ₂).vector : ℤ) = 2 * m + δ := by
        rw [hd₂, hm]
        push_cast
        ring
      rcases hδ with rfl | rfl
      · exact ⟨m, by omega⟩
      · exact ⟨m - 1, by omega⟩
    have heq : Module.finrank ℂ (basis.representation ψ₁).vector =
        Module.finrank ℂ (basis.representation ψ₂).vector := by
      have h : (Module.finrank ℂ (basis.representation ψ₁).vector : ℤ) =
          Module.finrank ℂ (basis.representation ψ₂).vector := by rw [hd₁, hd₂]
      exact_mod_cast h
    rcases key ψ₁ hψ₁ hr₁ ho₁ with h₁ | h₁ | h₁ <;>
      rcases key ψ₂ hψ₂ hr₂ ho₂ with h₂ | h₂ | h₂ <;>
      subst h₁ h₂ <;> first | exact hψ rfl | omega

theorem case_one_false {g f δ : ℤ} (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hBr : g * (f + 11 * δ) ^ 2 = 15 * 2640 ^ 2 * (f * (f - δ)))
    (hOF : g * 20 ^ 2 * ((f + 11 * δ) ^ 2 * 11) = 2640 ^ 3 * (f * (f + δ) * 10)) : False := by
  have h1 : (2640 ^ 2 * f) * (26400 * (f + δ)) = (2640 ^ 2 * f) * (66000 * (f - δ)) := by
    linear_combination 4400 * hBr - hOF
  have h2 := mul_left_cancel₀ (by positivity : (2640 : ℤ) ^ 2 * f ≠ 0) h1
  rcases hδ with rfl | rfl <;> omega

theorem case_two_false {g f δ : ℤ} (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hBr : g * (f - 11 * δ) ^ 2 = 15 * 2640 ^ 2 * (f * (f + δ)))
    (hOF : g * 20 ^ 2 * ((f - 11 * δ) ^ 2 * 11) = 2640 ^ 3 * (f * (f + δ) * 12)) : False := by
  have hpos : 0 < f + δ := by rcases hδ with rfl | rfl <;> omega
  have h1 : (2640 ^ 2 * (f * (f + δ))) * 31680 = (2640 ^ 2 * (f * (f + δ))) * 66000 := by
    linear_combination 4400 * hBr - hOF
  have h2 := mul_left_cancel₀ (by positivity : (2640 : ℤ) ^ 2 * (f * (f + δ)) ≠ 0) h1
  omega

theorem case_three_false {g f δ : ℤ} (hg : 16 ∣ g) (h8 : 8 ∣ f + δ) (hδ : δ = 1 ∨ δ = -1)
    (hBr : g * (f + δ) ^ 2 = 15 * 2640 ^ 2 * (f * (f - δ))) : False := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨k, hk⟩ := h8
  have hf : f = 8 * k - δ := by linarith
  subst hf
  rcases hδ with rfl | rfl
  · have h : 1024 * (a * k ^ 2) = 209088000 * (32 * k ^ 2 - 12 * k + 1) := by
      rw [hk] at hBr
      linear_combination hBr
    generalize a * k ^ 2 = X at h
    generalize k ^ 2 = Y at h
    omega
  · have h : 1024 * (a * k ^ 2) = 209088000 * (32 * k ^ 2 + 12 * k + 1) := by
      rw [hk] at hBr
      linear_combination hBr
    generalize a * k ^ 2 = X at h
    generalize k ^ 2 = Y at h
    omega

theorem padicValNat_two_eleven_sq_sub_one : padicValNat 2 ((11 ^ 1) ^ 2 - 1) = 3 := by
  have h : (11 ^ 1) ^ 2 - 1 = 2 ^ 3 * 15 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]

theorem alternating_four_branch_false
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 11 1)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (h2part : 2 ^ padicValNat 2 ((11 ^ 1) ^ 2 - 1) = modulus n)
    (hC : Nat.card (C t) = 2640)
    (hd : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 20)
    (V W : Subgroup G) [IsKleinFour V] (htV : t ∈ V) (hW5 : Nat.card W = 5)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G))
    (hH : Nat.card (Subgroup.normalizer (W : Set G)) = 120)
    (hHV : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ :=
      CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra! hall
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr hall
    rw [hbot, Subgroup.card_bot] at hW5
    norm_num at hW5
  have hwo : orderOf w = 5 := by
    have hdvd : orderOf w ∣ 5 := hW5 ▸ Subgroup.orderOf_dvd_natCard W hwW
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hWw : W = Subgroup.zpowers w := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW)
    rw [hW5, Nat.card_zpowers, hwo]
  have hw5 : w ^ 5 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  have hidx : ¬ 5 ∣ W.index := by
    intro hdvd
    have hmod := Sylow.card_normalizer_modEq_card (p := 5) (n := 1) (H := W)
      (by rw [hW5, pow_one])
    have hG25 : 5 ^ 2 ∣ Nat.card G := by
      rw [← Subgroup.card_mul_index W, hW5, sq]
      exact Nat.mul_dvd_mul_left 5 hdvd
    have h0 : Nat.card G % 5 ^ (1 + 1) = 0 := Nat.mod_eq_zero_of_dvd hG25
    have h1 : Nat.card (Subgroup.normalizer (W : Set G)) % 5 ^ (1 + 1) =
        Nat.card G % 5 ^ (1 + 1) := hmod
    rw [hH, h0] at h1
    norm_num at h1
  have hWp : IsPGroup 5 W := IsPGroup.of_card (n := 1) (by rw [hW5, pow_one])
  let P : Sylow 5 G := hWp.toSylow hidx
  have hPW : (P : Subgroup G) = W := rfl
  have hWD : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hwt : w * t = t * w := (Subgroup.mem_centralizer_iff.mp (hWD hwW) t htV).symm
  have hwC : w ∈ C t := Subgroup.mem_centralizer_singleton_iff.mpr hwt
  have htK : t ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hWD hx) t htV).symm
  set w' : C t := ⟨w, hwC⟩ with hw'def
  have hw'5 : w' ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hw5)
  have hw'o : orderOf w' = 5 := by rw [← Subgroup.orderOf_coe]; exact hwo
  have hw'odd : Odd (orderOf w') := by rw [hw'o]; decide
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨⟨ideal₅, hmax₅, h5mem⟩, hchar₅⟩ := CFSG.BlockBasics.residue_prime_existence 5
    (by norm_num)
  have : ideal₅.IsMaximal := hmax₅
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5 := hchar₅ ideal₅ hmax₅ h5mem
  obtain ⟨F, hfield, hfinite, ρ, hFcard, hρ, hLρ, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc 11 1
      (by norm_num) (by decide) le_rfl hmodel ideal₂ basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  obtain ⟨hφ1, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  have hOF := hOFall S fS hcent
  have hF11 : Nat.card F = 11 := by rw [hFcard]; norm_num
  have he : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by rw [hF11]; norm_num
  have hq3 : 3 ≤ Nat.card F := by rw [hF11]; norm_num
  have hqodd : Odd (Nat.card F) := by rw [hF11]; decide
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by rw [hFcard]; exact h2part
  obtain ⟨hf₁, hf₂, hf₃, -, -, -, hsigns, hsum2, hprod, -, -⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3 hqodd hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  obtain ⟨-, -, -, hc₃⟩ := actual_principal_rotation_values_and_congruences hG hn ht2 hnonab
    basis ideal₂ principal hprincipal localBasis localPrincipal (Nat.card F) hq3 hqodd _ he1 he3 _
    δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ₂ ν₂ hfam hdeg fS hcent
  obtain ⟨-, hδ₁, hδ₂, hδ₃, -, -, -, -, -, -, -, -, -, hodd2, hsec, -⟩ := hfam
  set f₁ := Module.finrank ℂ (basis.representation χ₁).vector with hf₁def
  set f₂ := Module.finrank ℂ (basis.representation χ₂).vector with hf₂def
  set f₃ := Module.finrank ℂ (basis.representation χ₃).vector with hf₃def
  have h8 : (8 : ℤ) ∣ (f₃ : ℤ) + δ₃ := by
    have h := hc₃.symm.dvd
    rwa [sub_neg_eq_add] at h
  have hM8 : ((2 ^ padicValNat 2 (11 ^ 2 - 1) : ℕ) : ℤ) = 8 := by
    rw [show (11 : ℕ) ^ 2 = (11 ^ 1) ^ 2 by norm_num, padicValNat_two_eleven_sq_sub_one]
    norm_num
  obtain ⟨h12, h13, h23⟩ := signed_degree_product_two_part_congruence_distinct 11 _ _ _ δ₁ δ₂ δ₃
    (by norm_num) (by decide) hf₁ hf₂ hf₃ hsigns hsum2 (by rw [hprod, hF11])
    (by rw [hM8]; exact h8)
  have hPcard : Nat.card P = 5 := hW5
  have hPu : (P : Subgroup G) = Subgroup.zpowers w := hWw
  obtain ⟨δ, χ, ψ, hδ, hχ, hψ, hinj, hB5, hreal, hpos, hdeg5, -, hsec5, -, hsum5⟩ :=
    prime_order_sylow_inversion_normalizer_exact_principal_block_family basis ideal₅ 5 le_rfl
      principal hprincipal P w hPu hPcard hKH
  have hBr := brauer_sum_of_five_normalizer_order_one_twenty t hinvol V W hW5 hH hHV hsup.symm
    hKH basis ideal₅ principal hprincipal hwW hw1
  rw [hsum5 t t w (by rw [ht2]; norm_num) (by rw [ht2]; norm_num) (by rw [hwo]), hC] at hBr
  obtain ⟨hχtw, -⟩ := hsec5 1 (by decide) t htK (by rw [ht2]; norm_num)
  rw [pow_one, hwt] at hχtw
  have hw'Y : w' ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) := by
    have h := Subgroup.sq_mem_of_index_two hY (w' ^ 3)
    rwa [← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_succ, hw'5, one_mul] at h
  have hκL : kappa t w' ∈ CFSG.generalizedFitting (Gamma t) := by
    rw [Subgroup.mem_comap, Subgroup.mem_comap, barKappa_nu] at hw'Y
    exact hw'Y
  have hκ1 : kappa t w' ≠ 1 := by
    intro h
    have hmem : w' ∈ NZ t := (QuotientGroup.eq_one_iff (N := NZ t) w').mp h
    have hZ : w' ∈ Z t := by
      have h' : NZ t = Z t := by
        change N t ⊔ Z t = Z t
        rw [hN, bot_sup_eq]
      rwa [h'] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hZ
    have hw2 : w ^ 2 = 1 := by
      have h1 : ((tInC t ^ k : C t) : G) = w := congrArg Subtype.val hk
      rw [← h1, Subgroup.coe_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast]
      change (t ^ 2) ^ k = 1
      rw [← ht2, pow_orderOf_eq_one, one_zpow]
    have := orderOf_dvd_of_pow_eq_one hw2
    rw [hwo] at this
    norm_num at this
  have hκ5 : kappa t w' ^ 5 = 1 := by rw [← map_pow, hw'5, map_one]
  have hfix := card_fixed_layer_element_eq_two hF11 ρ hρ hLρ hκL hκ1 hκ5
  obtain ⟨h₁t, h₂t, h₃t, -⟩ := hsec 1 (by rw [orderOf_one]; decide)
  obtain ⟨h₁w, h₂w, h₃w, -⟩ := hsec w' hw'odd
  simp only [OneMemClass.coe_one, mul_one, hφ1, he] at h₁t h₂t h₃t
  beta_reduce at h₁w h₂w
  rw [hfix, he] at h₁w h₂w
  change (basis.representation χ₁).character (t * w) = _ at h₁w
  change (basis.representation χ₂).character (t * w) = _ at h₂w
  change (basis.representation χ₃).character (t * w) = _ at h₃w
  rw [hF11] at h₁t h₂t
  have hmemB : ∀ i ∈ Finset.Icc 1 ((5 - 1) / 2),
      ψ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₅) principal := by
    intro i hi
    rw [hB5]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ψ hi))
  have hχB : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal₅) principal := by
    rw [hB5]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h1I : (1 : ℕ) ∈ Finset.Icc 1 ((5 - 1) / 2) := by decide
  have h2I : (2 : ℕ) ∈ Finset.Icc 1 ((5 - 1) / 2) := by decide
  have hdegψ : ∀ i ∈ Finset.Icc 1 ((5 - 1) / 2),
      (Module.finrank ℂ (basis.representation (ψ i)).vector : ℤ) =
        Module.finrank ℂ (basis.representation χ).vector + δ := by
    intro i hi
    have h := hdeg5 i hi
    rw [(basis_character_one basis (ψ i)).1, (basis_character_one basis χ).1] at h
    exact_mod_cast h
  obtain ⟨-, hχmem⟩ := odd_and_mem_of_real_family basis ideal₂ principal hprincipal χ₁ χ₂ χ₃
    hodd2 (fun h => h12 (by exact_mod_cast h)) (fun h => h13 (by exact_mod_cast h))
    (fun h => h23 (by exact_mod_cast h)) χ
    (ψ 1) (ψ 2) δ hδ hχ (hψ 1 h1I).1 (hψ 2 h2I).1
    (fun h => absurd (hinj (Finset.mem_coe.mpr h1I) (Finset.mem_coe.mpr h2I) h) (by norm_num))
    (hreal χ hχB) (hreal (ψ 1) (hmemB 1 h1I)) (hreal (ψ 2) (hmemB 2 h2I)) (hdegψ 1 h1I)
    (hdegψ 2 h2I)
  have hFc : (basis.representation χ).character 1 =
      (Module.finrank ℂ (basis.representation χ).vector : ℂ) := (basis_character_one basis χ).1
  have hFpos : 0 < Module.finrank ℂ (basis.representation χ).vector :=
    (basis_character_one basis χ).2
  have hF0 : (Module.finrank ℂ (basis.representation χ).vector : ℂ) ≠ 0 := by
    exact_mod_cast hFpos.ne'
  have hFδ : (Module.finrank ℂ (basis.representation χ).vector : ℂ) + (δ : ℂ) ≠ 0 := by
    have h : (((Module.finrank ℂ (basis.representation χ).vector : ℤ) + δ : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact_mod_cast h
  rw [hFc, mul_div_assoc', div_eq_iff (mul_ne_zero hF0 hFδ)] at hBr
  have h16 : (16 : ℤ) ∣ Nat.card G := by
    have hS : Nat.card (S : Subgroup G) = 2 ^ n := by
      rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n (by omega)]
    have h := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
    rw [hS] at h
    have h' : 2 ^ 4 ∣ Nat.card G := (pow_dvd_pow 2 hn).trans h
    exact_mod_cast h'
  have hOF1 := cleared_first_order_formula (by omega) hOF
  have hOF2 := cleared_second_order_formula (by omega) hOF
  rw [he, hd, hC, hF11] at hOF1 hOF2
  rcases hχmem with rfl | rfl | rfl
  ·
    have hδe : (δ : ℂ) = -(δ₁ : ℂ) := by rw [← hχtw, h₁w]; push_cast; ring
    have hδz : δ = -δ₁ := by exact_mod_cast hδe
    rw [h₁t, hδz] at hBr
    push_cast at hBr
    have hBrZ : (Nat.card G : ℤ) * ((f₁ : ℤ) + 11 * δ₁) ^ 2 =
        15 * 2640 ^ 2 * ((f₁ : ℤ) * ((f₁ : ℤ) - δ₁)) := by
      have h : ((Nat.card G : ℤ) * ((f₁ : ℤ) + 11 * δ₁) ^ 2 : ℤ) =
          ((15 * 2640 ^ 2 * ((f₁ : ℤ) * ((f₁ : ℤ) - δ₁)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hBr
      exact_mod_cast h
    have hOFZ : (Nat.card G : ℤ) * 20 ^ 2 * (((f₁ : ℤ) + 11 * δ₁) ^ 2 * 11) =
        2640 ^ 3 * ((f₁ : ℤ) * ((f₁ : ℤ) + δ₁) * 10) := by
      have h : (((Nat.card G : ℤ) * 20 ^ 2 * (((f₁ : ℤ) + 11 * δ₁) ^ 2 * 11) : ℤ) : ℚ) =
          ((2640 ^ 3 * ((f₁ : ℤ) * ((f₁ : ℤ) + δ₁) * 10) : ℤ) : ℚ) := by
        push_cast
        linear_combination hOF1
      exact_mod_cast h
    exact case_one_false hf₁ hδ₁ hBrZ hOFZ
  ·
    have hδe : (δ : ℂ) = (δ₂ : ℂ) := by rw [← hχtw, h₂w]; push_cast; ring
    have hδz : δ = δ₂ := by exact_mod_cast hδe
    rw [h₂t, hδz] at hBr
    push_cast at hBr
    have hBrZ : (Nat.card G : ℤ) * ((f₂ : ℤ) - 11 * δ₂) ^ 2 =
        15 * 2640 ^ 2 * ((f₂ : ℤ) * ((f₂ : ℤ) + δ₂)) := by
      have h : ((Nat.card G : ℤ) * ((f₂ : ℤ) - 11 * δ₂) ^ 2 : ℤ) =
          ((15 * 2640 ^ 2 * ((f₂ : ℤ) * ((f₂ : ℤ) + δ₂)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hBr
      exact_mod_cast h
    have hOFZ : (Nat.card G : ℤ) * 20 ^ 2 * (((f₂ : ℤ) - 11 * δ₂) ^ 2 * 11) =
        2640 ^ 3 * ((f₂ : ℤ) * ((f₂ : ℤ) + δ₂) * 12) := by
      have h : (((Nat.card G : ℤ) * 20 ^ 2 * (((f₂ : ℤ) - 11 * δ₂) ^ 2 * 11) : ℤ) : ℚ) =
          ((2640 ^ 3 * ((f₂ : ℤ) * ((f₂ : ℤ) + δ₂) * 12) : ℤ) : ℚ) := by
        push_cast
        linear_combination hOF2
      exact_mod_cast h
    exact case_two_false hf₂ hδ₂ hBrZ hOFZ
  ·
    have hδe : (δ : ℂ) = -(δ₃ : ℂ) := by rw [← hχtw, h₃w]
    have hδz : δ = -δ₃ := by exact_mod_cast hδe
    rw [h₃t, hδz] at hBr
    push_cast at hBr
    have hBrZ : (Nat.card G : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 =
        15 * 2640 ^ 2 * ((f₃ : ℤ) * ((f₃ : ℤ) - δ₃)) := by
      have h : ((Nat.card G : ℤ) * ((f₃ : ℤ) + δ₃) ^ 2 : ℤ) =
          ((15 * 2640 ^ 2 * ((f₃ : ℤ) * ((f₃ : ℤ) - δ₃)) : ℤ) : ℂ) := by
        push_cast
        linear_combination hBr
      exact_mod_cast h
    exact case_three_false h16 h8 hδ₃ hBrZ

end ParameterElevenTorus

end CFSG.Semidihedral.Principal
