module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFiveInversionFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.OrderOneTwentyFourInvolutionSum
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace ParameterNineNonregular

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

theorem trace_mul_of_finrank_eq_one {U : Type*} [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (h : Module.finrank ℂ U = 1) (f g : Module.End ℂ U) :
    LinearMap.trace ℂ U (f * g) = LinearMap.trace ℂ U f * LinearMap.trace ℂ U g := by
  let b := Module.finBasisOfFinrankEq ℂ U h
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul]
  simp [Matrix.trace_fin_one, Matrix.mul_apply]

theorem character_eq_one_of_finrank_eq_one {G : Type*} [Group G] [Group.IsPerfect G]
    {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (σ : Representation ℂ G U) (h : Module.finrank ℂ U = 1) : σ.character = 1 := by
  let ψ : G →* ℂ :=
    { toFun := σ.character
      map_one' := by rw [Representation.char_one, h, Nat.cast_one]
      map_mul' := fun x y => by
        change LinearMap.trace ℂ U (σ (x * y)) =
          LinearMap.trace ℂ U (σ x) * LinearMap.trace ℂ U (σ y)
        rw [map_mul, trace_mul_of_finrank_eq_one h] }
  funext g
  have hg : g ∈ ψ.toHomUnits.ker := Abelianization.commutator_subset_ker ψ.toHomUnits
    (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top g)
  have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hg)
  rw [Pi.one_apply]
  exact h1

theorem two_le_finrank_of_ne_principal {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (basis : FiniteIrreducibleCharacterBasis G) (principal χ : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (hχ : χ ≠ principal) :
    2 ≤ Module.finrank ℂ (basis.representation χ).vector := by
  have h0 : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by
    have h := irreducible_character_degree_ne_zero _ (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  have h1 : Module.finrank ℂ (basis.representation χ).vector ≠ 1 := by
    intro h1
    apply hχ
    apply basis.distinct
    change (basis.representation χ).character = (basis.representation principal).character
    rw [hprincipal]
    exact character_eq_one_of_finrank_eq_one _ h1
  omega

theorem sum_kleinFour_character {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
    (σ : Representation ℂ G U) (V : Subgroup G) [Fintype V] [IsKleinFour V] (t : G)
    (hconj : ∀ x : V, x ≠ 1 → IsConj (x : G) t) :
    ∑ x : V, σ.character (x : G) = σ.character 1 + 3 * σ.character t := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : V))]
  have hval : ∀ x ∈ (Finset.univ : Finset V).erase 1, σ.character (x : G) = σ.character t := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj x (Finset.ne_of_mem_erase hx))
    rw [← hc, Representation.char_conj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, IsKleinFour.card_four', OneMemClass.coe_one, nsmul_eq_mul]
  norm_num

theorem padicValNat_eq_of_eq_pow_mul {N p k a : ℕ} (hp : p.Prime) (hN : N = p ^ k * a)
    (ha : ¬ p ∣ a) : padicValNat p N = k := by
  have : Fact p.Prime := ⟨hp⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (dvd_zero p)
  rw [hN, padicValNat.mul (pow_ne_zero _ hp.ne_zero) ha0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd ha, add_zero]

theorem le_of_order_identity {N f k δ : ℤ} (hN : 0 ≤ N) (hk0 : 0 ≤ k) (hkf : k ≤ f)
    (hf : 2 ≤ f) (hδ : δ = 1 ∨ δ = -1) (h : 16 * N * (f - k) ^ 2 = 279936000 * f * (f + δ)) :
    8748000 ≤ N := by
  have h1 : (f - k) ^ 2 ≤ f ^ 2 := by nlinarith
  have h2 : N * (f - k) ^ 2 ≤ N * f ^ 2 := mul_le_mul_of_nonneg_left h1 hN
  have h3 : f * (f - 1) ≤ f * (f + δ) := by
    apply mul_le_mul_of_nonneg_left _ (by omega)
    rcases hδ with rfl | rfl <;> omega
  by_contra hlt
  push Not at hlt
  have h4 : N * f ^ 2 ≤ 8747999 * f ^ 2 :=
    mul_le_mul_of_nonneg_right (by omega) (sq_nonneg f)
  have h5 : 2 * f ≤ f ^ 2 := by nlinarith
  nlinarith

theorem le_card_of_five_sylow_order_one_twenty_normalizer {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G] (t : G) (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (V W : Subgroup G) [IsKleinFour V] (hW : Nat.card W = 5)
    (P : Sylow 5 G) (hPW : (P : Subgroup G) = W)
    (hH : Nat.card (Subgroup.normalizer (W : Set G)) = 120)
    (hHV : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hD : Subgroup.centralizer (V : Set G) = V ⊔ W)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set G)) = 1440) :
    8748000 ≤ Nat.card G := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr hcon
    rw [hbot, Subgroup.card_bot] at hW
    norm_num at hW
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
  obtain ⟨⟨ideal, hmax, h5⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 5 (by norm_num)
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 5 := hchar ideal hmax h5
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  have hPcard : Nat.card P = 5 := by rw [hPW]; exact hW
  have hPidx : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2 := by
    change (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 2
    rw [hPW, ← hHdef]
    exact hKH
  obtain ⟨δ, χ, -, -, hδ, hχ, -, -, -, -, -, -, -, -, -, hpos, -, -, -, hsum⟩ :=
    cyclic_five_sylow_inversion_normalizer_principal_block_four_character_family basis ideal
      principal hprincipal P w (hPW.trans hWw) hPcard hPidx
  have hglobal := hsum t t w (by rw [ht2]; norm_num) (by rw [ht2]; norm_num) (by rw [hwo])
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
  rw [hlocal', hH, hC, mul_one] at hform
  change (Nat.card G : ℂ) * ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal, (basis.representation label).character t *
        (basis.representation label).character t * (basis.representation label).character w /
          (basis.representation label).character 1 = _ at hform
  rw [hglobal] at hform
  have hVconj : ∀ x : V, x ≠ 1 → IsConj (x : G) t := by
    intro x hx
    rw [← hinvol, Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact IsKleinFour.mul_self x) hx
  have : Invertible (Nat.card V : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set f := Module.finrank ℂ (basis.representation χ).vector
  set k := Module.finrank ℂ
    (Representation.invariants ((basis.representation χ).representation.comp V.subtype))
  have hkf : k ≤ f := Submodule.finrank_le _
  have hf2 : 2 ≤ f := two_le_finrank_of_ne_principal basis principal χ hprincipal hχ
  have hχ1 : (basis.representation χ).character 1 = (f : ℂ) := Representation.char_one _
  have hinv : (4 : ℂ)⁻¹ * ((f : ℂ) + 3 * (basis.representation χ).character t) = (k : ℂ) := by
    have h := Representation.card_inv_mul_sum_char_eq_finrank
      (ρ := (basis.representation χ).representation.comp V.subtype)
    have hs := sum_kleinFour_character (basis.representation χ).representation V t hVconj
    rw [Representation.char_one] at hs
    change (Nat.card V : ℂ)⁻¹ *
      ∑ x : V, (basis.representation χ).representation.character (x : G) = _ at h
    rw [hs, IsKleinFour.card_four] at h
    push_cast at h
    exact h
  rw [hχ1] at hform
  have h3a : 3 * (basis.representation χ).character t = 4 * (k : ℂ) - f := by
    linear_combination 4 * hinv
  have hF0 : (f : ℂ) ≠ 0 := by exact_mod_cast (by omega : f ≠ 0)
  have hFδ : (f : ℂ) + (δ : ℂ) ≠ 0 := by
    have h : (((f : ℤ) + δ : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact_mod_cast h
  have hmain : (Nat.card G : ℂ) * (((f : ℂ) - (basis.representation χ).character t) *
      ((f : ℂ) - (basis.representation χ).character t)) = 31104000 * ((f : ℂ) * (f + δ)) := by
    rw [mul_div_assoc', div_eq_iff (mul_ne_zero hF0 hFδ)] at hform
    push_cast at hform
    linear_combination hform
  have hint : 16 * (Nat.card G : ℤ) * ((f : ℤ) - k) ^ 2 = 279936000 * f * (f + δ) := by
    have h : ((16 * (Nat.card G : ℤ) * ((f : ℤ) - k) ^ 2 : ℤ) : ℂ) =
        ((279936000 * (f : ℤ) * (f + δ) : ℤ) : ℂ) := by
      push_cast
      linear_combination 9 * hmain + ((Nat.card G : ℂ) *
        (7 * f - 4 * k - 3 * (basis.representation χ).character t)) * h3a
    exact_mod_cast h
  exact_mod_cast le_of_order_identity (by positivity) (by positivity) (by exact_mod_cast hkf)
    (by exact_mod_cast hf2) hδ hint

end ParameterNineNonregular

end CFSG.Semidihedral.Principal
