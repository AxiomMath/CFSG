module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualSimpleLayerRegularBasis
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem centralizer_zpowers_eq_centralizer_singleton {G : Type*} [Group G] (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) = Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem principal_involution_section_integral_basis_columns_of_eq {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {t : G} (ht : orderOf t = 2)
    (S : Subgroup G) (hS : S = Subgroup.centralizer ({t} : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis S) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Fin ℓ → S → ℂ)
    (hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, Odd (orderOf y) →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        c θ * (localBasis.representation θ).character y)
    (hbindep : ∀ c : Fin ℓ → ℂ, (∀ y, Odd (orderOf y) → ∑ j, c j * b j y = 0) → c = 0)
    (d : localBasis.index → Fin ℓ → ℤ)
    (hd : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      ∀ y, Odd (orderOf y) →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y) :
    ∃ u : basis.index → Fin ℓ → ℤ,
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ y : S, Odd (orderOf y) →
          (basis.representation χ).character (t * y) = ∑ j, (u χ j : ℂ) * b j y) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ v : Fin ℓ → ℤ, (∀ y : S, Odd (orderOf y) →
            (basis.representation χ).character (t * y) = ∑ j, (v j : ℂ) * b j y) → v = u χ) ∧
      (∀ j k, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          u χ j * u χ k =
        ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
          d θ j * d θ k) ∧
      (∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a t) →
        ∀ j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (u χ j : ℂ) * starRingEnd ℂ ((basis.representation χ).character x) = 0) := by
  rw [← centralizer_zpowers_eq_centralizer_singleton] at hS
  subst hS
  exact principal_involution_section_integral_basis_columns basis ideal principal hprincipal ht
    localBasis localPrincipal hlocalPrincipal ℓ hℓ b hbmem hbindep d hd

theorem two_primary_factor_not_conj_of_odd {G : Type*} [Group G] {t x : G}
    (ht : orderOf t = 2) (hx : Odd (orderOf x)) :
    ∀ a c : G, a * c = x → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
      Odd (orderOf c) → ¬ IsConj a t := by
  rintro a c rfl hac ⟨k, hk⟩ hc hconj
  have hxc : Commute (a * c) c⁻¹ := (hac.mul_left (Commute.refl c)).inv_right
  have ha : a = a * c * c⁻¹ := by group
  have hodd : Odd (orderOf a) := by
    rw [ha]
    refine Odd.of_dvd_nat ?_ hxc.orderOf_mul_dvd_lcm
    rw [orderOf_inv]
    exact Odd.of_dvd_nat (hx.mul hc) (Nat.lcm_dvd_mul _ _)
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      rw [hk] at hodd
      exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' h.ne').mpr even_two)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  rw [hk, isConj_one_right] at hconj
  rw [hconj, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem actual_simple_layer_principal_involution_columns {G : Type} [Group G] [Fintype G]
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
      let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      (∃ lφ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation lφ).IsIrreducible ∧
        (localBasis.representation lφ).character = φ ∧
        Module.finrank ℂ (localBasis.representation lφ).vector = Nat.card F ∧
        MonoidHom.ker (localBasis.representation lφ).representation = NZ t) ∧
      ∃ U : basis.index → Fin 2 → ℤ,
        (∀ χ ∈ B, ∀ y : C t, Odd (orderOf y) →
          (basis.representation χ).character (t * y) =
            U χ 0 + U χ 1 * (1 + (e : ℂ) * φ y)) ∧
        ∑ χ ∈ B, U χ 0 * U χ 0 = 8 ∧ ∑ χ ∈ B, U χ 0 * U χ 1 = -4 ∧
        ∑ χ ∈ B, U χ 1 * U χ 1 = 2 ^ (n - 2) + 2 ∧
        U principal 0 = 1 ∧ U principal 1 = 0 ∧
        (∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
            Odd (orderOf c) → ¬ IsConj a t) →
          ∀ i, ∑ χ ∈ B, (U χ i : ℂ) * starRingEnd ℂ ((basis.representation χ).character x) =
            0) ∧
        ∀ x : G, Odd (orderOf x) →
          ∀ i, ∑ χ ∈ B, (U χ i : ℂ) * starRingEnd ℂ ((basis.representation χ).character x) =
            0) := by
  obtain ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hD, hrest⟩ :=
    actual_simple_layer_centralizer_principal_regular_basis n hn S0 f0 hG t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel ideal localBasis localPrincipal hlocalPrincipal
  refine ⟨F, hfield, hfinite, ρ, hcard, hρ, hlayer, hD, ?_⟩
  intro φ e B
  set Bloc := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hBloc
  obtain ⟨⟨lφ, hlφB, hlφirr, hlφchar, hlφdeg, hlφker⟩, -, hind, -, ⟨D, hDrows⟩, hgram⟩ := hrest
  have hlφchar' : (localBasis.representation lφ).character = φ := hlφchar
  have hind' : LinearIndependent ℤ
      ![oddRestriction (1 : C t → ℂ), oddRestriction (1 + (e : ℂ) • φ)] := hind
  have hDrows' : ∀ χ : Bloc, oddRestriction (localBasis.representation χ).character =
      D χ 0 • oddRestriction (1 : C t → ℂ) + D χ 1 • oddRestriction (1 + (e : ℂ) • φ) :=
    hDrows
  have hDD : D.transpose * D = !![8, -4; -4, ((2 ^ (n - 2) + 2 : ℕ) : ℤ)] := hgram D hDrows
  have hpB : localPrincipal ∈ Bloc := coefficientBlock_self_mem _ _ _
  have hpG : principal ∈ B := coefficientBlock_self_mem _ _ _
  have he : (e : ℂ) ≠ 0 := by
    simp only [e]
    split_ifs <;> norm_num
  have hφ1 : φ 1 = Nat.card F := by
    let _ : Fintype F := Fintype.ofFinite F
    have hfix : Nat.card {x : Omega F // ((ρ (kappa t 1) : coordinateE F) :
        Equiv.Perm (Omega F)) x = x} = Nat.card (Omega F) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
        rw [map_one, map_one]
        rfl)
    simp only [φ]
    rw [hfix, card_omega]
    push_cast
    ring
  let b : Fin 2 → C t → ℂ := ![1, 1 + (e : ℂ) • φ]
  have hb0 : ∀ y, b 0 y = 1 := fun y => rfl
  have hb1 : ∀ y, b 1 y = 1 + (e : ℂ) * φ y := fun y => rfl
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, Odd (orderOf y) →
      b j y = ∑ θ ∈ Bloc, c θ * (localBasis.representation θ).character y := by
    intro j
    fin_cases j
    · refine ⟨fun θ => if θ = localPrincipal then 1 else 0, fun y _ => ?_⟩
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hpB, ↓reduceIte,
        hlocalPrincipal, Pi.one_apply]
      exact hb0 y
    · refine ⟨fun θ => (if θ = localPrincipal then 1 else 0) +
        (if θ = lφ then (e : ℂ) else 0), fun y _ => ?_⟩
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', hpB, hlφB, ↓reduceIte, hlocalPrincipal, hlφchar', Pi.one_apply]
      exact hb1 y
  have hex : ∃ y : C t, Odd (orderOf y) ∧ φ y ≠ Nat.card F := by
    by_contra hne
    push Not at hne
    have h0 := (LinearIndependent.pair_iff.mp hind') (1 + e * (Nat.card F : ℤ)) (-1) (by
      funext y
      have hy := hne y.1 y.2
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
      simp only [oddRestriction, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        zsmul_eq_mul, hy]
      push_cast
      ring)
    exact absurd h0.2 (by norm_num)
  have hbindep : ∀ c : Fin 2 → ℂ, (∀ y : C t, Odd (orderOf y) → ∑ j, c j * b j y = 0) →
      c = 0 := by
    intro c hc
    obtain ⟨y0, hy0, hy0ne⟩ := hex
    have h1 := hc 1 (by rw [orderOf_one]; exact odd_one)
    have h2 := hc y0 hy0
    rw [Fin.sum_univ_two, hb0, hb1, hφ1] at h1
    rw [Fin.sum_univ_two, hb0, hb1] at h2
    have hsub : φ y0 - Nat.card F ≠ 0 := sub_ne_zero.mpr hy0ne
    have hc1 : c 1 = 0 := by
      have h3 : c 1 * ((e : ℂ) * (φ y0 - Nat.card F)) = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (mul_ne_zero he hsub)
    have hc0 : c 0 = 0 := by
      rw [hc1] at h1
      simpa using h1
    funext j
    fin_cases j
    · exact hc0
    · exact hc1
  let d : localBasis.index → Fin 2 → ℤ := fun θ j => if h : θ ∈ Bloc then D ⟨θ, h⟩ j else 0
  have hd : ∀ θ ∈ Bloc, ∀ y : C t, Odd (orderOf y) →
      (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y := by
    intro θ hθ y hy
    have h := congrFun (hDrows' ⟨θ, hθ⟩) ⟨y, hy⟩
    simp only [Pi.add_apply, Pi.smul_apply] at h
    simp only [oddRestriction, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      zsmul_eq_mul] at h
    rw [Fin.sum_univ_two, hb0, hb1]
    simp only [d, hθ, ↓reduceDIte]
    linear_combination h
  have hgramd : ∀ j k, ∑ θ ∈ Bloc, d θ j * d θ k = (D.transpose * D) j k := by
    intro j k
    rw [Matrix.mul_apply, ← Finset.sum_coe_sort Bloc]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [d, θ.2, ↓reduceDIte, Matrix.transpose_apply, Subtype.coe_eta]
  rw [hDD] at hgramd
  obtain ⟨u, hu, huniq, hgramu, hvanish⟩ :=
    principal_involution_section_integral_basis_columns_of_eq basis ideal principal hprincipal ht
      (C t) rfl localBasis localPrincipal hlocalPrincipal 2 (by norm_num) b hbmem hbindep d hd
  have hprow : ![1, 0] = u principal := huniq principal hpG ![1, 0] fun y _ => by
    rw [Fin.sum_univ_two, hb0, hb1, hprincipal]
    simp
  refine ⟨⟨lφ, hlφB, hlφirr, hlφchar', hlφdeg, hlφker⟩, u, fun χ hχ y hy => ?_, ?_, ?_, ?_,
    ?_, ?_, fun x hx i => hvanish x hx i,
    fun x hx i => hvanish x (two_primary_factor_not_conj_of_odd ht hx) i⟩
  · rw [hu χ hχ y hy, Fin.sum_univ_two, hb0, hb1, mul_one]
  · rw [hgramu, hgramd]
    simp
  · rw [hgramu, hgramd]
    simp
  · rw [hgramu, hgramd]
    simp
  · exact (congrFun hprow 0).symm
  · exact (congrFun hprow 1).symm

end CFSG.Semidihedral.Principal
