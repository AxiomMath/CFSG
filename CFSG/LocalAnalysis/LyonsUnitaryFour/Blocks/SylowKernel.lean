module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open scoped BigOperators Classical

variable {G : Type*} [Group G]

theorem centralizer_singleton_eq_zpowers (u : G) :
    Subgroup.centralizer {u} = Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact mem_centralizer_zpowers_of_commute (show Commute u g from h.symm)
  · intro h
    exact (Subgroup.mem_centralizer_iff.mp h u (Subgroup.mem_zpowers u)).symm

theorem centralizer_zpowers_inv (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) =
      Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
  rw [← centralizer_singleton_eq_zpowers, ← centralizer_singleton_eq_zpowers]
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : Commute g u⁻¹ := h
    exact (Commute.inv_right_iff.mp this).eq
  · intro h
    have : Commute g u := h
    exact this.inv_right.eq

theorem mem_of_coprime_of_normal_complement {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (K : Subgroup H) [K.Normal] (hK : IsPGroup p (H ⧸ K)) (r : H)
    (hr : Nat.Coprime p (orderOf r)) : r ∈ K := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hK
  have h1 : orderOf (r : H ⧸ K) ∣ p ^ k := by
    rw [← hk]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (r : H ⧸ K) ∣ orderOf r := orderOf_map_dvd (QuotientGroup.mk' K) r
  have hcop : Nat.Coprime (orderOf (r : H ⧸ K)) (p ^ k) :=
    ((hr.coprime_dvd_right h2).pow_left k).symm
  have hone := Nat.Coprime.eq_one_of_dvd hcop h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hone
  exact hone

theorem local_principal_character_mul_regular [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (H : Subgroup G) (localBasis : FiniteIrreducibleCharacterBasis H)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (K : Subgroup H) [K.Normal] (hKcop : Nat.Coprime p (Nat.card K)) (hK : IsPGroup p (H ⧸ K))
    (θ : localBasis.index)
    (hθ : θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
    (r c : H) (hr : Nat.Coprime p (orderOf r)) :
    (localBasis.representation θ).character (r * c) =
      (localBasis.representation θ).character c := by
  obtain ⟨hker, -, -⟩ := normal_p_complement_principal_block localBasis ideal p localPrincipal
    hlocalPrincipal K hKcop hK
  have hrK := mem_of_coprime_of_normal_complement K hK r hr
  have hρ := (hker θ).mp hθ hrK
  rw [MonoidHom.mem_ker] at hρ
  change LinearMap.trace ℂ _ ((localBasis.representation θ).representation (r * c)) =
    LinearMap.trace ℂ _ ((localBasis.representation θ).representation c)
  rw [map_mul, hρ, one_mul]

theorem principal_character_section_inv_eq [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (u : G) (e : ℕ)
    (hu : orderOf u ∣ p ^ e)
    (K : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) [K.Normal]
    (hKcop : Nat.Coprime p (Nat.card K))
    (hK : IsPGroup p (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ K))
    (label : basis.index)
    (hlabel : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (r : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hr : Nat.Coprime p (orderOf r)) :
    (basis.representation label).character ((centralizerSelf u * r : _) : G)⁻¹ =
      (basis.representation label).character u⁻¹ := by
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  have hproj : ∀ r' : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      Nat.Coprime p (orderOf r') →
      (basis.representation label).character ((centralizerSelf u * r' : _) : G)⁻¹ =
        characterSubsetProjection localBasis
          (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
          (fun m => (basis.representation label).character m.val)
          (centralizerSelf u * r')⁻¹ := by
    intro r' hr'
    have hreg : Nat.Coprime p (orderOf (r' : G)) := by rwa [Subgroup.orderOf_coe]
    have h := principal_local_section_projection basis ideal p principal hprincipal u e hu
      localBasis localPrincipal hlocalPrincipal r' hreg (basis.representation label).character
      (fun element conjugator => Representation.char_conj _ element conjugator)
    rw [characterSubsetProjection_character basis _ label hlabel] at h
    rw [← Subgroup.coe_inv]
    exact h.symm
  have hr1 : Nat.Coprime p (orderOf (1 : Subgroup.centralizer (Subgroup.zpowers u : Set G))) := by
    simp
  rw [hproj r hr, show (u : G)⁻¹ = (((centralizerSelf u * 1 : _) :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G)⁻¹ by simp [centralizerSelf],
    hproj 1 hr1]
  rw [characterSubsetProjection_apply', characterSubsetProjection_apply']
  apply Finset.sum_congr rfl
  intro θ hθ
  congr 1
  rw [mul_inv_rev, mul_one]
  exact local_principal_character_mul_regular ideal p _ localBasis localPrincipal hlocalPrincipal
    K hKcop hK θ hθ r⁻¹ (centralizerSelf u)⁻¹ (by rwa [orderOf_inv])

theorem normal_complement_principal_sylow_kernel [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G)
    (hsylow : ∀ u ∈ (P : Subgroup G), u ≠ 1 →
      ∃ Q : Sylow p (Subgroup.centralizer {u}),
        (Q : Subgroup (Subgroup.centralizer {u})) =
          ((P : Subgroup G) ⊓ Subgroup.centralizer {u}).subgroupOf (Subgroup.centralizer {u}))
    (hcomplement : ∀ u ∈ (P : Subgroup G), u ≠ 1 →
      ∃ (K : Subgroup (Subgroup.centralizer {u})) (_ : K.Normal),
        Nat.Coprime p (Nat.card K) ∧ IsPGroup p (Subgroup.centralizer {u} ⧸ K)) :
    (∀ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ g a : G, CFSG.BlocksIsPPart p g a → a ≠ 1 →
        (basis.representation label).character g = (basis.representation label).character a) ∧
    (∀ x ∈ (P : Subgroup G), x ≠ 1 → ∀ y ∈ (P : Subgroup G),
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character x *
          starRingEnd ℂ ((basis.representation label).character y) =
        if IsConj x y then (Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {x} : Subgroup G) : ℂ)
          else 0) := by
  have hcomp' : ∀ u ∈ (P : Subgroup G), u ≠ 1 →
      ∃ (K : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) (_ : K.Normal),
        Nat.Coprime p (Nat.card K) ∧
          IsPGroup p (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ K) := by
    intro u hu hu1
    have h := hcomplement u hu hu1
    rw [centralizer_singleton_eq_zpowers] at h
    exact h
  have hpelt : ∀ u ∈ (P : Subgroup G), ∃ k : ℕ, orderOf u ∣ p ^ k := by
    intro u hu
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
    refine ⟨k, orderOf_dvd_of_pow_eq_one ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hsection : ∀ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ u ∈ (P : Subgroup G), u ≠ 1 → ∀ r : G, Commute u r → Nat.Coprime p (orderOf r) →
        (basis.representation label).character (u * r) =
          (basis.representation label).character u := by
    intro label hlabel u hu hu1 r hur hr
    have hu' : u⁻¹ ∈ (P : Subgroup G) := Subgroup.inv_mem _ hu
    have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
    obtain ⟨K, hKn, hKcop, hK⟩ := hcomp' u⁻¹ hu' hu1'
    obtain ⟨k, hk⟩ := hpelt u⁻¹ hu'
    have hrC : r⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers u⁻¹ : Set G) :=
      mem_centralizer_zpowers_of_commute (hur.inv_inv)
    have h := principal_character_section_inv_eq basis ideal p principal hprincipal u⁻¹ k hk K
      hKcop hK label hlabel ⟨r⁻¹, hrC⟩ (by rw [Subgroup.orderOf_mk, orderOf_inv]; exact hr)
    have heq : ((centralizerSelf u⁻¹ * ⟨r⁻¹, hrC⟩ : _) : G)⁻¹ = u * r := by
      change (u⁻¹ * r⁻¹)⁻¹ = u * r
      rw [mul_inv_rev, inv_inv, inv_inv, hur.eq]
    rw [heq, inv_inv] at h
    exact h
  refine ⟨?_, ?_⟩
  ·
    intro label hlabel g a hpart ha1
    obtain ⟨b, hab, hba, ⟨n, hn⟩, -, hbcop⟩ := hpart
    have hcomm : Commute a b := hab.trans hba.symm
    obtain ⟨c, -, hc⟩ := exists_conj_mem_sylow_of_le P (le_top : (P : Subgroup G) ≤ ⊤)
      (Subgroup.mem_top a) ⟨n, by rw [← hn, pow_orderOf_eq_one]⟩
    have hca1 : c * a * c⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have := congrArg (fun x => c⁻¹ * x * c) h
      simpa [mul_assoc] using this
    have hcomm' : Commute (c * a * c⁻¹) (c * b * c⁻¹) := by
      have := hcomm.map (MulAut.conj c).toMonoidHom
      simpa using this
    have hbord : Nat.Coprime p (orderOf (c * b * c⁻¹)) := by
      have := (MulAut.conj c).orderOf_eq b
      change orderOf (c * b * c⁻¹) = orderOf b at this
      rw [this]
      exact hbcop.symm
    have h := hsection label hlabel (c * a * c⁻¹) hc hca1 (c * b * c⁻¹) hcomm' hbord
    have hprod : c * a * c⁻¹ * (c * b * c⁻¹) = c * g * c⁻¹ := by
      rw [← hab]
      group
    have e1 : (basis.representation label).character (c * g * c⁻¹) =
        (basis.representation label).character g := Representation.char_conj _ g c
    have e2 : (basis.representation label).character (c * a * c⁻¹) =
        (basis.representation label).character a := Representation.char_conj _ a c
    rw [hprod, e1, e2] at h
    exact h
  ·
    intro x hx hx1 y hy
    by_cases hxy : IsConj x y
    · rw [ite_eq_left hxy]
      have hval : ∀ label, (basis.representation label).character y =
          (basis.representation label).character x := by
        intro label
        obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
        exact Representation.char_conj _ x c
      simp_rw [hval]
      obtain ⟨K, hKn, hKcop, hK⟩ := hcomp' x hx hx1
      obtain ⟨k, hk⟩ := hpelt x hx
      obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
        (G := Subgroup.centralizer (Subgroup.zpowers x : Set G))
      obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
        finiteIrreducibleCharacterBasis_contains_irreducible localBasis
          (principalFiniteComplexRepresentation _)
          (principalFiniteComplexRepresentation_isIrreducible _)
      rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
      obtain ⟨h1, h2, h3⟩ := principal_primary_column_centralizer_norm_of_normal_complement basis
        ideal p principal hprincipal x k hk localBasis localPrincipal hlocalPrincipal K hKcop hK
      rw [h1, h2]
      obtain ⟨Q, hQ⟩ := hsylow x hx hx1
      have hQcard : Nat.card (Q : Subgroup (Subgroup.centralizer {x})) =
          Nat.card ((P : Subgroup G) ⊓ Subgroup.centralizer {x} : Subgroup G) := by
        rw [hQ]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      have hQmult := Sylow.card_eq_multiplicity Q
      have hCcard : Nat.card (Subgroup.centralizer {x}) =
          Nat.card (Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
        rw [centralizer_singleton_eq_zpowers]
      obtain ⟨Q₀⟩ := (inferInstance :
        Nonempty (Sylow p (Subgroup.centralizer (Subgroup.zpowers x : Set G))))
      have hdef := h3 Q₀
      rw [Sylow.card_eq_multiplicity] at hdef
      rw [hdef, ← hCcard, ← hQmult, hQcard]
    · rw [ite_eq_right hxy]
      obtain ⟨k, hk⟩ := hpelt x hx
      obtain ⟨k', hk'⟩ := hpelt y hy
      have h := coefficientBlock_section_column_orthogonality basis ideal p principal x y 1 1 k k'
        hk hk' (by simp) (by simp) (Commute.one_right x) (Commute.one_right y) hxy
      simp only [mul_one] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro label _
      rw [finite_character_conjugate_inverse]

end CFSG.LyonsUnitaryFour
