module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G] [Fintype G]

theorem restriction_pairing_nat (basis : FiniteIrreducibleCharacterBasis G) {H : Subgroup G}
    (localBasis : FiniteIrreducibleCharacterBasis H) (χ : basis.index) (θ : localBasis.index) :
    ∃ m : ℕ, characterPairing (fun h : H => (basis.representation χ).character (h : G))
      (localBasis.representation θ).character = m := by
  classical
  let data : FiniteComplexRepresentation H :=
    { vector := (basis.representation χ).vector
      representation := (basis.representation χ).representation.comp H.subtype }
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  have hfun : (fun h : H => (basis.representation χ).character (h : G)) =
      fun h => ∑ k, (1 : ℂ) * (summand k).character h := by
    funext h
    simp only [one_mul]
    exact hsum h
  refine ⟨(Finset.univ.filter fun k => (summand k).character =
    (localBasis.representation θ).character).card, ?_⟩
  rw [hfun, characterPairing_expansion_left]
  simp only [one_mul]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [characterPairing_irreducible _ _ (hirr k) (localBasis.irreducible θ)]
  split_ifs <;> simp

theorem principal_involution_section_integral_basis_columns
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {t : G} (ht : orderOf t = 2)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (ℓ : ℕ) (_hℓ : 1 ≤ ℓ)
    (b : Fin ℓ → Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ)
    (_hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, Odd (orderOf y) →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        c θ * (localBasis.representation θ).character y)
    (hbindep : ∀ c : Fin ℓ → ℂ, (∀ y, Odd (orderOf y) → ∑ j, c j * b j y = 0) → c = 0)
    (d : localBasis.index → Fin ℓ → ℤ)
    (hd : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      ∀ y, Odd (orderOf y) →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y) :
    ∃ u : basis.index → Fin ℓ → ℤ,
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
          (basis.representation χ).character (t * y) = ∑ j, (u χ j : ℂ) * b j y) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ v : Fin ℓ → ℤ, (∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G),
          Odd (orderOf y) →
            (basis.representation χ).character (t * y) = ∑ j, (v j : ℂ) * b j y) → v = u χ) ∧
      (∀ j k, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          u χ j * u χ k =
        ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
          d θ j * d θ k) ∧
      (∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a t) →
        ∀ j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (u χ j : ℂ) * starRingEnd ℂ ((basis.representation χ).character x) = 0) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htord : orderOf t ∣ 2 ^ 1 := by rw [ht, pow_one]
  have hodd : ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
      Nat.Coprime 2 (orderOf y) := fun y hy =>
    Nat.coprime_two_left.mpr hy
  have hself2 : centralizerSelf t ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]; exact ht2)
  choose ε hε hεt hεval using fun θ : localBasis.index =>
    (irreducible_character_central_involution_parity (localBasis.representation θ)
      (localBasis.irreducible θ) (centralizerSelf t) (centralizerSelf_mem_center t) hself2)
  have hεsq : ∀ θ, ε θ * ε θ = 1 := fun θ => by
    rcases hε θ with h | h <;> rw [h] <;> norm_num
  have hεconj : ∀ θ, starRingEnd ℂ (ε θ) = ε θ := fun θ => by
    rcases hε θ with h | h <;> rw [h] <;> simp
  let εint : localBasis.index → ℤ := fun θ => if ε θ = 1 then 1 else -1
  have hεint : ∀ θ, ((εint θ : ℤ) : ℂ) = ε θ := fun θ => by
    simp only [εint]
    rcases hε θ with h | h
    · rw [ite_eq_left h, h]; simp
    · rw [ite_eq_right (by rw [h]; norm_num), h]; simp
  have htcomm : ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      (t * (y : G)) =
        ((y * centralizerSelf t : Subgroup.centralizer (Subgroup.zpowers t : Set G)) : G) :=
    fun y => by
    rw [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp y.2 t (Subgroup.mem_zpowers t)
  choose m hm using fun (χ : basis.index) (θ : localBasis.index) =>
    restriction_pairing_nat basis localBasis χ θ
  set B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB₀
  set b₀ := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hb₀
  have hlocal : ∀ θ ∈ b₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
      (localBasis.representation θ).character (y * centralizerSelf t) =
        ε θ * ∑ j, (d θ j : ℂ) * b j y := fun θ hθ y hy => by
    rw [hεval θ y, hd θ hθ y hy]
  have hproj : ∀ χ ∈ B₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
      (basis.representation χ).character (t * y) =
        ∑ θ ∈ b₀, (m χ θ : ℂ) * (localBasis.representation θ).character (y * centralizerSelf t) :=
    by
    intro χ hχ y hy
    have hyinv :
        Nat.Coprime 2 (orderOf (y⁻¹ : Subgroup.centralizer (Subgroup.zpowers t : Set G))) := by
      rw [orderOf_inv]; exact hodd y hy
    have h := principal_local_section_projection_character basis ideal 2 principal hprincipal t 1
      htord localBasis localPrincipal hlocalPrincipal y⁻¹ (by
        rw [Subgroup.orderOf_coe]; exact hyinv) χ
    have hpt : ((⟨t, element_mem_centralizer_zpowers t⟩ :
        Subgroup.centralizer (Subgroup.zpowers t : Set G)) * y⁻¹)⁻¹ =
        y * centralizerSelf t := by
      rw [mul_inv_rev, inv_inv]
      congr 1
      apply Subtype.ext
      change t⁻¹ = t
      rw [← mul_eq_one_iff_inv_eq, ← pow_two, ht2]
    rw [hpt, characterSubsetProjection_character basis B₀ χ hχ,
      characterSubsetProjection_apply'] at h
    rw [htcomm y, ← h]
    exact Finset.sum_congr rfl fun θ _ => by rw [hm χ θ]
  let u : basis.index → Fin ℓ → ℤ := fun χ j => ∑ θ ∈ b₀, (m χ θ : ℤ) * εint θ * d θ j
  have hrow : ∀ χ ∈ B₀, ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
      (basis.representation χ).character (t * y) = ∑ j, (u χ j : ℂ) * b j y := by
    intro χ hχ y hy
    rw [hproj χ hχ y hy]
    simp only [u, Int.cast_sum, Int.cast_mul, Int.cast_natCast, hεint, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hlocal θ hθ y hy, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have huniq : ∀ (v w : Fin ℓ → ℤ), (∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      Odd (orderOf y) →
      ∑ j, (v j : ℂ) * b j y = ∑ j, (w j : ℂ) * b j y) → v = w := by
    intro v w hvw
    have h := hbindep (fun j => (v j : ℂ) - w j) fun y hy => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hvw y hy, sub_self]
    funext j
    have hj := congrFun h j
    simp only [Pi.zero_apply, sub_eq_zero] at hj
    exact_mod_cast hj
  have hcoeff : ∀ c : Fin ℓ → ℂ, (∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G),
      Odd (orderOf y) → ∑ j, c j * b j y = 0) →
      ∀ j, c j = 0 := fun c hc j => congrFun (hbindep c hc) j
  refine ⟨u, hrow, fun χ hχ v hv => huniq v (u χ) fun y hy => by rw [← hv y hy, hrow χ hχ y hy],
    ?_, ?_⟩
  ·
    have hker : ∀ y y' : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        Odd (orderOf y) → Odd (orderOf y') →
        ∑ χ ∈ B₀, (basis.representation χ).character (t * y) *
            starRingEnd ℂ ((basis.representation χ).character (t * y')) =
          ∑ θ ∈ b₀, (∑ j, (d θ j : ℂ) * b j y) * starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') := by
      intro y y' hy hy'
      have h := CFSG.LyonsUnitaryFour.brauer_principal_section_kernel basis ideal 2 principal
        hprincipal t 1 htord localBasis localPrincipal hlocalPrincipal (y * centralizerSelf t)
        (y' * centralizerSelf t)
        ⟨y, (centralizerSelf_commute t y).eq.symm, hodd y hy⟩
        ⟨y', (centralizerSelf_commute t y').eq.symm, hodd y' hy'⟩
      rw [← htcomm y, ← htcomm y'] at h
      rw [h]
      refine Finset.sum_congr rfl fun θ hθ => ?_
      rw [hlocal θ hθ y hy, hlocal θ hθ y' hy', map_mul, hεconj]
      linear_combination (∑ j, (d θ j : ℂ) * b j y) *
        starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') * (hεsq θ)
    intro j k
    set Δ : Fin ℓ → Fin ℓ → ℤ := fun j k => ∑ χ ∈ B₀, u χ j * u χ k - ∑ θ ∈ b₀, d θ j * d θ k
      with hΔ
    have hexp : ∀ y y' : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        Odd (orderOf y) → Odd (orderOf y') →
        ∑ j, (∑ k, (Δ j k : ℂ) * starRingEnd ℂ (b k y')) * b j y = 0 := by
      intro y y' hy hy'
      have hl : ∑ χ ∈ B₀, (basis.representation χ).character (t * y) *
          starRingEnd ℂ ((basis.representation χ).character (t * y')) =
          ∑ j, ∑ k, (∑ χ ∈ B₀, (u χ j * u χ k : ℂ)) * b j y * starRingEnd ℂ (b k y') := by
        rw [Finset.sum_congr rfl fun χ hχ => by
          rw [hrow χ hχ y hy, hrow χ hχ y' hy', map_sum, Finset.sum_mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul, map_intCast]
        ring
      have hr : ∑ θ ∈ b₀, (∑ j, (d θ j : ℂ) * b j y) *
          starRingEnd ℂ (∑ k, (d θ k : ℂ) * b k y') =
          ∑ j, ∑ k, (∑ θ ∈ b₀, (d θ j * d θ k : ℂ)) * b j y * starRingEnd ℂ (b k y') := by
        rw [Finset.sum_congr rfl fun θ _ => by rw [map_sum, Finset.sum_mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun θ _ => ?_
        rw [map_mul, map_intCast]
        ring
      have hkey := (hl.symm.trans (hker y y' hy hy')).trans hr
      simp only [hΔ, Int.cast_sub, Int.cast_sum, Int.cast_mul]
      have : ∀ j, (∑ k, ((∑ χ ∈ B₀, (u χ j : ℂ) * u χ k) - ∑ θ ∈ b₀, (d θ j : ℂ) * d θ k) *
          starRingEnd ℂ (b k y')) * b j y =
          ∑ k, (∑ χ ∈ B₀, (u χ j * u χ k : ℂ)) * b j y * starRingEnd ℂ (b k y') -
            ∑ k, (∑ θ ∈ b₀, (d θ j * d θ k : ℂ)) * b j y * starRingEnd ℂ (b k y') := by
        intro j
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, hkey, sub_self]
    have hrowzero : ∀ y' : Subgroup.centralizer (Subgroup.zpowers t : Set G),
        Odd (orderOf y') → ∀ j,
        ∑ k, (Δ j k : ℂ) * starRingEnd ℂ (b k y') = 0 := fun y' hy' =>
      hcoeff _ fun y hy => by rw [← hexp y y' hy hy']
    have hzero : ∀ j k, Δ j k = 0 := by
      intro j k
      have h := hcoeff (fun k => (Δ j k : ℂ)) (fun y' hy' => by
        have h0 := congrArg (starRingEnd ℂ) (hrowzero y' hy' j)
        simp only [map_sum, map_mul, map_intCast, Complex.conj_conj, map_zero] at h0
        exact h0) k
      exact_mod_cast h
    have := hzero j k
    simp only [hΔ, sub_eq_zero] at this
    exact this
  ·
    intro x hx j
    obtain ⟨a, c, e, -, -, hac, hacx, ha, hc⟩ := finite_prime_primary_factorization x 2
      Nat.prime_two
    have hnot : ¬ IsConj t a := fun h => hx a c hacx hac (by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
      exact ⟨k, hk⟩) (Nat.coprime_two_left.mp hc) h.symm
    refine hcoeff (fun j => ∑ χ ∈ B₀, (u χ j : ℂ) *
      starRingEnd ℂ ((basis.representation χ).character x)) (fun y hy => ?_) j
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal t a (y : G) c 1
      e htord ha (by rw [Subgroup.orderOf_coe]; exact hodd y hy) hc
      (Subgroup.mem_centralizer_iff.mp y.2 t (Subgroup.mem_zpowers t)) hac hnot
    rw [hacx] at h
    rw [← h]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← finite_character_conjugate_inverse, hrow χ hχ y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end CFSG.Semidihedral.Principal
