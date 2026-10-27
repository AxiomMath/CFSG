module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPrimesFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FixedCoreNontrivialPrimes

open CFSG.TwoRankLowerBound.Helpers CFSG.CyclicBlocks CFSG.Semidihedral.Principal

theorem add_inv_ne_sign_of_pow_eq_one {ζ : ℂ} {N : ℕ} (hN : ζ ^ N = 1)
    (hcop : Nat.Coprime N 6) (hζ : ζ ≠ 1) (c : ℂ) (hc : c = 1 ∨ c = -1) : ζ + ζ⁻¹ ≠ c := by
  intro h
  have hN0 : N ≠ 0 := by
    rintro rfl
    norm_num at hcop
  have hz0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hN
    exact zero_ne_one hN
  have hquad : ζ ^ 2 + 1 = c * ζ := by
    have h' := congrArg (· * ζ) h
    simp only [add_mul, inv_mul_cancel₀ hz0] at h'
    rw [← h']
    ring
  have hsix : ζ ^ 6 = 1 := by
    rcases hc with rfl | rfl
    · have h3 : ζ ^ 3 = -1 := by linear_combination (ζ + 1) * hquad
      calc ζ ^ 6 = (ζ ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3]; norm_num
    · have h3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hquad
      calc ζ ^ 6 = (ζ ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3]; norm_num
  have h1 : ζ ^ (Nat.gcd N 6) = 1 := pow_gcd_eq_one.mpr ⟨hN, hsix⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact hζ h1

theorem card_sylow_coprime_six {H : Type*} [Group H] [Finite H] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : 5 ≤ ℓ) (Q : Sylow ℓ H) : Nat.Coprime (Nat.card Q) 6 := by
  have hp : ℓ.Prime := Fact.out
  rw [Q.card_eq_multiplicity]
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h6 : ℓ ≤ 6 := Nat.le_of_dvd (by norm_num) h
  have hcases : ℓ = 5 ∨ ℓ = 6 := by omega
  rcases hcases with rfl | rfl
  · norm_num at h
  · norm_num at hp

theorem exists_character_add_inv_ne_sign {H : Type*} [Group H] [Fintype H] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (Q : Sylow ℓ H) [IsMulCommutative (Q : Subgroup H)]
    (basisQ : FiniteIrreducibleCharacterBasis (Q : Subgroup H)) (principalQ : basisQ.index)
    (hprincipalQ : (basisQ.representation principalQ).character = 1) {μ : basisQ.index}
    (hμ : μ ≠ principalQ) :
    ∃ w : (Q : Subgroup H), w ≠ 1 ∧ ∀ c : ℂ, (c = 1 ∨ c = -1) →
      (basisQ.representation μ).character w + (basisQ.representation μ).character w⁻¹ ≠ c := by
  have hex : ∃ w : (Q : Subgroup H), (basisQ.representation μ).character w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hμ
    apply basisQ.distinct
    show (basisQ.representation μ).character = (basisQ.representation principalQ).character
    rw [hprincipalQ]
    funext w
    exact hcon w
  obtain ⟨w, hw⟩ := hex
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hw (label_character_one_of_comm basisQ μ)
  refine ⟨w, hw1, fun c hc => ?_⟩
  have hinv : (basisQ.representation μ).character w⁻¹ =
      ((basisQ.representation μ).character w)⁻¹ :=
    eq_inv_of_mul_eq_one_right (label_character_mul_inv_of_comm basisQ μ w)
  have hpow : (basisQ.representation μ).character w ^ Nat.card (Q : Subgroup H) = 1 := by
    rw [← label_character_pow_of_comm, pow_card_eq_one', label_character_one_of_comm]
  rw [hinv]
  exact add_inv_ne_sign_of_pow_eq_one hpow (card_sylow_coprime_six hℓ Q) hw c hc

theorem prime_dvd_index_centralizer_of_inverts {H : Type*} [Group H] [Finite H] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (Q : Sylow ℓ H) (hQn : (Q : Subgroup H).Normal)
    (hQ : (Q : Subgroup H) ≠ ⊥) {c : H}
    (hc : ∀ x ∈ (Q : Subgroup H), c * x * c⁻¹ = x⁻¹) :
    ℓ ∣ (Subgroup.centralizer ({c} : Set H)).index := by
  have hp : ℓ.Prime := Fact.out
  have hnot : ¬ ℓ ∣ Nat.card (Subgroup.centralizer ({c} : Set H)) := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({c} : Set H)) ℓ
      hdvd
    have hyord : orderOf (y : H) = ℓ := by rw [Subgroup.orderOf_coe, hy]
    have hyQ : (y : H) ∈ (Q : Subgroup H) := by
      have hpgroup : IsPGroup ℓ (Subgroup.zpowers (y : H)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one])
      obtain ⟨Q', hQ'⟩ := hpgroup.exists_le_sylow
      have hQQ : Q' = Q := by
        let := Sylow.unique_of_normal Q hQn
        exact Subsingleton.elim _ _
      exact hQQ ▸ hQ' (Subgroup.mem_zpowers _)
    have hcy : c * (y : H) = (y : H) * c := (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
    have hyinv : (y : H) = (y : H)⁻¹ := by
      rw [← hc _ hyQ, hcy, mul_inv_cancel_right]
    have hy1 : (y : H) = 1 := by
      refine eq_one_of_inv_eq_self_of_odd ?_ hyinv.symm
      rw [hyord]
      exact hp.eq_two_or_odd'.resolve_left hℓ2
    rw [hy1, orderOf_one] at hyord
    exact hp.one_lt.ne hyord
  have hcardH : ℓ ∣ Nat.card H := by
    have h1 : ℓ ∣ Nat.card (Q : Subgroup H) := by
      obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      obtain ⟨k, hk⟩ := (Q.isPGroup'.exists_orderOf_dvd_pow (⟨x, hx⟩ : (Q : Subgroup H)))
      have hord : orderOf (⟨x, hx⟩ : (Q : Subgroup H)) ≠ 1 := by
        rw [Ne, orderOf_eq_one_iff]
        exact hx1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hk
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hj
        exact hord hj
      have hdvd : ℓ ∣ orderOf (⟨x, hx⟩ : (Q : Subgroup H)) := by
        rw [hj]
        exact dvd_pow_self ℓ hj0
      exact hdvd.trans (orderOf_dvd_natCard _)
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  rw [← Subgroup.card_mul_index (Subgroup.centralizer ({c} : Set H))] at hcardH
  exact (hp.dvd_mul.mp hcardH).resolve_left hnot

theorem normal_abelian_inverted_sylow_principal_sum {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ]
    (hℓ : 5 ≤ ℓ) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (Q : Sylow ℓ H) (hQn : (Q : Subgroup H).Normal)
    (hcomm : ∀ x ∈ (Q : Subgroup H), ∀ y ∈ (Q : Subgroup H), x * y = y * x)
    (hindex : (Subgroup.centralizer (Q : Set H)).index = 2)
    (τ : H) (hτ : ∀ x ∈ (Q : Subgroup H), τ * x * τ⁻¹ = x⁻¹)
    {x₁ x₂ z : H} (hx₁ : ¬ ℓ ∣ orderOf x₁) (hx₂ : ¬ ℓ ∣ orderOf x₂)
    (hz : z ∈ (Q : Subgroup H)) (hz1 : z ≠ 1) :
    ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character x₁ * (basis.representation θ).character x₂ *
        (basis.representation θ).character z / (basis.representation θ).character 1 =
      (1 - if x₁ ∈ Subgroup.centralizer (Q : Set H) then 1 else -1) *
        (1 - if x₂ ∈ Subgroup.centralizer (Q : Set H) then 1 else -1) / 2 := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  set K := Subgroup.centralizer (Q : Set H) with hK
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hNtop : Subgroup.normalizer (Q : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hQn
  have hrel : K.relIndex (Subgroup.normalizer (Q : Set H)) = 2 := by
    rw [hNtop, Subgroup.relIndex_top_right]
    exact hindex
  have hP : InvertedAbelianSylow Q τ :=
    ⟨hcomm, hrel, by rw [hNtop]; exact Subgroup.mem_top τ, hτ⟩
  have := hP.isMulCommutative
  have hQK : ∀ x ∈ (Q : Subgroup H), x ∈ K := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  have hQbot : (Q : Subgroup H) ≠ ⊥ := fun h => hz1 (by rw [h] at hz; exact hz)
  have hout : ∀ c : H, c ∉ K → ∀ x ∈ (Q : Subgroup H), c * x * c⁻¹ = x⁻¹ := by
    intro c hc
    rcases hP.conj_eq_or_inv hℓ2 (by rw [hNtop]; exact Subgroup.mem_top c) with h | h
    · exfalso
      apply hc
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h' := h x hx
      calc x * c = c * x * c⁻¹ * c := by rw [h']
        _ = c * x := by group
    · exact h
  obtain ⟨basisQ⟩ := finiteIrreducibleCharacterBasis_exists (G := (Q : Subgroup H))
  obtain ⟨principalQ, hprincipalQ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    basisQ (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalQ
  obtain ⟨T, a, b, δ, hF⟩ := inverted_family_exists basis ideal ℓ hℓ2 principal hprincipal Q τ
    hP basisQ principalQ hprincipalQ
  let sgn : H →* ℂˣ :=
    { toFun := fun x => if x ∈ K then 1 else -1
      map_one' := by simp [K.one_mem]
      map_mul' := fun x y => by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> simp [hx, hy] }
  obtain ⟨lam, hlam⟩ := character_norm_one_basis_character basis
    (linearTwist sgn (basis.representation principal))
    (by rw [linearTwist_characterPairing, characterPairing_irreducible _ _
      (basis.irreducible principal) (basis.irreducible principal), ite_eq_left rfl])
  have hlamval : ∀ x, (basis.representation lam).character x = if x ∈ K then 1 else -1 := by
    intro x
    rw [hlam, linearTwist_character, hprincipal]
    by_cases hx : x ∈ K <;> simp [sgn, hx]
  have hlam1 : (basis.representation lam).character 1 = 1 := by
    simp [hlamval, K.one_mem]
  have hlamB : lam ∈ B := by
    rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    apply centralCharacterResidueHom_eq_of_class_values
    intro C
    obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
    set k := (Subgroup.centralizer ({c} : Set H)).index with hk
    set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk c)
    have hvalP : (localCentralCharacterHom basis ideal principal v : ℂ) = k := by
      have h' := CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis c principal
      rw [hprincipal, Pi.one_apply, Pi.one_apply, mul_one, div_one] at h'
      exact h'
    have hvalL : (localCentralCharacterHom basis ideal lam v : ℂ) =
        k * (if c ∈ K then 1 else -1) := by
      have h' := CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis c lam
      rw [hlam1, div_one, hlamval c] at h'
      exact h'
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v) =
      localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal lam v)
    by_cases hc : c ∈ K
    · have heq : localCentralCharacterHom basis ideal principal v =
          localCentralCharacterHom basis ideal lam v := by
        apply Subtype.ext
        rw [hvalP, hvalL]
        simp [hc]
      rw [heq]
    · have hdvd : ℓ ∣ k :=
        prime_dvd_index_centralizer_of_inverts hℓ2 Q hQn hQbot (hout c hc)
      have hk0 : ((k : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) = 0 :=
        (CharP.cast_eq_zero_iff _ ℓ k).mpr hdvd
      have hP0 : localCentralCharacterHom basis ideal principal v =
          (k : localizedComplexIntegerRing ideal) := by
        apply Subtype.ext
        rw [hvalP]
        simp
      have hL0 : localCentralCharacterHom basis ideal lam v =
          (k : localizedComplexIntegerRing ideal) * (-1) := by
        apply Subtype.ext
        rw [hvalL]
        simp [hc]
      rw [hP0, hL0, map_mul, map_natCast, hk0, zero_mul]
  have hlamp : lam ≠ principal := by
    obtain ⟨g₀, hg₀⟩ : ∃ g : H, g ∉ K := by
      by_contra hcon
      push Not at hcon
      have hKtop : K = ⊤ := eq_top_iff.mpr fun g _ => hcon g
      rw [hKtop, Subgroup.index_top] at hindex
      omega
    intro heq
    have h' := congrFun (congrArg (fun θ => (basis.representation θ).character) heq) g₀
    simp only [hlamval g₀, hg₀, hprincipal, Pi.one_apply, ↓reduceIte] at h'
    norm_num at h'
  have hz1' : (⟨z, hz⟩ : (Q : Subgroup H)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hlama : lam = a := by
    by_contra hne
    by_cases hlb : ∃ k, lam = b k
    · obtain ⟨k, hk⟩ := hlb
      obtain ⟨w, hw1, hwne⟩ := exists_character_add_inv_ne_sign hℓ Q basisQ principalQ
        hprincipalQ (fun h => hF.T_nontrivial (h ▸ k.2))
      have hv := hF.value_b k w hw1
      rw [← hk, hlamval, ite_eq_left (hQK _ w.2)] at hv
      have hδsq : (δ : ℂ) * δ = 1 := by rcases hF.sign with h | h <;> rw [h] <;> norm_num
      apply hwne δ (by rcases hF.sign with h | h <;> rw [h] <;> norm_num)
      linear_combination (-(δ : ℂ)) * hv -
        ((basisQ.representation k).character w + (basisQ.representation k).character w⁻¹) * hδsq
    · push Not at hlb
      have h0 := hF.vanish lam hlamB hlamp hne hlb ⟨z, hz⟩ hz1'
      rw [hlamval, ite_eq_left (hQK z hz)] at h0
      exact one_ne_zero h0
  have hδ1 : (δ : ℂ) = 1 := by
    have h := hF.value_a ⟨z, hz⟩ hz1'
    rw [← hlama, hlamval, ite_eq_left (hQK z hz)] at h
    exact h.symm
  have hsum := hF.weighted_sum hp hprincipal hprinB hx₁ hx₂ ⟨z, hz⟩ hz1'
  rw [hsum, ← hlama, hlamval x₁, hlamval x₂, hlam1, hδ1]
  ring

end CFSG.Semidihedral.FixedCoreNontrivialPrimes
