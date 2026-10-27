module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.Semidihedral.Principal.FourierSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G]

section Fusion

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {u : G}

theorem conj_eq_or_inv_of_mem_normalizer (hu : orderOf u = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {g : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹ := by
  have hpp : ℓ.Prime := hℓ.out
  have hmem : g * u * g⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hg u).mp (Subgroup.mem_zpowers u)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsq : g * g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    have h := Subgroup.mul_self_mem_of_index_two hindex ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have hsqu : (g * g) * u * (g * g)⁻¹ = u := by
    have hc := Subgroup.mem_centralizer_iff.mp hsq u (Subgroup.mem_zpowers u)
    rw [← hc]
    group
  have hkk : u ^ (k * k) = u := by
    calc u ^ (k * k) = (u ^ k) ^ k := by rw [zpow_mul]
      _ = (g * u * g⁻¹) ^ k := by rw [hk]
      _ = g * u ^ k * g⁻¹ := conj_zpow
      _ = g * (g * u * g⁻¹) * g⁻¹ := by rw [hk]
      _ = (g * g) * u * (g * g)⁻¹ := by group
      _ = u := hsqu
  have hdvd : (ℓ : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← hu, orderOf_dvd_iff_zpow_eq_one]
    have hring : (k - 1) * (k + 1) = k * k - 1 := by ring
    rw [hring, zpow_sub, hkk, zpow_one, mul_inv_cancel]
  rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd hdvd with h | h
  · left
    rw [← hk]
    have h1 : u ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hu]
      exact h
    calc u ^ k = u ^ (k - 1) * u := by rw [← zpow_add_one, sub_add_cancel]
      _ = u := by rw [h1, one_mul]
  · right
    rw [← hk]
    have h1 : u ^ (k + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hu]
      exact h
    calc u ^ k = u ^ (k + 1) * u⁻¹ := by rw [zpow_add_one, mul_inv_cancel_right]
      _ = u⁻¹ := by rw [h1, one_mul]

theorem exists_mem_normalizer_conj_eq_inv (hu : orderOf u = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    ∃ n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G), n * u * n⁻¹ = u⁻¹ := by
  have hnle : ¬ Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    intro hle
    rw [← Subgroup.relIndex_eq_one] at hle
    omega
  obtain ⟨n, hn, hnc⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨n, hn, ?_⟩
  rcases conj_eq_or_inv_of_mem_normalizer hu hindex hn with h | h
  · exfalso
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hm : n * u ^ m * n⁻¹ = u ^ m := by rw [← conj_zpow, h]
    calc u ^ m * n = n * u ^ m * n⁻¹ * n := by rw [hm]
      _ = n * u ^ m := by group
  · exact h

theorem exists_zpow_zpow_eq_self (hu : orderOf u = ℓ) {a : ℤ} (ha : ¬ (ℓ : ℤ) ∣ a) :
    ∃ b : ℤ, (u ^ a) ^ b = u := by
  have hpp : ℓ.Prime := hℓ.out
  have hnat : ¬ ℓ ∣ a.natAbs := fun h => ha (Int.natCast_dvd.mpr h)
  have hcopN : Nat.Coprime ℓ a.natAbs := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hnat
  have hcop : IsCoprime a (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using hcopN
  obtain ⟨x, y, hxy⟩ := hcop
  refine ⟨x, ?_⟩
  rw [← zpow_mul]
  have hexp : a * x = 1 + (ℓ : ℤ) * (-y) := by linear_combination hxy
  have hℓu : u ^ (ℓ : ℤ) = 1 := by
    rw [← hu, zpow_natCast, pow_orderOf_eq_one]
  rw [hexp, zpow_add, zpow_one, zpow_mul, hℓu, one_zpow, mul_one]

theorem zpow_isConj_zpow_iff (hu : orderOf u = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {a b : ℤ} (ha : ¬ (ℓ : ℤ) ∣ a) :
    IsConj (u ^ a) (u ^ b) ↔ (ℓ : ℤ) ∣ b - a ∨ (ℓ : ℤ) ∣ b + a := by
  have hone : ∀ m : ℤ, u ^ m = 1 ↔ (ℓ : ℤ) ∣ m := fun m => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hu]
  constructor
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hb : ¬ (ℓ : ℤ) ∣ b := by
      intro hdvd
      apply ha
      rw [← hone] at hdvd ⊢
      rw [hdvd] at hc
      calc u ^ a = c⁻¹ * (c * u ^ a * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group
    obtain ⟨a', ha'⟩ := exists_zpow_zpow_eq_self hu ha
    obtain ⟨b', hb'⟩ := exists_zpow_zpow_eq_self hu hb
    have hcu : c * u * c⁻¹ = u ^ (b * a') := by
      calc c * u * c⁻¹ = c * (u ^ a) ^ a' * c⁻¹ := by rw [ha']
        _ = (c * u ^ a * c⁻¹) ^ a' := conj_zpow.symm
        _ = u ^ (b * a') := by rw [hc, zpow_mul]
    have hcu' : c⁻¹ * u * c = u ^ (a * b') := by
      have hc' : c⁻¹ * u ^ b * c = u ^ a := by rw [← hc]; group
      calc c⁻¹ * u * c = c⁻¹ * (u ^ b) ^ b' * c := by rw [hb']
        _ = (c⁻¹ * u ^ b * c⁻¹⁻¹) ^ b' := by rw [conj_zpow, inv_inv]
        _ = u ^ (a * b') := by rw [inv_inv, hc', zpow_mul]
    have hnorm : c ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        rw [← conj_zpow, hcu, ← zpow_mul]
        exact Subgroup.zpow_mem_zpowers u _
      · intro hh
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
        have : h = (c⁻¹ * u * c) ^ m := by
          rw [show c⁻¹ * u * c = c⁻¹ * u * c⁻¹⁻¹ by rw [inv_inv], conj_zpow, hm]
          group
        rw [this, hcu', ← zpow_mul]
        exact Subgroup.zpow_mem_zpowers u _
    rcases conj_eq_or_inv_of_mem_normalizer hu hindex hnorm with h | h
    · left
      rw [← hone, zpow_sub, ← hc, ← conj_zpow, h, mul_inv_cancel]
    · right
      rw [← hone, zpow_add, ← hc, ← conj_zpow, h, inv_zpow', ← zpow_add, neg_add_cancel,
        zpow_zero]
  · rintro (h | h)
    · have h1 : u ^ (b - a) = 1 := (hone (b - a)).mpr h
      have hab : u ^ b = u ^ a := by
        calc u ^ b = u ^ (b - a) * u ^ a := by rw [← zpow_add, sub_add_cancel]
          _ = u ^ a := by rw [h1, one_mul]
      rw [hab]
    · obtain ⟨n, -, hn⟩ := exists_mem_normalizer_conj_eq_inv hu hindex
      have h1 : u ^ (b + a) = 1 := (hone (b + a)).mpr h
      have hab : u ^ b = u ^ (-a) := by
        calc u ^ b = u ^ (b + a) * u ^ (-a) := by rw [← zpow_add, add_neg_cancel_right]
          _ = u ^ (-a) := by rw [h1, one_mul]
      refine isConj_iff.mpr ⟨n, ?_⟩
      rw [← conj_zpow, hn, inv_zpow', hab]

theorem commute_zpow_iff (hu : orderOf u = ℓ) {a : ℤ} (ha : ¬ (ℓ : ℤ) ∣ a) {y : G} :
    Commute (u ^ a) y ↔ Commute u y := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_zpow_zpow_eq_self hu ha
    rw [← hb]
    exact h.zpow_left b
  · intro h
    exact h.zpow_left a

end Fusion

section Sections

variable [Fintype G]

theorem prime_sylow_principal_section_constant (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G)
    (hP : Nat.card P = ℓ) {v : G} (hv : v ∈ (P : Subgroup G)) (hne : v ≠ 1) {y : G}
    (hvy : Commute v y) (hy : ¬ ℓ ∣ orderOf y) {θ : basis.index}
    (hθ : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (basis.representation θ).character (v * y) = (basis.representation θ).character v := by
  have hp : ℓ.Prime := Fact.out
  have horder : orderOf v = ℓ := orderOf_eq_prime_of_mem_of_card_eq hP hv hne
  have hGfactor : (Nat.card G).factorization ℓ = 1 := by
    have h := P.card_eq_multiplicity
    rw [hP] at h
    exact Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one ℓ).symm)
  have horder' : orderOf (centralizerSelf v) = ℓ := by
    rw [centralizerSelf, Subgroup.orderOf_mk, horder]
  have hCfactor : (Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G))).factorization ℓ =
      1 := by
    have hC0 : Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G)) ≠ 0 :=
      Nat.card_pos.ne'
    have hpC : ℓ ∣ Nat.card (Subgroup.centralizer (Subgroup.zpowers v : Set G)) :=
      horder' ▸ orderOf_dvd_natCard (centralizerSelf v)
    have hle := (Nat.factorization_le_iff_dvd hC0 Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) ℓ
    have hpos := hp.factorization_pos_of_dvd hC0 hpC
    omega
  have hzpowers : IsPGroup ℓ (Subgroup.zpowers (centralizerSelf v)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder', pow_one])
  obtain ⟨S, hS⟩ := hzpowers.exists_le_sylow
  have hScard : Nat.card S = ℓ := by rw [S.card_eq_multiplicity, hCfactor, pow_one]
  have hSeq : Subgroup.zpowers (centralizerSelf v) = S :=
    Subgroup.eq_of_le_of_card_ge hS (by rw [hScard, Nat.card_zpowers, horder'])
  have hScentral : (S : Subgroup (Subgroup.centralizer (Subgroup.zpowers v : Set G))) ≤
      CFSG.centerIn (Subgroup.normalizer
        ((S : Subgroup (Subgroup.centralizer (Subgroup.zpowers v : Set G))) :
          Set (Subgroup.centralizer (Subgroup.zpowers v : Set G)))) := by
    intro s hs
    have hcenter : s ∈ Subgroup.center (Subgroup.centralizer (Subgroup.zpowers v : Set G)) := by
      rw [← hSeq] at hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact Subgroup.zpow_mem _ (centralizerSelf_mem_center v) k
    exact ⟨Subgroup.le_normalizer hs, fun n _ => Subgroup.mem_center_iff.mp hcenter n⟩
  obtain ⟨N, hNormal, hcoprime, hquotient⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer ℓ S
      hScentral
  have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    CFSG.LyonsUnitaryFour.mem_centralizer_zpowers_of_commute hvy
  have hyN : (⟨y, hyC⟩ : Subgroup.centralizer (Subgroup.zpowers v : Set G)) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    obtain ⟨k, hk⟩ := hquotient (QuotientGroup.mk ⟨y, hyC⟩)
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (QuotientGroup.mk (s := N) (⟨y, hyC⟩ :
        Subgroup.centralizer (Subgroup.zpowers v : Set G))) ∣ orderOf y := by
      have h := orderOf_map_dvd (QuotientGroup.mk' N) ⟨y, hyC⟩
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime (ℓ ^ k) (orderOf y) :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hy).pow_left k
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  exact principal_character_section_constant_of_normal_complement basis ideal ℓ principal
    hprincipal (u := v) (e := 1) (by rw [horder, pow_one]) N hcoprime hquotient hθ hyN

theorem principalCyclicProjection_eq_zero_of_regular (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (label : basis.index) {u : G}
    (hu : orderOf u = ℓ) (h : Subgroup.zpowers u → ℂ) (h1 : h 1 = 0) {g : G}
    (hg : ¬ ℓ ∣ orderOf g) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      label) u h g = 0 := by
  have hp : ℓ.Prime := Fact.out
  rw [principalCyclicProjection_eq_sum]
  apply mul_eq_zero_of_right
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = 1
  · rw [hx, inv_one, h1, zero_mul]
  · apply mul_eq_zero_of_right
    have hxne : (x : G) ≠ 1 := fun h' => hx (Subtype.ext h')
    have hxord : orderOf (x : G) ∣ ℓ ^ 1 := by
      rw [pow_one, ← hu]
      exact orderOf_dvd_of_mem_zpowers x.2
    have horth := coefficientBlock_section_column_orthogonality basis ideal ℓ label
      (x : G) 1 1 g⁻¹ 1 0 hxord (by simp) (by simp)
      (by rw [orderOf_inv]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hg)
      (Commute.one_right _) (Commute.one_left _) (fun hc => hxne (isConj_one_left.mp hc))
    simpa using horth

theorem principalCyclicProjection_prime_inversion_section
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ]
    (hℓ2 : ℓ ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow ℓ G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    (h : Subgroup.zpowers u → ℂ) {j : ℤ} (hj : ¬ (ℓ : ℤ) ∣ j) {y : G}
    (hy : Commute u y) (hyreg : ¬ ℓ ∣ orderOf y) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) u h (u ^ j * y) =
      h ⟨u ^ j, Subgroup.zpow_mem_zpowers u j⟩ +
        h ⟨u ^ (-j), Subgroup.zpow_mem_zpowers u (-j)⟩ := by
  have hp : ℓ.Prime := Fact.out
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  have hone : ∀ m : ℤ, u ^ m = 1 ↔ (ℓ : ℤ) ∣ m := fun m => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hu]
  have hmemP : ∀ m : ℤ, u ^ m ∈ (P : Subgroup G) := fun m => hPu ▸ Subgroup.zpow_mem_zpowers u m
  have hjne : u ^ j ≠ 1 := fun h' => hj ((hone j).mp h')
  have hnegj : ¬ (ℓ : ℤ) ∣ -j := fun h' => hj (dvd_neg.mp h')
  have hyj : Commute (u ^ j) y := hy.zpow_left j
  have hyreg' : Nat.Coprime ℓ (orderOf y) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hyreg
  have hconst : ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character (u ^ j * y) =
        (basis.representation θ).character (u ^ j) := fun θ hθ =>
    prime_sylow_principal_section_constant basis ideal ℓ principal hprincipal P hP (hmemP j) hjne
      hyj hyreg hθ
  have hinvconj : IsConj (u ^ j) (u ^ (-j)) :=
    (zpow_isConj_zpow_iff hu hindex hj).mpr (Or.inr (by simp))
  have hθinv : ∀ θ : basis.index, (basis.representation θ).character (u ^ (-j)) =
      (basis.representation θ).character (u ^ j) := by
    intro θ
    obtain ⟨c, hc⟩ := isConj_iff.mp hinvconj
    rw [← hc]
    simp only [FiniteComplexRepresentation.character, Representation.char_conj]
  have hθconj : ∀ θ : basis.index, (basis.representation θ).character (u ^ (-j)) =
      starRingEnd ℂ ((basis.representation θ).character (u ^ j)) := by
    intro θ
    rw [finite_character_conjugate_inverse, zpow_neg]
  have hnorm := prime_order_sylow_principal_column_norm basis ideal ℓ principal hprincipal P hP
    (u ^ j) (hmemP j) hjne
  set x₁ : Subgroup.zpowers u := ⟨u ^ j, Subgroup.zpow_mem_zpowers u j⟩ with hx₁
  set x₂ : Subgroup.zpowers u := ⟨u ^ (-j), Subgroup.zpow_mem_zpowers u (-j)⟩ with hx₂
  have hx12 : x₁ ≠ x₂ := by
    intro heq
    have hval : u ^ j = u ^ (-j) := congrArg Subtype.val heq
    have h2 : u ^ (j - -j) = 1 := by rw [zpow_sub, hval, mul_inv_cancel]
    rw [hone, show j - -j = 2 * j by ring] at h2
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h3 | h3
    · have h4 : (ℓ : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h3
      have h5 := hp.two_le
      omega
    · exact hj h3
  have hx1inv : x₁⁻¹ = x₂ := Subtype.ext (by simp [hx₁, hx₂, zpow_neg])
  have hx2inv : x₂⁻¹ = x₁ := by rw [← hx1inv, inv_inv]
  have hS₁ : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character (x₁ : G) *
        (basis.representation θ).character (u ^ j * y) = ℓ := by
    rw [← hnorm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hconst θ hθ, ← hθconj, hθinv]
  have hS₂ : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation θ).character (x₂ : G) *
        (basis.representation θ).character (u ^ j * y) = ℓ := by
    rw [← hnorm]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    change (basis.representation θ).character (u ^ (-j)) * _ = _
    rw [hconst θ hθ, hθconj, mul_comm]
  rw [principalCyclicProjection_eq_sum, Fintype.sum_eq_add x₁ x₂ hx12, hS₁, hS₂, hx1inv, hx2inv,
    Nat.card_zpowers, hu]
  · have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp
    ring
  · rintro x ⟨hxne1, hxne2⟩
    apply mul_eq_zero_of_right
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have hnot : ¬ IsConj (u ^ k) (u ^ (-j)) := by
      intro hc
      rcases (zpow_isConj_zpow_iff hu hindex hnegj).mp hc.symm with h' | h'
      · apply hxne2
        apply Subtype.ext
        rw [← hk]
        change u ^ k = u ^ (-j)
        have h'' : u ^ (k - -j) = 1 := (hone _).mpr h'
        calc u ^ k = u ^ (k - -j) * u ^ (-j) := by rw [← zpow_add, sub_add_cancel]
          _ = u ^ (-j) := by rw [h'', one_mul]
      · apply hxne1
        apply Subtype.ext
        rw [← hk]
        change u ^ k = u ^ j
        have h'' : u ^ (k + -j) = 1 := (hone _).mpr h'
        calc u ^ k = u ^ (k + -j) * u ^ j := by rw [← zpow_add, neg_add_cancel_right]
          _ = u ^ j := by rw [h'', one_mul]
    have hkord : orderOf (u ^ k) ∣ ℓ ^ 1 := by
      rw [pow_one, ← hu]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers u k)
    have hjord : orderOf (u ^ (-j)) ∣ ℓ ^ 1 := by
      rw [pow_one, ← hu]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers u (-j))
    have horth := coefficientBlock_section_column_orthogonality basis ideal ℓ principal
      (u ^ k) (u ^ (-j)) 1 y⁻¹ 1 1 hkord hjord (by simp) (by rw [orderOf_inv]; exact hyreg')
      (Commute.one_right _) ((hy.zpow_left (-j)).inv_right) hnot
    have hrw : (u ^ (-j) * y⁻¹)⁻¹ = u ^ j * y := by
      rw [mul_inv_rev, inv_inv, zpow_neg, inv_inv]
      exact hyj.eq.symm
    rw [hrw, mul_one] at horth
    rw [← hk]
    exact horth

end Sections

end CFSG.Semidihedral.Principal
