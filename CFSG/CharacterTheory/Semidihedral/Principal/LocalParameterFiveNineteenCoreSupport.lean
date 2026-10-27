module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSeventeenSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.OrderFiveThreeGroupObstruction
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalOddQuaternionEigenspace

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem mem_oddCore_of_pow_prime {G : Type} [Group G] [Finite G] {t s₀ : G} {ℓ : ℕ}
    (h36 : 36 % ℓ = 1)
    (hD : Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀}) =
      12 * Nat.card (((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t)))
    {y : G} (hyC : y ∈ C t) (hys : y ∈ Subgroup.centralizer {s₀}) (hy : y ^ ℓ = 1) :
    (⟨y, hyC⟩ : C t) ∈ N t := by
  set Ds : Subgroup (C t) := (Subgroup.centralizer {s₀}).comap (C t).subtype with hDs
  set K : Subgroup Ds := (N t).subgroupOf Ds with hK
  have hcardDs : Nat.card Ds = Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀}) := by
    rw [← Subgroup.card_map_of_injective (K := Ds) (f := (C t).subtype)
      (C t).subtype_injective, hDs, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hcardK : Nat.card K = Nat.card (Ds.subgroupOf (N t)) := by
    rw [hK, ← Subgroup.card_map_of_injective (K := (N t).subgroupOf Ds) (f := Ds.subtype)
        Ds.subtype_injective, Subgroup.subgroupOf_map_subtype,
      ← Subgroup.card_map_of_injective (K := Ds.subgroupOf (N t)) (f := (N t).subtype)
        (N t).subtype_injective, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hindex : K.index = 12 := by
    have h := Subgroup.card_mul_index K
    rw [hcardDs, hD, ← hcardK] at h
    have h' : Nat.card K * K.index = Nat.card K * 12 := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have : K.Normal := Subgroup.Normal.subgroupOf inferInstance Ds
  let yD : Ds := ⟨⟨y, hyC⟩, by
    change y ∈ Subgroup.centralizer {s₀}
    exact hys⟩
  have hyD : yD ^ ℓ = 1 := Subtype.ext (Subtype.ext hy)
  have h12 : yD ^ 12 ∈ K := hindex ▸ Subgroup.pow_index_mem K yD
  have hyD' : yD = (yD ^ 12) ^ 3 := by
    rw [← pow_mul, pow_eq_pow_mod (12 * 3) hyD, show 12 * 3 = 36 by norm_num, h36, pow_one]
  have hmem : yD ∈ K := hyD' ▸ K.pow_mem h12 3
  exact hmem

theorem prime_not_dvd_card_oddCore_centralizer {G : Type} [Group G] [Fintype G] {n : ℕ}
    (hn : 4 ≤ n) {S : Subgroup G} (fS : SemidihedralGroup n ≃* S) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (h36 : 36 % ℓ = 1)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdeg : Module.finrank ℂ θ.vector < 4 * (ℓ - 1) + 5)
    (hrat : ∀ g, ∃ q : ℚ, θ.character g = q) (hfaith : Function.Injective θ.representation)
    (htval : θ.character t = -5) (hNval : ∀ y : C t, y ∈ N t → θ.character (t * y) = -5)
    (hD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      12 * Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
        (N t))) :
    ¬ ℓ ∣ Nat.card (((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf
      (N t)) := by
  intro hℓdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) with hV
  have : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  obtain ⟨-, ht2, -, hsC, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hℓdvd
  set u : G := (((x : N t) : C t) : G) with hu
  have hu17 : orderOf u = ℓ := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have huC : u ∈ C t := ((x : N t) : C t).property
  have hus : u ∈ Subgroup.centralizer {(fS (s n) : G)} := (Subgroup.mem_subgroupOf.mp x.property)
  set P : Subgroup G := Subgroup.zpowers u with hP
  have hPcard : Nat.card P = ℓ := by rw [hP, Nat.card_zpowers, hu17]
  have hPV : P ≤ Subgroup.centralizer V := by
    rw [hP, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    have hle : V ≤ Subgroup.centralizer {u} := by
      rw [hV]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hus).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))
  have hconst : ∀ v ∈ V, v ≠ 1 → ∀ z ∈ P, θ.representation.character (v * z) =
      θ.representation.character v := by
    intro v hv hv1 z hz
    obtain ⟨g, hg, hgv⟩ := hfus v hv hv1
    have hzV : z ∈ Subgroup.centralizer V := hPV hz
    have hyV : g * z * g⁻¹ ∈ Subgroup.centralizer V := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : g⁻¹ * w * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hzV _ hw'
      calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
        _ = g * z * g⁻¹ * w := by group
    have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hsV : (fS (s n) : G) ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyC : g * z * g⁻¹ ∈ C t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV t htV).symm
    have hys : g * z * g⁻¹ ∈ Subgroup.centralizer {(fS (s n) : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV _ hsV).symm
    have hz17 : z ^ ℓ = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu17,
        pow_orderOf_eq_one, one_zpow]
    have hy17 : (g * z * g⁻¹) ^ ℓ = 1 := by rw [conj_pow, hz17]; group
    have hyN := mem_oddCore_of_pow_prime h36 hD hyC hys hy17
    have hval := hNval ⟨g * z * g⁻¹, hyC⟩ hyN
    have hconj : θ.representation.character (v * z) =
        θ.representation.character (g * (v * z) * g⁻¹) :=
      (Representation.char_conj θ.representation (v * z) g).symm
    rw [hconj, show g * (v * z) * g⁻¹ = (g * v * g⁻¹) * (g * z * g⁻¹) by group, hgv]
    have hconjv : θ.representation.character v =
        θ.representation.character (g * v * g⁻¹) :=
      (Representation.char_conj θ.representation v g).symm
    rw [hconjv, hgv]
    exact hval.trans htval.symm
  have hker : ¬ P ≤ MonoidHom.ker θ.representation := by
    intro hle
    have huker : u ∈ MonoidHom.ker θ.representation := hle (Subgroup.mem_zpowers u)
    have hu1 : u = 1 := hfaith ((MonoidHom.mem_ker.mp huker).trans (map_one _).symm)
    rw [hu1, orderOf_one] at hu17
    exact hℓ.one_lt.ne hu17
  obtain ⟨-, hbound⟩ := four_group_central_prime_coset_constant_degree_bound θ.representation V
    P hPV hℓ hℓodd hPcard
    (fun z _ => hrat z) hker hconst
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have h := hbound t htV ht1
  rw [show θ.representation.character t = -5 from htval] at h
  have hnorm : ‖(-5 : ℂ)‖ = 5 := by norm_num
  rw [hnorm] at h
  have hdeg' : (Module.finrank ℂ θ.vector : ℝ) < ((4 * (ℓ - 1) : ℕ) : ℝ) + 5 := by
    exact_mod_cast hdeg
  linarith

theorem pow_gcd_conj_eq_of_normalizes {G : Type*} [Group G] {u h : G} {ℓ m : ℕ}
    (hℓ : ℓ.Prime) (hu : orderOf u = ℓ) (hnorm : h * u * h⁻¹ ∈ Subgroup.zpowers u)
    (hm : h ^ m = 1) :
    h ^ (Nat.gcd m (ℓ - 1)) * u * (h ^ (Nat.gcd m (ℓ - 1)))⁻¹ = u := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have huℓ : u ^ ℓ = 1 := hu ▸ pow_orderOf_eq_one u
  obtain ⟨k, hk⟩ : ∃ k : ℕ, h * u * h⁻¹ = u ^ k := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hnorm
    refine ⟨(i % ℓ).toNat, ?_⟩
    rw [← hi, zpow_eq_zpow_emod' i huℓ, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hℓ.ne_zero))]
  have hpow : ∀ j : ℕ, h ^ j * u * (h ^ j)⁻¹ = u ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc h ^ (j + 1) * u * (h ^ (j + 1))⁻¹ = h * (h ^ j * u * (h ^ j)⁻¹) * h⁻¹ := by group
        _ = h * u ^ (k ^ j) * h⁻¹ := by rw [ih]
        _ = (h * u * h⁻¹) ^ (k ^ j) := by rw [conj_pow]
        _ = u ^ (k ^ (j + 1)) := by rw [hk, ← pow_mul, pow_succ', mul_comm]
  have hmod : ∀ a : ℕ, u ^ a = u ↔ (a : ZMod ℓ) = 1 := by
    intro a
    rw [show u ^ a = u ↔ u ^ a = u ^ 1 by rw [pow_one], pow_eq_pow_iff_modEq, hu,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  have hk0 : (k : ZMod ℓ) ≠ 0 := by
    intro h0
    obtain ⟨c, rfl⟩ := (ZMod.natCast_eq_zero_iff k ℓ).mp h0
    have h1 : h * u * h⁻¹ = 1 := by rw [hk, pow_mul, huℓ, one_pow]
    have : u = 1 := by
      have := congrArg (fun x => h⁻¹ * x * h) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hu
    exact hℓ.one_lt.ne hu
  have hkm : (k : ZMod ℓ) ^ m = 1 := by
    rw [← Nat.cast_pow, ← hmod, ← hpow, hm]
    group
  have hkℓ : (k : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
  rw [hpow, hmod, Nat.cast_pow]
  exact pow_gcd_eq_one.mpr ⟨hkm, hkℓ⟩

theorem le_of_le_sup_of_odd {C : Type*} [Group C] [Finite C] (K M Q : Subgroup C) [K.Normal]
    (hQ : Q ≤ K ⊔ M) (hQ2 : IsPGroup 2 Q) (hM : Odd (Nat.card M)) : Q ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq
  obtain ⟨k, hk, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hQ hq)
  have hmk : (QuotientGroup.mk' K (k * m)) = QuotientGroup.mk' K m := by
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [map_mul, hk1, one_mul]
  have h1 : orderOf (QuotientGroup.mk' K (k * m)) ∣ orderOf (k * m) := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' K (k * m)) ∣ Nat.card M := by
    rw [hmk]
    refine (orderOf_map_dvd _ _).trans ?_
    have := orderOf_dvd_natCard (⟨m, hm⟩ : M)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨k * m, hq⟩
  rw [Subgroup.orderOf_mk] at ha
  rw [ha] at h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hb0 : b = 0 := by
    by_contra hb0
    have h2' : 2 ∣ Nat.card M := by
      rw [hb] at h2
      exact (dvd_pow_self 2 hb0).trans h2
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h2')
  rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
  exact (QuotientGroup.eq_one_iff (k * m)).mp hb

theorem exists_normal_central_order_three {C : Type*} [Group C] (M T : Subgroup C) [M.Normal]
    (hT : ∀ x ∈ T, ∀ z ∈ M, (∀ m ∈ M, z * m = m * z) → x * z * x⁻¹ = z) (g : C) (hg : g ^ 2 ∈ T)
    (hcov : ∀ c : C, c ∈ T ∨ g⁻¹ * c ∈ T) {e : C} (heM : e ∈ M) (heZ : ∀ m ∈ M, e * m = m * e)
    (he3 : orderOf e = 3) :
    ∃ p : C, p ∈ M ∧ (∀ m ∈ M, p * m = m * p) ∧ orderOf p = 3 ∧
      ∀ c : C, ∀ x ∈ Subgroup.zpowers p, c * x * c⁻¹ ∈ Subgroup.zpowers p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' := g * e * g⁻¹ with he'
  have he'M : e' ∈ M := (inferInstance : M.Normal).conj_mem e heM g
  have he'Z : ∀ m ∈ M, e' * m = m * e' := by
    intro m hm
    have hm' : g⁻¹ * m * g ∈ M := by
      simpa using (inferInstance : M.Normal).conj_mem m hm g⁻¹
    have h := heZ (g⁻¹ * m * g) hm'
    calc e' * m = g * (e * (g⁻¹ * m * g)) * g⁻¹ := by rw [he']; group
      _ = g * ((g⁻¹ * m * g) * e) * g⁻¹ := by rw [h]
      _ = m * e' := by rw [he']; group
  have hcomm : e * e' = e' * e := heZ e' he'M
  have he3' : e ^ 3 = 1 := he3 ▸ pow_orderOf_eq_one e
  have hg2 : g * e' * g⁻¹ = e := by
    have h := hT _ hg e heM heZ
    rw [he']
    calc g * (g * e * g⁻¹) * g⁻¹ = g ^ 2 * e * (g ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = e := h
  have hconjpow : ∀ (c p : C) (x : C), x ∈ Subgroup.zpowers p →
      (∃ q ∈ Subgroup.zpowers p, c * p * c⁻¹ = q) → c * x * c⁻¹ ∈ Subgroup.zpowers p := by
    rintro c p x hx ⟨q, hq, hcp⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hcp]
    exact Subgroup.zpow_mem _ hq k
  by_cases hne : e * e' = 1
  ·
    have hginv : g * e * g⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right hne
    refine ⟨e, heM, heZ, he3, fun c x hx => ?_⟩
    apply hconjpow c e x hx
    rcases hcov c with hc | hc
    · exact ⟨e, Subgroup.mem_zpowers e, hT c hc e heM heZ⟩
    · refine ⟨e⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers e), ?_⟩
      have h := hT _ hc e heM heZ
      calc c * e * c⁻¹ = g * ((g⁻¹ * c) * e * (g⁻¹ * c)⁻¹) * g⁻¹ := by group
        _ = g * e * g⁻¹ := by rw [h]
        _ = e⁻¹ := hginv
  ·
    set p := e * e' with hp
    have hpM : p ∈ M := M.mul_mem heM he'M
    have hpZ : ∀ m ∈ M, p * m = m * p := by
      intro m hm
      rw [hp, mul_assoc, he'Z m hm, ← mul_assoc, heZ m hm, mul_assoc]
    have hp3 : orderOf p = 3 := by
      apply orderOf_eq_prime
      · rw [hp, (Commute.mul_pow hcomm), he3', he', conj_pow, he3']
        group
      · exact hne
    have hgp : g * p * g⁻¹ = p := by
      calc g * p * g⁻¹ = (g * e * g⁻¹) * (g * e' * g⁻¹) := by rw [hp]; group
        _ = e' * e := by rw [← he', hg2]
        _ = p := hcomm.symm
    refine ⟨p, hpM, hpZ, hp3, fun c x hx => ?_⟩
    apply hconjpow c p x hx
    refine ⟨p, Subgroup.mem_zpowers p, ?_⟩
    rcases hcov c with hc | hc
    · exact hT c hc p hpM hpZ
    · have h := hT _ hc p hpM hpZ
      calc c * p * c⁻¹ = g * ((g⁻¹ * c) * p * (g⁻¹ * c)⁻¹) * g⁻¹ := by group
        _ = g * p * g⁻¹ := by rw [h]
        _ = p := hgp

theorem eq_tInC_of_mem_K_of_orderOf_eq_two {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0) (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t : G) (ht : orderOf t = 2) {v : C t} (hv : v ∈ K t) (hv2 : orderOf v = 2) :
    v = tInC t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, huniq, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hNodd : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hoddN : ∀ w ∈ N t, w ^ 2 = 1 → w = 1 := by
    intro w hw hw2
    have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    have h2 : orderOf w ∣ Nat.card (N t) := by
      have := orderOf_dvd_natCard (⟨w, hw⟩ : N t)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : orderOf w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hNodd)
    exact orderOf_eq_one_iff.mp h3
  have hmem : nu t v ∈ (J t).comap (barKappa t) := by
    rw [Subgroup.mem_comap, barKappa_nu]
    exact Subgroup.mem_map_of_mem _ hv
  have hνv : orderOf (nu t v) = 2 := by
    have hdvd : orderOf (nu t v) ∣ 2 := by
      have := orderOf_map_dvd (nu t) v
      rwa [hv2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have hv1 : nu t v = 1 := orderOf_eq_one_iff.mp h
      have hvN : v ∈ N t := (QuotientGroup.eq_one_iff v).mp hv1
      have hvsq : v ^ 2 = 1 := hv2 ▸ pow_orderOf_eq_one v
      rw [hoddN v hvN hvsq, orderOf_one] at hv2
      norm_num at hv2
    · exact h
  have h := huniq ⟨nu t v, hmem⟩ (by rw [Subgroup.orderOf_mk]; exact hνv)
  change nu t v = nu t (tInC t) at h
  have hw : v⁻¹ * tInC t ∈ N t := QuotientGroup.eq.mp h
  have htc : Commute v (tInC t) := (Subgroup.mem_center_iff.mp (tInC_central t) v)
  have hvsq : v ^ 2 = 1 := hv2 ▸ pow_orderOf_eq_one v
  have htsq : tInC t ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at *
    have : orderOf (tInC t) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ht
    exact this ▸ pow_orderOf_eq_one (tInC t)
  have hw2 : (v⁻¹ * tInC t) ^ 2 = 1 := by
    rw [(htc.inv_left).mul_pow, inv_pow, hvsq, htsq, inv_one, one_mul]
  have := hoddN _ hw hw2
  rw [inv_mul_eq_one] at this
  exact this

theorem generalizedFitting_eq_J_of_field_group_trivial {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hfodd : ∀ a : ℕ, Odd a → a ∣ f → a = 1) :
    CFSG.generalizedFitting (Gamma t) = J t := by
  obtain ⟨-, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t :=
    simple_le_index_two _ _ hJindex hnonab
  obtain ⟨F, hF, hFfin, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S0 f0 hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨-, -, -, hquot⟩ := data.compatible_layer
  have hA : Nat.card A = 1 := hfodd _ data.field_group_odd data.field_group_dvd
  rw [hA] at hquot
  apply le_antisymm hLJ
  intro x hx
  obtain ⟨y, rfl⟩ := barKappa_surjective t x
  have hyJ : y ∈ (J t).comap (barKappa t) := hx
  have htop : ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).subgroupOf
      ((J t).comap (barKappa t)) = ⊤ := by
    have h1 : Nat.card ((((J t).comap (barKappa t)) ⧸
        ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).subgroupOf
          ((J t).comap (barKappa t)))) = 1 := hquot
    rw [← Subgroup.index_eq_card, Subgroup.index_eq_one] at h1
    exact h1
  have hy : (⟨y, hyJ⟩ : (J t).comap (barKappa t)) ∈
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).subgroupOf
        ((J t).comap (barKappa t)) := htop ▸ Subgroup.mem_top _
  exact hy

theorem mem_zpowers_of_unique_involution {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {t : G} (huniq : ∀ v ∈ Q, orderOf v = 2 → v = t) {u : G} (hu : u ∈ Q)
    (hu1 : u ≠ 1) : t ∈ Subgroup.zpowers u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hb
    exact hu1 hb
  have h2 : 2 ∣ orderOf u := by
    rw [hb]
    exact dvd_pow_self 2 hb0
  have hw : orderOf (u ^ (orderOf u / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' h2
  have := huniq _ (Q.pow_mem hu _) hw
  rw [← this]
  exact Subgroup.npow_mem_zpowers u _

theorem eq_of_mem_zpowers_sq_of_orderOf_eq_two {G : Type*} [Group G] {r v : G}
    (hr : orderOf r = 8) (hv : v ∈ Subgroup.zpowers (r ^ 2)) (hv2 : orderOf v = 2) :
    v = r ^ 4 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hr8 : r ^ 8 = 1 := hr ▸ pow_orderOf_eq_one r
  have hsq : ((r ^ 2) ^ k) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((r ^ 2) ^ k)
    rwa [hv2] at this
  have hne : (r ^ 2) ^ k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv2
    norm_num at hv2
  have hk : (r ^ 2) ^ k = (r ^ 2) ^ (k % 4) := by
    have h4 : (r ^ 2) ^ (4 : ℕ) = 1 := by rw [← pow_mul, hr8]
    exact zpow_eq_zpow_emod' k h4
  rw [hk] at hsq hne ⊢
  have hmod : 0 ≤ k % 4 ∧ k % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _
    (by norm_num)⟩
  obtain ⟨hm0, hm4⟩ := hmod
  interval_cases (k % 4)
  · simp at hne
  · exfalso
    apply hne
    have : ((r ^ 2) ^ (1 : ℤ)) ^ 2 = r ^ 4 := by
      rw [zpow_one, ← pow_mul]
    rw [this] at hsq
    have h4 : orderOf r ∣ 4 := orderOf_dvd_of_pow_eq_one hsq
    rw [hr] at h4
    norm_num at h4
  · rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_mul]
  · exfalso
    have : ((r ^ 2) ^ (3 : ℤ)) ^ 2 = r ^ 4 := by
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_mul, ← pow_mul,
        show 2 * 3 * 2 = 8 + 4 by norm_num, pow_add, hr8, one_mul]
    rw [this] at hsq
    have h4 : orderOf r ∣ 4 := orderOf_dvd_of_pow_eq_one hsq
    rw [hr] at h4
    norm_num at h4

theorem not_seven_dvd_card_oddCore {G : Type} [Group G] [Fintype G] {S : Sylow 2 G}
    (fS : SemidihedralGroup 4 ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r 4) : G) ^ 2 ^ (4 - 2))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hrat : ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q)
    (hfaith : Function.Injective (basis.representation χ).representation)
    (htval : (basis.representation χ).character t = -5)
    (hdeg : Module.finrank ℂ (basis.representation χ).vector = 19)
    (h7 : ∀ P : Sylow 7 (N t), Nat.card P ∣ 7)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (N t) → p = 3 ∨ p = 7)
    (h3 : ∀ P : Sylow 3 (N t), Nat.card P ∣ 81) :
    ¬ 7 ∣ Nat.card (N t) := by
  intro h7dvd
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts (by norm_num : 4 ≤ 4) fS ht
  obtain ⟨P₇⟩ : Nonempty (Sylow 7 (N t)) := inferInstance
  have hNpos : Nat.card (N t) ≠ 0 := Nat.card_pos.ne'
  have hP7card : Nat.card P₇ = 7 := by
    have hc := Sylow.card_eq_multiplicity P₇
    have hpos : 1 ≤ (Nat.card (N t)).factorization 7 :=
      (Nat.Prime.factorization_pos_of_dvd (by norm_num) hNpos h7dvd)
    have hle : (Nat.card (N t)).factorization 7 ≤ 1 := by
      have h := h7 P₇
      rw [hc] at h
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 7)).mp (by rw [pow_one]; exact h)
    rw [hc, show (Nat.card (N t)).factorization 7 = 1 by omega, pow_one]
  have hidx : Nat.card P₇ * (P₇ : Subgroup (N t)).index = Nat.card (N t) :=
    Subgroup.card_mul_index _
  have hidx0 : (P₇ : Subgroup (N t)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx3 : (P₇ : Subgroup (N t)).index =
      3 ^ (P₇ : Subgroup (N t)).index.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hidx0
    intro d hd hdd
    have hdN : d ∣ Nat.card (N t) := hdd.trans (Dvd.intro_left _ hidx)
    rcases hprimes d hd hdN with h | h
    · exact h
    · exfalso
      subst h
      have h49 : 7 ^ 2 ∣ Nat.card (N t) := by
        rw [← hidx, hP7card, pow_two]
        exact mul_dvd_mul_left 7 hdd
      have hc := Sylow.card_eq_multiplicity P₇
      rw [hP7card] at hc
      have hle : 2 ≤ (Nat.card (N t)).factorization 7 :=
        (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hNpos).mp h49
      have : (7 : ℕ) ^ 2 ≤ 7 ^ (Nat.card (N t)).factorization 7 := Nat.pow_le_pow_right
        (by norm_num) hle
      rw [← hc] at this
      norm_num at this
  have hn7 : Nat.card (Sylow 7 (N t)) = 1 := by
    have hmod := card_sylow_modEq_one 7 (N t)
    have hdvd := Sylow.card_dvd_index P₇
    rw [hidx3] at hdvd
    obtain ⟨i, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    obtain ⟨P₃⟩ : Nonempty (Sylow 3 (N t)) := inferInstance
    have h3i : 3 ^ i ∣ Nat.card (N t) := by
      rw [← hn]
      exact (Sylow.card_dvd_index P₇).trans (Dvd.intro_left _ hidx)
    have h3fac : 3 ^ i ∣ 3 ^ (Nat.card (N t)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hNpos).mp h3i |>
        Nat.pow_dvd_pow 3
    have h81 : 3 ^ i ∣ 81 := by
      have := h3 P₃
      rw [Sylow.card_eq_multiplicity] at this
      exact h3fac.trans this
    have hi4 : i ≤ 4 := by
      have := Nat.le_of_dvd (by norm_num) h81
      by_contra hi
      push Not at hi
      have : 3 ^ 5 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      omega
    rw [hn] at hmod
    have hi0 : i = 0 := by
      interval_cases i <;> first | rfl | (simp only [Nat.ModEq] at hmod; norm_num at hmod)
    rw [hn, hi0, pow_zero]
  have hsub : Subsingleton (Sylow 7 (N t)) := (Nat.card_eq_one_iff_unique.mp hn7).1
  have hnormC : ∀ c : C t, ∀ x ∈ (P₇ : Subgroup (N t)),
      (MulAut.conjNormal (H := N t) c) x ∈ (P₇ : Subgroup (N t)) := by
    intro c x hx
    have h : (MulAut.conjNormal (H := N t) c) • P₇ = P₇ := Subsingleton.elim _ _
    have hmem : (MulAut.conjNormal (H := N t) c) • x ∈
        (((MulAut.conjNormal (H := N t) c) • P₇ : Sylow 7 (N t)) : Subgroup (N t)) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
    rw [h] at hmem
    exact hmem
  obtain ⟨g₇, hg₇P, hg₇1⟩ : ∃ g ∈ (P₇ : Subgroup (N t)), g ≠ 1 := by
    by_contra! hall
    have hbot : (P₇ : Subgroup (N t)) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [hbot, Subgroup.card_bot] at hP7card
    norm_num at hP7card
  have hg₇ord : orderOf g₇ = 7 := orderOf_eq_prime_of_mem_of_card_eq hP7card hg₇P hg₇1
  have hPeq : (P₇ : Subgroup (N t)) = Subgroup.zpowers g₇ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact hg₇P
    · rw [hP7card, Nat.card_zpowers, hg₇ord]
  set u : G := ((g₇ : C t) : G) with hu
  have hu7 : orderOf u = 7 := by rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg₇ord]
  set P : Subgroup G := Subgroup.zpowers u with hP
  have hPcard : Nat.card P = 7 := by rw [hP, Nat.card_zpowers, hu7]
  have huC : u ∈ C t := (g₇ : C t).property
  have hPnormal : P ≤ C t ∧ ∀ c ∈ C t, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    refine ⟨by rw [hP, Subgroup.zpowers_le]; exact huC, ?_⟩
    intro c hc x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    apply Subgroup.zpow_mem
    have h := hnormC ⟨c, hc⟩ g₇ hg₇P
    rw [hPeq] at h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have h' := congrArg (fun y : N t => ((y : C t) : G)) hm
    simp only [Subgroup.coe_zpow, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h'
    exact h'
  set rr : G := (fS (r 4) : G) with hrr
  have hrr8 : orderOf rr = 8 := by
    rw [hrr, supplied_orderOf_r (by norm_num) fS]
    rfl
  have htrr : t = rr ^ 4 := by rw [ht]; norm_num
  have hrrC : rr ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, htrr]
    exact (((Commute.refl rr).pow_left 4).eq).symm
  have hnorm : rr * u * rr⁻¹ ∈ Subgroup.zpowers u := hPnormal.2 rr hrrC u (Subgroup.mem_zpowers u)
  have hcomm := pow_gcd_conj_eq_of_normalizes (by norm_num : Nat.Prime 7) hu7 hnorm
    (m := 8) (by rw [← hrr8, pow_orderOf_eq_one])
  rw [show Nat.gcd 8 (7 - 1) = 2 by norm_num] at hcomm
  set Q : Subgroup G := Subgroup.zpowers (rr ^ 2) with hQ
  have hQcard : Nat.card Q = 4 := by
    rw [hQ, Nat.card_zpowers, orderOf_pow' rr (by norm_num), hrr8]
    norm_num
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 2) (by rw [hQcard]; norm_num)
  have htQ : t ∈ Q := by
    rw [htrr, show rr ^ 4 = (rr ^ 2) ^ 2 by rw [← pow_mul]]
    exact Subgroup.npow_mem_zpowers _ _
  have hQt : ∀ x ∈ Q, x ≠ 1 → t ∈ Subgroup.zpowers x := fun x hx hx1 =>
    mem_zpowers_of_unique_involution hQ2
      (fun v hv hv2 => htrr ▸ eq_of_mem_zpowers_sq_of_orderOf_eq_two hrr8 hv hv2) hx hx1
  have hQle : Q ≤ C t ∧ Q ≤ Subgroup.centralizer P := by
    refine ⟨by rw [hQ, Subgroup.zpowers_le]; exact Subgroup.pow_mem _ hrrC 2, ?_⟩
    rw [hQ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute (rr ^ 2) u := by
      have : rr ^ 2 * u = u * rr ^ 2 := by
        calc rr ^ 2 * u = rr ^ 2 * u * (rr ^ 2)⁻¹ * rr ^ 2 := by group
          _ = u * rr ^ 2 := by rw [hcomm]
      exact this
    exact ((hc.zpow_right k).eq).symm
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu7
    norm_num at hu7
  have hker : ∃ x ∈ P, (basis.representation χ).character x ≠
      (basis.representation χ).character 1 := by
    refine ⟨u, Subgroup.mem_zpowers u, character_ne_one_of_not_mem_ker _ ?_⟩
    intro huk
    exact hu1 (hfaith ((MonoidHom.mem_ker.mp huk).trans (map_one _).symm))
  obtain ⟨hbound, -⟩ := normal_odd_prime_principal_quaternion_eigenspace_bound basis ideal
    principal hprincipal hχ (basis.representation χ).representation rfl ht2 P hPnormal
    (by norm_num : Nat.Prime 7) (by decide) hPcard Q hQle hQ2 htQ hQt (fun x _ => hrat x) hker
  rw [hQcard, show (basis.representation χ).representation.character t = -5 from htval,
    hdeg] at hbound
  norm_num at hbound

theorem oddCore_eq_bot_of_isPGroup_three {G : Type} [Group G] [Fintype G] (S : Sylow 2 G)
    (fS : SemidihedralGroup 4 ≃* (S : Subgroup G)) (hG : ∀ U : Subgroup G, U.index ≠ 2) {t : G}
    (ht : t = (fS (r 4) : G) ^ 2 ^ (4 - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hrat : ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q)
    (hfaith : Function.Injective (basis.representation χ).representation)
    (htval : (basis.representation χ).character t = -5)
    (hdeg : Module.finrank ℂ (basis.representation χ).vector = 19)
    (τ : FiniteComplexRepresentation.{0, 0} (N t))
    (hτfaith : Function.Injective τ.representation) (hτrat : ∀ x, ∃ q : ℚ, τ.character x = q)
    (hτdeg : Module.finrank ℂ τ.vector = 7)
    (hτinv : ∀ (c : C t) (x : N t),
      τ.character ((MulAut.conjNormal (H := N t) c) x) = τ.character x)
    (hN3 : IsPGroup 3 (N t)) (hN81 : Nat.card (N t) ≤ 81) (h5C : 5 ∣ Nat.card (C t)) :
    N t = ⊥ := by
  by_contra hN1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts (by norm_num : 4 ≤ 4) fS ht
  have hNodd : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hcent5 : ∀ c : C t, orderOf c = 5 → ∀ x : N t, c * (x : C t) * c⁻¹ = x := by
    intro c hc x
    have hα : (MulAut.conjNormal (H := N t) c) ^ 5 = 1 := by
      rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    have h := order_five_automorphism_small_three_group_rational_character_obstruction hN3 hN81
      _ hα τ hτfaith hτrat (by rw [hτdeg]; norm_num) (hτinv c)
    have h' := congrArg (fun α : MulAut (N t) => ((α x : N t) : C t)) h
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using h'
  set K' : Subgroup (C t) := Subgroup.centralizer (N t : Set (C t)) with hK'
  have hK'n : K'.Normal := Subgroup.normal_centralizer
  obtain ⟨c₅, hc₅⟩ := exists_prime_orderOf_dvd_card' 5 h5C
  have hc₅K' : c₅ ∈ K' := by
    rw [hK', Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hcent5 c₅ hc₅ ⟨x, hx⟩
    calc x * c₅ = c₅ * x * c₅⁻¹ * c₅ := by rw [h]
      _ = c₅ * x := by group
  have hLJ := generalizedFitting_eq_J_of_field_group_trivial 4 (by norm_num) S fS hG t ht2
    hnonab hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel
    (fun a _ ha => Nat.dvd_one.mp ha)
  obtain ⟨hNZK, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs 4 (by norm_num) S fS hG t ht2
  have hc₅K : c₅ ∈ K t := by
    rw [K_eq_odd_order_closure]
    exact Subgroup.subset_closure (show Odd (orderOf c₅) by rw [hc₅]; decide)
  have hκL : kappa t c₅ ∈ CFSG.generalizedFitting (Gamma t) := by
    rw [hLJ]
    exact Subgroup.mem_map_of_mem _ hc₅K
  have hκ1 : kappa t c₅ ≠ 1 := by
    intro h1
    have hmem : c₅ ∈ NZ t := (QuotientGroup.eq_one_iff c₅).mp h1
    obtain ⟨m, hm, z, hz, hmz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hz2 : z * z = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have htt : tInC t ^ 2 = 1 := by
        have : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
        exact this ▸ pow_orderOf_eq_one (tInC t)
      rw [← zpow_add, ← two_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast,
        htt, one_zpow]
    have hzc : ∀ y : C t, z * y = y * z := by
      intro y
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc : Commute (tInC t) y := (Subgroup.mem_center_iff.mp (tInC_central t) y).symm
      exact (hc.zpow_left k).eq
    have hsq : c₅ ^ 2 = m ^ 2 := by
      rw [← hmz, pow_two, pow_two]
      calc m * z * (m * z) = m * (z * m) * z := by group
        _ = m * (m * z) * z := by rw [hzc m]
        _ = m * m * (z * z) := by group
        _ = m * m := by rw [hz2, mul_one]
    have hc₅N : c₅ ∈ N t := by
      have h6 : c₅ = (c₅ ^ 2) ^ 3 := by
        rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, ← hc₅, pow_orderOf_eq_one,
          one_mul, pow_one]
      rw [h6, hsq]
      exact (N t).pow_mem ((N t).pow_mem hm 2) 3
    have hdvd : orderOf c₅ ∣ Nat.card (N t) := by
      have := orderOf_dvd_natCard (⟨c₅, hc₅N⟩ : N t)
      rwa [Subgroup.orderOf_mk] at this
    rw [hc₅] at hdvd
    obtain ⟨k, hk⟩ := hN3.exists_card_eq
    rw [hk] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_three).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd))
    norm_num at this
  have hLM : CFSG.generalizedFitting (Gamma t) ≤ K'.map (kappa t) := by
    have hMn : (K'.map (kappa t)).Normal := hK'n.map _ (QuotientGroup.mk'_surjective _)
    have hsub : ((K'.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t))).Normal :=
      hMn.subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K'.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t))) with h | h
    · exfalso
      have hmem : (⟨kappa t c₅, hκL⟩ : CFSG.generalizedFitting (Gamma t)) ∈
          (K'.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t)) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hc₅K')
      rw [h, Subgroup.mem_bot] at hmem
      exact hκ1 (congrArg Subtype.val hmem)
    · intro x hx
      have hmem : (⟨x, hx⟩ : CFSG.generalizedFitting (Gamma t)) ∈
          (K'.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t)) :=
        h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
  have hKcomap : K t = (J t).comap (kappa t) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact (sup_eq_left.mpr hNZK).symm
  have hKle : K t ≤ K' ⊔ N t := by
    intro x hx
    rw [hKcomap, ← hLJ] at hx
    have hx' := hLM hx
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
    have hZK' : Z t ≤ K' := by
      rw [Subgroup.zpowers_le, hK', Subgroup.mem_centralizer_iff]
      intro y _
      exact (Subgroup.mem_center_iff.mp (tInC_central t) y)
    have hNZ : NZ t ≤ K' ⊔ N t := sup_le (le_sup_right) (hZK'.trans le_sup_left)
    exact (sup_le le_sup_left hNZ) hx'
  have hSC : (S : Subgroup G) ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : (fS (z 4) : G) = t := (supplied_t_s_facts (by norm_num : 4 ≤ 4) fS ht).1
    rw [← hz]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center 4 (by norm_num)))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : (S : Subgroup G)) : G)) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
    exact h'
  set SC : Subgroup (C t) := (S : Subgroup G).subgroupOf (C t) with hSCdef
  have hcard_subgroupOf : ∀ H K : Subgroup (C t), Nat.card (H.subgroupOf K) = Nat.card ↥(H ⊓ K) :=
    fun H K => by
      rw [← Subgroup.card_map_of_injective (K := H.subgroupOf K) (f := K.subtype)
        K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hSCcard : Nat.card SC = 16 := by
    have h1 : Nat.card SC = Nat.card (S : Subgroup G) := by
      rw [hSCdef, ← Subgroup.card_map_of_injective (K := (S : Subgroup G).subgroupOf (C t))
        (f := (C t).subtype) (C t).subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hSC]
    rw [h1, ← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
    norm_num
  have hKidx : (K t).index = 2 := by
    rw [hKcomap, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hJindex]
  set Q : Subgroup (C t) := SC ⊓ K t with hQdef
  have hQcard : 8 ≤ Nat.card Q := by
    have hrel := Subgroup.relIndex_dvd_index_of_normal (K t) SC
    rw [hKidx] at hrel
    have hmul := Subgroup.card_mul_index ((K t).subgroupOf SC)
    rw [hSCcard, hcard_subgroupOf, inf_comm] at hmul
    have hle : ((K t).subgroupOf SC).index ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
    have hpos : 0 < ((K t).subgroupOf SC).index := Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite
    change 8 ≤ Nat.card ↥(SC ⊓ K t)
    nlinarith
  have hSC2 : IsPGroup 2 SC := by
    apply IsPGroup.of_card (n := 4)
    rw [hSCcard]
    norm_num
  have hQ2 : IsPGroup 2 Q := hSC2.to_le inf_le_left
  have hQK' : Q ≤ K' := le_of_le_sup_of_odd K' (N t) Q (inf_le_right.trans hKle) hQ2 hNodd
  have huniqQ : ∀ v ∈ Q, orderOf v = 2 → v = tInC t := fun v hv hv2 =>
    eq_tInC_of_mem_K_of_orderOf_eq_two 4 (by norm_num) S fS hG t ht2 (Subgroup.mem_inf.mp hv).2
      hv2
  have htQ : tInC t ∈ Q := by
    refine ⟨?_, hNZK (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩
    change (tInC t : G) ∈ (S : Subgroup G)
    change t ∈ (S : Subgroup G)
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r 4)).property _
  set s₀ : C t := ⟨(fS (s 4) : G), hsC⟩ with hs₀
  have hs₀2 : orderOf s₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hs₀K : s₀ ∉ K t := by
    intro h
    have := eq_tInC_of_mem_K_of_orderOf_eq_two 4 (by norm_num) S fS hG t ht2 h hs₀2
    exact hst (congrArg Subtype.val this)
  have : Nontrivial (N t) := (Subgroup.nontrivial_iff_ne_bot _).mpr hN1
  have hZnt : Nontrivial (Subgroup.center (N t)) := hN3.center_nontrivial
  have hZ3 : IsPGroup 3 (Subgroup.center (N t)) := hN3.to_subgroup _
  obtain ⟨kz, hkz⟩ := hZ3.exists_card_eq
  have hkz0 : kz ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkz
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hkz
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [hkz]; exact dvd_pow_self 3 hkz0 : 3 ∣ Nat.card (Subgroup.center (N t)))
  set e : C t := ((zc : N t) : C t) with he
  have heN : e ∈ N t := (zc : N t).property
  have heZ : ∀ m ∈ N t, e * m = m * e := by
    intro m hm
    have h := Subgroup.mem_center_iff.mp zc.property ⟨m, hm⟩
    have h' := congrArg (fun y : N t => (y : C t)) h
    exact h'.symm
  have he3 : orderOf e = 3 := by
    rw [he, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hT : ∀ x ∈ K' ⊔ N t, ∀ z ∈ N t, (∀ m ∈ N t, z * m = m * z) → x * z * x⁻¹ = z := by
    intro x hx z hz hzZ
    obtain ⟨k, hk, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hk z hz).symm
    have hmz : m * z = z * m := (hzZ m hm).symm
    calc k * m * z * (k * m)⁻¹ = k * (m * z) * m⁻¹ * k⁻¹ := by group
      _ = k * (z * m) * m⁻¹ * k⁻¹ := by rw [hmz]
      _ = (k * z) * k⁻¹ := by group
      _ = z := by rw [hkz]; group
  have hs₀sq : s₀ ^ 2 ∈ K' ⊔ N t := by
    rw [← hs₀2, pow_orderOf_eq_one]
    exact Subgroup.one_mem _
  have hcov : ∀ c : C t, c ∈ K' ⊔ N t ∨ s₀⁻¹ * c ∈ K' ⊔ N t := by
    intro c
    by_cases hc : c ∈ K t
    · exact Or.inl (hKle hc)
    · right
      apply hKle
      rw [Subgroup.mul_mem_iff_of_index_two hKidx]
      exact iff_of_false (fun h => hs₀K (by simpa using (K t).inv_mem h)) hc
  obtain ⟨pp, hppN, hppZ, hpp3, hppnorm⟩ := exists_normal_central_order_three (N t) (K' ⊔ N t)
    hT s₀ hs₀sq hcov heN heZ he3
  set P : Subgroup G := Subgroup.zpowers (pp : G) with hP
  have hPcard : Nat.card P = 3 := by
    rw [hP, Nat.card_zpowers, Subgroup.orderOf_coe, hpp3]
  have hPnormal : P ≤ C t ∧ ∀ c ∈ C t, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    refine ⟨by rw [hP, Subgroup.zpowers_le]; exact pp.property, ?_⟩
    intro c hc x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h := hppnorm ⟨c, hc⟩ (pp ^ k) (Subgroup.zpow_mem_zpowers pp k)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have h' := congrArg (fun y : C t => (y : G)) hj
    simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] using h'
  set QG : Subgroup G := Q.map (C t).subtype with hQG
  have hQGcard : Nat.card QG = Nat.card Q :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  have hQGle : QG ≤ C t ∧ QG ≤ Subgroup.centralizer P := by
    refine ⟨by rw [hQG]; exact Subgroup.map_subtype_le Q, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [hP, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hqp : q * pp = pp * q := (Subgroup.mem_centralizer_iff.mp (hQK' hq) pp hppN).symm
    have hc : Commute (q : G) (pp : G) := by
      change (q : G) * pp = pp * q
      exact congrArg Subtype.val hqp
    exact ((hc.zpow_right k).eq).symm
  have hQG2 : IsPGroup 2 QG := hQ2.map _
  have htQG : t ∈ QG := ⟨tInC t, htQ, rfl⟩
  have hQGt : ∀ u ∈ QG, u ≠ 1 → t ∈ Subgroup.zpowers u := by
    rintro _ ⟨q, hq, rfl⟩ hq1
    have hq1' : q ≠ 1 := fun h => hq1 (by rw [h]; rfl)
    have h := mem_zpowers_of_unique_involution hQ2 huniqQ hq hq1'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h' := congrArg (fun y : C t => (y : G)) hk
    simp only [Subgroup.coe_zpow] at h'
    exact h'
  have hpp1 : (pp : G) ≠ 1 := by
    intro h
    have h1 : pp = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hpp3
    norm_num at hpp3
  have hker : ∃ x ∈ P, (basis.representation χ).character x ≠
      (basis.representation χ).character 1 := by
    refine ⟨(pp : G), Subgroup.mem_zpowers _, character_ne_one_of_not_mem_ker _ ?_⟩
    intro hk
    exact hpp1 (hfaith ((MonoidHom.mem_ker.mp hk).trans (map_one _).symm))
  obtain ⟨hbound, -⟩ := normal_odd_prime_principal_quaternion_eigenspace_bound basis ideal
    principal hprincipal hχ (basis.representation χ).representation rfl ht2 P hPnormal
    Nat.prime_three (by decide) hPcard QG hQGle hQG2 htQG hQGt (fun x _ => hrat x) hker
  rw [hQGcard, show (basis.representation χ).representation.character t = -5 from htval,
    hdeg] at hbound
  have hn5 : ‖(-5 : ℂ)‖ = 5 := by norm_num
  rw [hn5] at hbound
  have h8 : (8 : ℝ) ≤ Nat.card Q := by exact_mod_cast hQcard
  have hcast : ((Nat.card Q * (3 - 1) : ℕ) : ℝ) = (Nat.card Q : ℝ) * 2 := by push_cast; ring
  rw [hcast] at hbound
  push_cast at hbound
  linarith

theorem local_parameter_five_nineteen_trivial_core_of_family {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector))
    (hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G), v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    Nat.card G = 68400 * a₀ * b₀ ^ 3 → N t = ⊥ ∧ Nat.card (C t) = 240 * a₀ * b₀ := by
  intro CN a₀ b₀ hG68400
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  obtain ⟨hn4, hCt, hDt, hrows⟩ := local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal q hq e he φ δ₁
    δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg hOF
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hne : ∀ K : ℕ, K ≠ 68400 → Nat.card G = K * a₀ * b₀ ^ 3 → False := by
    intro K hK h
    rw [h] at hG68400
    apply hK
    have h'' : K * (a₀ * b₀ ^ 3) = 68400 * (a₀ * b₀ ^ 3) := by
      rw [← mul_assoc, hG68400, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h''
  rcases hrows with ⟨hδ₁, hδ₂, hδ₃, hf₁, hf₂, hf₃, -⟩ | ⟨-, -, -, -, -, -, hX⟩ |
    ⟨-, -, -, -, -, -, hX⟩
  rotate_left
  · exact (hne 126000 (by norm_num) (congrArg Prod.fst hX)).elim
  · exact (hne 85680 (by norm_num) (congrArg Prod.fst hX)).elim
  refine ⟨?_, hCt⟩
  by_contra hN1
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1 hδ₁ hδ₂ hδ₃ hn4
  obtain ⟨hlφ, -, -, -, -, hnd, hψinj, hνinj, hψx, hνx, hνψ, hB, -, hodd, hsec, hrel⟩ := hfam
  obtain ⟨-, -, -, -, -, -, hf₄, -, -⟩ := hdeg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨lφ, -, -, hφchar, hφdeg, hφker⟩ := hlφ
  have hφN : ∀ y : C t, y ∈ N t → φ y = 5 := by
    intro y hy
    have hyker : y ∈ MonoidHom.ker (localBasis.representation lφ).representation := by
      rw [hφker]
      exact Subgroup.mem_sup_left hy
    have hρ : (localBasis.representation lφ).representation y =
        (localBasis.representation lφ).representation 1 := by
      rw [MonoidHom.mem_ker.mp hyker, map_one]
    rw [← hφchar]
    change LinearMap.trace ℂ _ ((localBasis.representation lφ).representation y) = 5
    rw [hρ]
    change (localBasis.representation lφ).character 1 = 5
    rw [(basis_character_one localBasis lφ).1, hφdeg]
    norm_num
  have hNodd : ∀ y : C t, y ∈ N t → Odd (orderOf y) := by
    intro y hy
    have hcop : Nat.Coprime 2 (Nat.card (N t)) := CFSG.pPrimeCore_coprime_card
    have hdvd : orderOf (⟨y, hy⟩ : N t) ∣ Nat.card (N t) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by
        rw [Nat.coprime_two_left]; exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))))
  have hNval : ∀ y : C t, y ∈ N t →
      (basis.representation χ₁).character (t * y) = -5 := by
    intro y hy
    rw [(hsec y (hNodd y hy)).1, hφN y hy]
    norm_num
  have htval : (basis.representation χ₁).character t = -5 := by
    have h := hNval 1 (one_mem _)
    rwa [OneMemClass.coe_one, mul_one] at h
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₁B : χ₁ ∈ B := hmem χ₁ (by simp)
  have hdeg1 : ∀ c : basis.index, (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
    fun c => (basis_character_one basis c).1
  have hχ₁1 : (basis.representation χ₁).character 1 = 19 := by rw [hdeg1, hf₁]; norm_num
  obtain ⟨hψ1, hν1, -, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  have hψdeg : ∀ j ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1),
      (basis.representation (ψ j)).character 1 = 18 := by
    intro j hj
    rw [hψ1 j hj, hχ₁1]
    norm_num
  have hνdeg : ∀ i ∈ Finset.range (2 ^ (4 - 3)),
      (basis.representation (ν i)).character 1 = 18 := by
    intro i hi
    rw [hν1 i hi, hχ₁1]
    norm_num
  have hrat : ∀ g, ∃ q : ℚ, (basis.representation χ₁).character g = q := by
    intro g
    apply CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal
      hχ₁B {1} (fun x hx => ⟨19, by rw [Set.mem_singleton_iff.mp hx, hχ₁1]; norm_num⟩)
    intro b hb hbval
    have hb1 := hbval 1 (Set.mem_singleton 1)
    rw [hχ₁1] at hb1
    have hb' : b ∈ B := hb
    rw [hB] at hb'
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hb'
    rcases hb' with ((h | h | h | h | h) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [h, hprincipal] at hb1
      norm_num at hb1
    · exact h
    · rw [h, hdeg1, hf₂] at hb1
      norm_num at hb1
    · rw [h, hdeg1, hf₃] at hb1
      norm_num at hb1
    · rw [h, hdeg1] at hb1
      have h76 : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 76 := by
        rw [hf₄, hf₂]
        norm_num
      have : (Module.finrank ℂ (basis.representation χ₄).vector : ℂ) = 76 := by
        exact_mod_cast h76
      rw [this] at hb1
      norm_num at hb1
    · rw [hψdeg j hj] at hb1
      norm_num at hb1
    · rw [hνdeg i hi] at hb1
      norm_num at hb1
  have hfaith : Function.Injective (basis.representation χ₁).representation := by
    rcases (MonoidHom.normal_ker (basis.representation χ₁).representation).eq_bot_or_eq_top
      with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have htker : t ∈ MonoidHom.ker (basis.representation χ₁).representation := h ▸ trivial
      have h1 : (basis.representation χ₁).character t =
          (basis.representation χ₁).character 1 := by
        change LinearMap.trace ℂ _ ((basis.representation χ₁).representation t) =
          LinearMap.trace ℂ _ ((basis.representation χ₁).representation 1)
        rw [MonoidHom.mem_ker.mp htker, (basis.representation χ₁).representation.map_one]
      rw [htval, hχ₁1] at h1
      norm_num at h1
  set ρC : Representation ℂ (C t) (basis.representation χ₁).vector :=
    (basis.representation χ₁).representation.comp (C t).subtype with hρC
  have ht2' : orderOf (tInC t) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (supplied_t_s_facts (by norm_num : 4 ≤ 4) fS ht).2.1
  have hNoddc : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  obtain ⟨k, r', hk, hdimV, ε, hE, -, hrE, -, hτrat, hτinv, hτfaith, -⟩ :=
    central_involution_coset_constant_half_degree ρC (tInC_central t) ht2' (N t) hNoddc
      (fun u _ hu => Subtype.ext (hfaith (by
        change (basis.representation χ₁).representation (u : G) = _ at hu
        rw [hu]
        simp)))
      (fun u _ => hrat (u : G))
      (fun u hu => by
        change (basis.representation χ₁).character (t * (u : G)) =
          (basis.representation χ₁).character t
        rw [hNval u hu, htval])
  have hk5 : k = -5 := by
    have h : ρC.character (tInC t) = -5 := htval
    rw [hk] at h
    exact_mod_cast h
  rw [hk5, hf₁] at hdimV
  have hr7 : r' = 7 := by norm_num at hdimV; omega
  rw [hr7] at hrE
  let τ : FiniteComplexRepresentation.{0, 0} (N t) :=
    { vector := Module.End.eigenspace (ρC (tInC t)) ε
      representation := (ρC.subrepresentation _ hE).comp (N t).subtype }
  have hτdeg : Module.finrank ℂ τ.vector = 7 := hrE
  have hτrat' : ∀ x : N t, ∃ q : ℚ, τ.character x = q := fun x => hτrat x x.2
  have hτfaith' : Function.Injective τ.representation := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hτfaith x x.2 hx)
  have hτinv' : ∀ (c : C t) (x : N t),
      τ.character ((MulAut.conjNormal (H := N t) c) x) = τ.character x := by
    intro c x
    change (ρC.subrepresentation _ hE).character (((MulAut.conjNormal (H := N t) c) x : C t)) =
      (ρC.subrepresentation _ hE).character (x : C t)
    rw [MulAut.conjNormal_apply]
    exact hτinv c x x.2
  have hprime8 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (N t) → p ≤ 8 := fun p hp hdvd => by
    have := CFSG.LyonsUnitaryFour.prime_le_of_faithful_rational_character τ hτfaith' hτrat' hp
      hdvd
    rw [hτdeg] at this
    exact this
  have hsyl3 : ∀ P : Sylow 3 (N t), Nat.card P ∣ 81 := by
    intro P
    have h := CFSG.LyonsUnitaryFour.sylow_card_dvd_of_faithful_rational_character τ hτfaith'
      hτrat' P
    rw [hτdeg, show (7 : ℕ) / (3 - 1) = 3 by norm_num, show Nat.factorial 3 = 6 by rfl] at h
    rw [Sylow.card_eq_multiplicity] at h ⊢
    have hle : (Nat.card (N t)).factorization 3 ≤ 4 := by
      by_contra hc
      push Not at hc
      have : 3 ^ 5 ∣ 3 ^ 3 * 6 := (pow_dvd_pow 3 hc).trans h
      norm_num at this
    exact pow_dvd_pow 3 hle |>.trans (by norm_num)
  have hsyl7 : ∀ P : Sylow 7 (N t), Nat.card P ∣ 7 := by
    intro P
    have h := CFSG.LyonsUnitaryFour.sylow_card_dvd_of_faithful_rational_character τ hτfaith'
      hτrat' P
    rw [hτdeg, show (7 : ℕ) / (7 - 1) = 1 by norm_num, Nat.factorial_one, pow_one,
      mul_one] at h
    exact h
  have h5a : ¬ 5 ∣ a₀ := prime_not_dvd_card_oddCore_centralizer hn fS ht hfus
    (by norm_num : Nat.Prime 5) (by decide) (by norm_num) (basis.representation χ₁)
    (by rw [hf₁]; norm_num) hrat hfaith htval hNval hDt
  have h7a : ¬ 7 ∣ a₀ := prime_not_dvd_card_oddCore_centralizer hn fS ht hfus
    (by norm_num : Nat.Prime 7) (by decide) (by norm_num) (basis.representation χ₁)
    (by rw [hf₁]; norm_num) hrat hfaith htval hNval hDt
  have ha : 0 < a₀ := Nat.card_pos
  have hb : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨P5⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hschur := CFSG.LyonsUnitaryFour.sylow_card_dvd_of_faithful_rational_character
    (basis.representation χ₁) hfaith hrat P5
  rw [hf₁, show (19 : ℕ) / (5 - 1) = 4 by norm_num] at hschur
  have hcardP5 := Sylow.card_eq_multiplicity P5
  have hfac_le : (Nat.card G).factorization 5 ≤ 4 := by
    by_contra hk
    push Not at hk
    have h5 : 5 ^ 5 ∣ Nat.card P5 := by
      rw [hcardP5]
      exact pow_dvd_pow 5 hk
    have := h5.trans hschur
    rw [show Nat.factorial 4 = 24 by rfl] at this
    norm_num at this
  have h68400 : padicValNat 5 68400 = 2 := by
    rw [show (68400 : ℕ) = 5 ^ 2 * 2736 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hval : (Nat.card G).factorization 5 =
      2 + padicValNat 5 a₀ + 3 * padicValNat 5 b₀ := by
    rw [Nat.factorization_def _ (by norm_num), hG68400,
      padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by norm_num) ha.ne',
      padicValNat.pow, h68400]
  have h5b : ¬ 5 ∣ b₀ := fun h => by
    have := one_le_padicValNat_of_dvd hb.ne' h
    omega
  have hab : a₀ * b₀ = Nat.card (N t) := Subgroup.card_mul_index CN
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (N t) → p = 3 ∨ p = 7 := by
    intro p hp hdvd
    have hp8 := hprime8 p hp hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hNoddc) (even_iff_two_dvd.mpr hdvd)
    have hp5 : p ≠ 5 := by
      rintro rfl
      rw [← hab] at hdvd
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp hdvd with h | h
      · exact h5a h
      · exact h5b h
    interval_cases p <;> first | omega | (exfalso; revert hp; decide)
  have h7N := not_seven_dvd_card_oddCore fS ht basis ideal principal hprincipal hχ₁B hrat hfaith
    htval hf₁ hsyl7 hprimes hsyl3
  have hNpos : Nat.card (N t) ≠ 0 := Nat.card_pos.ne'
  have hN3card : Nat.card (N t) = 3 ^ (Nat.card (N t)).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hNpos
    intro d hd hdd
    rcases hprimes d hd hdd with h | h
    · exact h
    · exact absurd (h ▸ hdd) h7N
  have hN3 : IsPGroup 3 (N t) := IsPGroup.of_card hN3card
  have hN81 : Nat.card (N t) ≤ 81 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card (N t) = 3 ^ m := ⟨_, hN3card⟩
    obtain ⟨P3⟩ : Nonempty (Sylow 3 (N t)) := inferInstance
    have h := hsyl3 P3
    rw [Sylow.card_eq_multiplicity, hm, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same] at h
    rw [hm]
    exact Nat.le_of_dvd (by norm_num) h
  have h5C : 5 ∣ Nat.card (C t) := by
    rw [hCt]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  exact hN1 (oddCore_eq_bot_of_isPGroup_three S fS hG ht hnonab hcentral hnc hmodel basis ideal
    principal hprincipal hχ₁B hrat hfaith htval hf₁ τ hτfaith' hτrat' hτdeg hτinv' hN3 hN81 h5C)

end CFSG.Semidihedral.Principal
