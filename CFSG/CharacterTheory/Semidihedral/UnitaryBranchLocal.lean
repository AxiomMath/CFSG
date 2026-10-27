module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchProjective
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

open scoped Pointwise

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.Principal

theorem conj_pow_eq_of_central {C : Type*} [Group C] {c d z : C} (hz : z ∈ Subgroup.center C)
    (hcd : c * d * c⁻¹ = z * d) (m : ℕ) : c ^ m * d * (c ^ m)⁻¹ = z ^ m * d := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzc : ∀ y : C, z ^ m * y = y * z ^ m := fun y =>
      (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz m) y).symm
    calc c ^ (m + 1) * d * (c ^ (m + 1))⁻¹ = c * (c ^ m * d * (c ^ m)⁻¹) * c⁻¹ := by group
      _ = c * (z ^ m * d) * c⁻¹ := by rw [ih]
      _ = z ^ m * (c * d * c⁻¹) := by
        calc c * (z ^ m * d) * c⁻¹ = (c * z ^ m) * d * c⁻¹ := by group
          _ = (z ^ m * c) * d * c⁻¹ := by rw [hzc c]
          _ = z ^ m * (c * d * c⁻¹) := by group
      _ = z ^ (m + 1) * d := by rw [hcd, pow_succ, mul_assoc]

theorem commute_of_mem_comap {C X : Type*} [Group C] [Group X] [Finite C] (κ : C →* X)
    (hker : κ.ker ≤ Subgroup.center C) (T : Subgroup X) [Finite T]
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hcop : Nat.Coprime (Nat.card T) (Nat.card κ.ker))
    {c d : C} (hc : c ∈ T.comap κ) (hd : d ∈ T.comap κ) : c * d = d * c := by
  set z := c * d * c⁻¹ * d⁻¹ with hzdef
  have hzk : z ∈ κ.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_mul, map_mul, map_inv, map_inv,
      hT _ hc _ hd]
    group
  have hz : z ∈ Subgroup.center C := hker hzk
  have hcd : c * d * c⁻¹ = z * d := by rw [hzdef]; group
  set m := Nat.card T
  have hcm : c ^ m ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have h' : ((⟨κ c, hc⟩ : T) ^ m) = 1 := pow_card_eq_one'
    have h'' := congrArg (fun y : T => (y : X)) h'
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h''
    exact h''
  have hzm : z ^ m = 1 := by
    have h1 := conj_pow_eq_of_central hz hcd m
    have h2 : c ^ m * d * (c ^ m)⁻¹ = d := by
      rw [(Subgroup.mem_center_iff.mp (hker hcm) d).symm]
      group
    rw [h2] at h1
    exact (mul_eq_right.mp h1.symm)
  have hzk' : z ^ Nat.card κ.ker = 1 := by
    have h' : ((⟨z, hzk⟩ : κ.ker) ^ Nat.card κ.ker) = 1 := pow_card_eq_one'
    have h'' := congrArg (fun y : κ.ker => (y : C)) h'
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h''
    exact h''
  have hz1 : z = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzm)
      (orderOf_dvd_of_pow_eq_one hzk')
  rw [hzdef] at hz1
  calc c * d = c * d * c⁻¹ * d⁻¹ * (d * c) := by group
    _ = d * c := by rw [hz1, one_mul]

theorem card_comap_of_le_range {C X : Type*} [Group C] [Group X] [Finite C] (κ : C →* X)
    (T : Subgroup X) (hT : T ≤ κ.range) :
    Nat.card (T.comap κ) = Nat.card T * Nat.card κ.ker := by
  have : Finite κ.range := Finite.of_surjective _ κ.rangeRestrict_surjective
  have h1 := Subgroup.card_mul_index (T.comap κ)
  rw [Subgroup.index_comap] at h1
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := κ.range)
  rw [inf_eq_left.mpr hT] at h2
  have h3 : Nat.card C = Nat.card κ.ker * Nat.card κ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup κ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv]
  have hpos : 0 < T.relIndex κ.range := by
    rcases Nat.eq_zero_or_pos (T.relIndex κ.range) with h | h
    · rw [h, zero_mul] at h2
      exact absurd h2.symm Nat.card_pos.ne'
    · exact h
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

theorem eq_zpowers_r_of_commute (n : ℕ) (hn : 4 ≤ n) (R : Subgroup (SemidihedralGroup n))
    (hR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hcard : Nat.card R = 2 ^ (n - 1)) :
    R = Subgroup.zpowers (r n) := by
  have hn3 : 3 ≤ n := by omega
  have : Finite (SemidihedralGroup n) := presentation_finite n hn3
  have hrcard : Nat.card (Subgroup.zpowers (r n)) = 2 ^ (n - 1) := by
    rw [Nat.card_zpowers, orderOf_r n hn3, modulus]
  by_cases hle : R ≤ Subgroup.zpowers (r n)
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hrcard, hcard])
  exfalso
  obtain ⟨g, hgR, hgr⟩ := Set.not_subset.mp hle
  have hRidx : R.index = 2 := by
    have h := Subgroup.card_mul_index R
    rw [hcard, card n hn3] at h
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hr2 : r n ^ 2 ∈ R := Subgroup.sq_mem_of_index_two hRidx (r n)
  obtain ⟨⟨j, e⟩, hje⟩ : ∃ c : ZMod (modulus n) × ZMod 2, element n hn3 c.1 c.2 = g :=
    ⟨coordinateEquiv n hn3 g, (coordinateEquiv n hn3).symm_apply_apply g⟩
  have he : e = 1 := by
    rcases exponent_cases e with rfl | rfl
    · exfalso
      apply hgr
      rw [← hje, ← ZMod.natCast_zmod_val j, ← Int.cast_natCast,
        ← r_zpow_eq_element n hn3]
      exact Subgroup.zpow_mem_zpowers _ _
    · rfl
  subst he
  have hcomm := hR g hgR _ hr2
  have hr2e : r n ^ 2 = element n hn3 2 0 := by
    have := r_zpow_eq_element n hn3 2
    simpa using this
  rw [hr2e, ← hje] at hcomm
  have hconj : element n hn3 j 1 * element n hn3 2 0 * (element n hn3 j 1)⁻¹ =
      element n hn3 2 0 := by
    rw [hcomm]
    group
  rw [conjugate_rotation_by_reflection n hn3, element_eq_iff] at hconj
  rcases (twist_fixed_iff n hn 2).mp hconj.1 with h0 | hh
  · have h8 : 8 ≤ modulus n := by
      unfold modulus
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hv := congrArg ZMod.val h0
    rw [ZMod.val_zero, show (2 : ZMod (modulus n)) = ((2 : ℕ) : ZMod (modulus n)) by norm_cast,
      ZMod.val_natCast_of_lt (by omega)] at hv
    omega
  · have h8 : 8 ≤ modulus n := by
      unfold modulus
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhalf : modulus n = 2 * half n := modulus_eq_two_mul_half (by omega)
    have hv := congrArg ZMod.val hh
    rw [show (2 : ZMod (modulus n)) = ((2 : ℕ) : ZMod (modulus n)) by norm_cast,
      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    omega

open ActualSimpleLayerLocalPackage

variable {G : Type} [Group G] [Finite G]

structure UnitaryLocalData (t : G) (p f : ℕ) (F : Type) [Field F] [Finite F]
    (κ : C t →* Equiv.Perm (Omega F)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  card_field : Nat.card F = p ^ f
  mod_four : p ^ f % 4 = 1
  orderOf_t : orderOf t = 2
  ker_eq : κ.ker = NZ t
  range_eq : κ.range = coordinateD F
  core_central : N t ≤ Subgroup.center (C t)
  core_cyclic : IsCyclic (N t)
  core_coprime : Nat.Coprime (Nat.card (N t)) (p * (p ^ f - 1))

abbrev unitaryK (t : G) : Subgroup G := (NZ t).map (C t).subtype

omit [Finite G] in
theorem supplied_orderOf {n : ℕ} (hn : 4 ≤ n) {S : Subgroup G}
    (fS : SemidihedralGroup n ≃* S) {t : G} (hz : (fS (z n) : G) = t) : orderOf t = 2 := by
  rw [← hz, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_z n (by omega)]

omit [Finite G] in
theorem sylow_le_and_normalizer_le_centralizer (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    (S : Subgroup G) ≤ C t ∧ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ C t := by
  have hz : (fS (z n) : G) = t := by
    rw [ht, z, map_pow, SubmonoidClass.coe_pow]
    rfl
  have htS : t ∈ (S : Subgroup G) := hz ▸ (fS (z n)).2
  have hcent : ∀ y ∈ (S : Subgroup G), y * t = t * y := by
    intro y hy
    obtain ⟨a, ha⟩ := fS.surjective ⟨y, hy⟩
    have hc := Subgroup.mem_center_iff.mp (z_mem_center n hn) a
    have h1 := congrArg (fun w => (fS w : G)) hc
    simp only [map_mul, Subgroup.coe_mul, ha, hz] at h1
    exact h1
  refine ⟨fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcent y hy), ?_⟩
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : ∀ y, y ∈ (S : Subgroup G) ↔ g * y * g⁻¹ ∈ (S : Subgroup G) :=
    Subgroup.mem_normalizer_iff.mp hg
  have hgt : g * t * g⁻¹ ∈ (S : Subgroup G) := (hmem t).mp htS
  have hcentral : fS.symm ⟨g * t * g⁻¹, hgt⟩ ∈ Subgroup.center (SemidihedralGroup n) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply fS.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    set y := (fS a : G)
    have hy : g⁻¹ * y * g ∈ (S : Subgroup G) := by
      refine (hmem (g⁻¹ * y * g)).mpr ?_
      have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this]
      exact (fS a).2
    have h1 := hcent _ hy
    calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * y := by group
  rw [center_eq_zpowers n hn, Subgroup.mem_zpowers_iff] at hcentral
  obtain ⟨k, hk⟩ := hcentral
  have hk' : z n ^ k = z n ^ (k % 2) := by
    have h := (zpow_mod_orderOf (z n) k).symm
    rwa [orderOf_z n (by omega)] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [hk', h0, zpow_zero] at hk
    have h2 := congrArg (fun w => (fS w : G)) hk
    simp only [map_one, OneMemClass.coe_one, MulEquiv.apply_symm_apply] at h2
    have ht1 : t ≠ 1 := by
      intro h
      have := (supplied_orderOf (n := n) hn fS hz)
      rw [h, orderOf_one] at this
      omega
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, ← h2]
    group
  · rw [hk', h1, zpow_one] at hk
    have h2 := congrArg (fun w => (fS w : G)) hk
    simp only [MulEquiv.apply_symm_apply] at h2
    rw [hz] at h2
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [← h2]

theorem NZ_facts {t : G} (ht : orderOf t = 2) (hcent : N t ≤ Subgroup.center (C t))
    (hcyc : IsCyclic (N t)) :
    Odd (Nat.card (N t)) ∧ NZ t ≤ Subgroup.center (C t) ∧ IsCyclic (NZ t) ∧
      Nat.card (NZ t) = 2 * Nat.card (N t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have htC : orderOf (tInC t) = 2 := by
    rw [tInC, Subgroup.orderOf_mk, ht]
  have hNZc : NZ t ≤ Subgroup.center (C t) :=
    sup_le hcent (Subgroup.zpowers_le.mpr (tInC_central t))
  obtain ⟨gN, hgN⟩ := IsCyclic.exists_generator (α := N t)
  set a := Nat.card (N t)
  have hgNo : orderOf (gN : C t) = a := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgN]
  set x : C t := (gN : C t) * tInC t with hxdef
  have hcomm : Commute (gN : C t) (tInC t) :=
    Subgroup.mem_center_iff.mp (tInC_central t) (gN : C t)
  have hcop2 : Nat.Coprime (orderOf (gN : C t)) (orderOf (tInC t)) := by
    rw [hgNo, htC]
    exact Nat.coprime_two_right.mpr hodd
  have hxo : orderOf x = a * 2 := by
    rw [hxdef, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop2, hgNo, htC]
  have hxNZ : x ∈ NZ t := Subgroup.mul_mem _ (Subgroup.mem_sup_left gN.2)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hNZx : NZ t = Subgroup.zpowers x := by
    refine le_antisymm (sup_le ?_ ?_) (Subgroup.zpowers_le.mpr hxNZ)
    ·
      have hpow : x ^ (a + 1) = gN := by
        have h1 : (gN : C t) ^ a = 1 := by rw [← hgNo]; exact pow_orderOf_eq_one _
        have h2 : tInC t ^ (a + 1) = 1 := by
          obtain ⟨m, hm⟩ := hodd
          rw [hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, ← htC,
            pow_orderOf_eq_one, one_pow]
        rw [hxdef, hcomm.mul_pow, h2, mul_one, pow_succ, h1, one_mul]
      intro y hy
      obtain ⟨k, hk⟩ := hgN ⟨y, hy⟩
      have hk' : y = (gN : C t) ^ k := by
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_zpow] at this
        exact this.symm
      rw [hk', ← hpow, ← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [Subgroup.zpowers_le]
      have hpow : x ^ a = tInC t := by
        rw [hxdef, hcomm.mul_pow, ← hgNo, pow_orderOf_eq_one, one_mul, hgNo]
        obtain ⟨m, hm⟩ := hodd
        rw [hm, pow_succ, pow_mul, ← htC, pow_orderOf_eq_one, one_pow, one_mul]
      rw [← hpow]
      exact Subgroup.npow_mem_zpowers _ _
  refine ⟨hodd, hNZc, ?_, ?_⟩
  · rw [hNZx]
    infer_instance
  · rw [hNZx, Nat.card_zpowers, hxo, mul_comm]

theorem unitaryLocalData_card {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) :
    Nat.card (unitaryK t) = 2 * Nat.card (N t) ∧
      Nat.card (C t) = 2 * Nat.card (N t) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  obtain ⟨-, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  have hK : Nat.card (unitaryK t) = 2 * Nat.card (N t) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective, hNZcard]
  refine ⟨hK, ?_⟩
  have h3 : Nat.card (C t) = Nat.card κ.ker * Nat.card κ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup κ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv]
  rw [h3, hD.ker_eq, hD.range_eq, hNZcard, card_coordinateD, hD.card_field]

theorem unitaryK_properties {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) :
    t ∈ unitaryK t ∧ (∀ r ∈ unitaryK t, ∀ g ∈ C t, g * r = r * g) ∧
      ¬ p ∣ Nat.card (unitaryK t) ∧
      ((∀ u ∈ (N t).map (C t).subtype, u ≠ 1 → Subgroup.centralizer {u} ≤ C t) →
        ∀ r ∈ unitaryK t, r ≠ 1 → Subgroup.centralizer {r} ≤ C t) := by
  obtain ⟨hodd, hNZc, -, -⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  have htK : t ∈ unitaryK t :=
    ⟨tInC t, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), rfl⟩
  refine ⟨htK, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ g hg
    have h := Subgroup.mem_center_iff.mp (hNZc hc) ⟨g, hg⟩
    exact congrArg Subtype.val h
  · rw [(unitaryLocalData_card hD).1]
    intro hdvd
    have hp := hD.prime
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | ha
    · exact hD.ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · have hcop := hD.core_coprime
      have h1 : p ∣ Nat.gcd (Nat.card (N t)) (p * (p ^ f - 1)) :=
        Nat.dvd_gcd ha (dvd_mul_right p _)
      rw [hcop] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · intro hconf r hr hr1
    obtain ⟨c, hc, rfl⟩ := hr
    have hc' : c ∈ ((N t : Set (C t)) * (Z t : Set (C t))) := by
      rw [← Subgroup.normal_mul]
      exact hc
    obtain ⟨y, hy, w, hw, hyw⟩ := hc'
    simp only at hyw
    subst hyw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have htC : orderOf (tInC t) = 2 := by
      rw [tInC, Subgroup.orderOf_mk, hD.orderOf_t]
    have hk : tInC t ^ k = tInC t ^ (k % 2) := by
      have h := (zpow_mod_orderOf (tInC t) k).symm
      rwa [htC] at h
    rw [hk] at hr1 ⊢
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero, mul_one] at hr1 ⊢
      exact hconf _ ⟨y, hy, rfl⟩ hr1
    · rw [h1, zpow_one]
      have hcomm : Commute y (tInC t) :=
        Subgroup.mem_center_iff.mp (tInC_central t) y
      have hpow : (y * tInC t) ^ Nat.card (N t) = tInC t := by
        rw [hcomm.mul_pow]
        have hy1 : y ^ Nat.card (N t) = 1 := by
          have h' : ((⟨y, hy⟩ : N t) ^ Nat.card (N t)) = 1 := pow_card_eq_one'
          have h'' := congrArg Subtype.val h'
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h''
          exact h''
        obtain ⟨m, hm⟩ := hodd
        rw [hy1, one_mul, hm, pow_succ, pow_mul, ← htC, pow_orderOf_eq_one, one_pow, one_mul]
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have hgp : g * ((C t).subtype (y * tInC t)) ^ Nat.card (N t) =
          ((C t).subtype (y * tInC t)) ^ Nat.card (N t) * g := by
        exact (Commute.pow_right hg _)
      rw [← map_pow, hpow] at hgp
      exact hgp

theorem card_translationHom_range (F' : Type) [Field F'] [Finite F'] :
    Nat.card (translationHom F').range = Nat.card F' := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (translationHom_injective F')).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem card_multiplierHom_range (F' : Type) [Field F'] [Finite F'] :
    Nat.card (multiplierHom F').range = Nat.card F' - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (multiplierHom_injective F')).toEquiv,
    Nat.card_units]

theorem factorization_prime_pow_mul {p f m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ f * m).factorization p = f := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem exists_translation_sylow {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) :
    ∃ Q₀ : Subgroup (C t), Nat.card Q₀ = p ^ f ∧ (∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a) ∧
      (∀ u ∈ Q₀, ∃ b : F, κ u = translation F b) ∧
      ∀ h ∈ (multiplierHom F).range.comap κ, ∀ u ∈ Q₀, h * u * h⁻¹ ∈ Q₀ := by
  classical
  have hp := hD.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hodd, hNZc, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  have hker : κ.ker ≤ Subgroup.center (C t) := hD.ker_eq ▸ hNZc
  have hkercard : Nat.card κ.ker = 2 * Nat.card (N t) := by rw [hD.ker_eq, hNZcard]
  set U := (translationHom F).range
  have hUcard : Nat.card U = p ^ f := by rw [card_translationHom_range F, hD.card_field]
  have hUle : U ≤ κ.range := hD.range_eq ▸ translationHom_range_le F
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  set Upre := U.comap κ
  have hnot : ¬ p ∣ 2 * Nat.card (N t) := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | ha
    · exact hD.ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · have h1 : p ∣ Nat.gcd (Nat.card (N t)) (p * (p ^ f - 1)) :=
        Nat.dvd_gcd ha (dvd_mul_right p _)
      rw [hD.core_coprime] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hUprecard : Nat.card Upre = p ^ f * (2 * Nat.card (N t)) := by
    rw [card_comap_of_le_range κ U hUle, hUcard, hkercard]
  have hcopU : Nat.Coprime (Nat.card U) (Nat.card κ.ker) := by
    rw [hUcard, hkercard]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot)
  have hUprecomm : ∀ x ∈ Upre, ∀ y ∈ Upre, x * y = y * x := fun x hx y hy =>
    commute_of_mem_comap κ hker U hUcomm hcopU hx hy
  let P : Sylow p Upre := default
  have hPcard : Nat.card P = p ^ f := by
    rw [Sylow.card_eq_multiplicity, hUprecard, factorization_prime_pow_mul hp hnot]
  have hPnormal : (P : Subgroup Upre).Normal := by
    have : IsMulCommutative Upre := ⟨⟨fun a b => Subtype.ext (hUprecomm a a.2 b b.2)⟩⟩
    infer_instance
  have hPuniq : ∀ x : Upre, x ^ p ^ f = 1 → x ∈ (P : Subgroup Upre) := by
    intro x hx
    have hxp : IsPGroup p (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := (orderOf x).factorization p)
      rw [Nat.card_zpowers]
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hx)
      rw [hk, hp.factorization_pow, Finsupp.single_eq_same]
    obtain ⟨P', hP'⟩ := hxp.exists_le_sylow
    have := Sylow.unique_of_normal P hPnormal
    rw [Subsingleton.elim P' P] at hP'
    exact hP' (Subgroup.mem_zpowers x)
  set Q₀ : Subgroup (C t) := (P : Subgroup Upre).map Upre.subtype with hQ₀
  refine ⟨Q₀, ?_, ?_, ?_, ?_⟩
  · rw [hQ₀, Subgroup.card_map_of_injective Upre.subtype_injective, hPcard]
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact hUprecomm x x.2 y y.2
  · rintro _ ⟨x, -, rfl⟩
    obtain ⟨b, hb⟩ := x.2
    exact ⟨Multiplicative.toAdd b, hb.symm⟩
  · rintro h ⟨c, hc⟩ _ ⟨x, hxP, rfl⟩
    have hmem : h * (x : C t) * h⁻¹ ∈ Upre := by
      obtain ⟨b, hb⟩ := x.2
      change κ (h * (x : C t) * h⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv, ← hc, ← hb, multiplierHom_apply, translationHom_apply,
        multiplier_conj_translation]
      exact ⟨Multiplicative.ofAdd ((c : F) * Multiplicative.toAdd b), rfl⟩
    have hxq : x ^ p ^ f = 1 := by
      rw [← hPcard]
      have h' : ((⟨x, hxP⟩ : (P : Subgroup Upre)) ^ Nat.card P) = 1 := pow_card_eq_one'
      have h'' := congrArg Subtype.val h'
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h''
    have hq : (⟨h * (x : C t) * h⁻¹, hmem⟩ : Upre) ^ p ^ f = 1 := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val hxq
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
      rw [conj_pow, h1, mul_one, mul_inv_cancel]
    exact ⟨⟨_, hmem⟩, hPuniq _ hq, rfl⟩

theorem isCyclic_of_commute_of_card {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRcard : Nat.card R = 2 ^ (n - 1)) :
    IsCyclic R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hRS'⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  set R₀ := R.map (MulAut.conj g).toMonoidHom with hR₀def
  have hR₀S : R₀ ≤ (S : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hRS' hx)
  have hR₀comm : ∀ a b : R₀, (a : G) * b = b * a := by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hRcomm x hx y hy]
  let ψ : R₀ →* SemidihedralGroup n := fS.symm.toMonoidHom.comp (Subgroup.inclusion hR₀S)
  have hψ : Function.Injective ψ :=
    fS.symm.injective.comp (Subgroup.inclusion_injective hR₀S)
  have hR₀card : Nat.card R₀ = 2 ^ (n - 1) := by
    rw [hR₀def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hRcard]
  have hrange : ψ.range = Subgroup.zpowers (r n) := by
    apply eq_zpowers_r_of_commute n hn
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hR₀comm a b)
    · rw [← hR₀card]
      exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  have : IsCyclic ψ.range := hrange ▸ inferInstance
  have hR₀cyc : IsCyclic R₀ := isCyclic_of_injective ψ.rangeRestrict
    (MonoidHom.rangeRestrict_injective_iff.mpr hψ)
  exact isCyclic_of_injective
    (R.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom
    (MulEquiv.injective _)

theorem factorization_two_multiplier_preimage {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    (Nat.card ((multiplierHom F).range.comap κ)).factorization 2 = n - 1 ∧
      Nat.card ((multiplierHom F).range.comap κ) = (p ^ f - 1) * (2 * Nat.card (N t)) := by
  have hp := hD.prime
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  obtain ⟨-, hCcard⟩ := unitaryLocalData_card hD
  have hkercard : Nat.card κ.ker = 2 * Nat.card (N t) := by rw [hD.ker_eq, hNZcard]
  set M := (multiplierHom F).range
  have hMle : M ≤ κ.range := hD.range_eq ▸ multiplierHom_range_le F
  have hMcard : Nat.card M = p ^ f - 1 := by rw [card_multiplierHom_range F, hD.card_field]
  have hH'card : Nat.card (M.comap κ) = (p ^ f - 1) * (2 * Nat.card (N t)) := by
    rw [card_comap_of_le_range κ M hMle, hMcard, hkercard]
  refine ⟨?_, hH'card⟩
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hqodd : Odd q := (Nat.odd_iff.mpr (by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hD.ne_two
    · exact h)).pow
  have hScard : Nat.card S = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv, card n (by omega)]
  have hG2 : (Nat.card G).factorization 2 = n := by
    have h := Sylow.card_eq_multiplicity S
    rw [hScard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hSC := (sylow_le_and_normalizer_le_centralizer n hn S fS ht).1
  have hC2 : (Nat.card (C t)).factorization 2 = n := by
    apply le_antisymm
    · rw [← hG2]
      exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card _) 2
    · have h := Subgroup.card_dvd_of_le hSC
      rw [hScard] at h
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h
  obtain ⟨m, hm⟩ : ∃ m, q + 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k + 1, by omega⟩
  have hmodd : Odd m := by
    have h4 := hD.mod_four
    rw [← hqdef] at h4
    rw [Nat.odd_iff]
    omega
  have hsplit : Nat.card (C t) = Nat.card (M.comap κ) * (2 ^ 1 * (q * m)) := by
    rw [hCcard, hH'card]
    have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [hq1, Nat.one_le_pow 2 q (by omega)]
      ring
    rw [hsq, hm]
    ring
  have hnot : ¬ 2 ∣ q * m := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hqodd.mul hmodd
  have hH0 : Nat.card (M.comap κ) ≠ 0 := Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  rw [hsplit, Nat.factorization_mul hH0 (Nat.mul_ne_zero (by norm_num) (Nat.mul_ne_zero hq0 hm0)),
    Finsupp.add_apply,
    factorization_prime_pow_mul Nat.prime_two hnot] at hC2
  omega

theorem multiplier_preimage_isCyclic {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    IsCyclic ((multiplierHom F).range.comap κ) := by
  classical
  have hp := hD.prime
  obtain ⟨hodd, hNZc, hNZcyc, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  obtain ⟨h2fac, hH'card⟩ := factorization_two_multiplier_preimage hD n hn S fS ht
  have hker : κ.ker ≤ Subgroup.center (C t) := hD.ker_eq ▸ hNZc
  set M := (multiplierHom F).range
  set H' := M.comap κ
  have hMcard : Nat.card M = p ^ f - 1 := by rw [card_multiplierHom_range F, hD.card_field]
  have hMcyc : IsCyclic M := isCyclic_of_surjective (multiplierHom F).rangeRestrict
    (multiplierHom F).rangeRestrict_surjective
  let φ : H' →* M := (κ.comp H'.subtype).codRestrict M (fun x => x.2)
  have hφ : ∀ x : H', ((φ x : M) : Equiv.Perm (Omega F)) = κ x := fun x => rfl
  have hφker : ∀ x : H', φ x = 1 → (x : C t) ∈ NZ t := by
    intro x hx
    rw [← hD.ker_eq, MonoidHom.mem_ker, ← hφ, hx]
    rfl
  have hφcent : φ.ker ≤ Subgroup.center H' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : (x : C t) ∈ NZ t := hφker x hx
    exact (Subgroup.mem_center_iff.mp (hNZc hx') y)
  have hcomm : IsMulCommutative H' := φ.isMulCommutative_of_isCyclic_of_ker_le_center hφcent
  have hZ : IsZGroup H' := by
    refine ⟨fun ℓ hℓ P => ?_⟩
    have : Fact ℓ.Prime := ⟨hℓ⟩
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hPcard : Nat.card P = 2 ^ (n - 1) := by
        rw [Sylow.card_eq_multiplicity, h2fac]
      set R : Subgroup G := ((P : Subgroup H').map H'.subtype).map (C t).subtype
      have hRcard : Nat.card R = 2 ^ (n - 1) := by
        rw [Subgroup.card_map_of_injective (C t).subtype_injective,
          Subgroup.card_map_of_injective H'.subtype_injective, hPcard]
      have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
        rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩ _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
        have := hcomm.is_comm.comm x y
        exact congrArg (fun w : H' => ((w : C t) : G)) this
      have hRcyc := isCyclic_of_commute_of_card hn S fS R (IsPGroup.of_card hRcard) hRcomm hRcard
      exact isCyclic_of_injective
        (((P : Subgroup H').equivMapOfInjective _ H'.subtype_injective).trans
          (((P : Subgroup H').map H'.subtype).equivMapOfInjective _
            (C t).subtype_injective)).toMonoidHom (MulEquiv.injective _)
    · have hPp : ∀ x : P, ∃ k : ℕ, orderOf x = ℓ ^ k := fun x =>
        IsPGroup.iff_orderOf.mp P.isPGroup' x
      by_cases hℓa : ℓ ∣ 2 * Nat.card (N t)
      ·
        have hℓa' : ℓ ∣ Nat.card (N t) := by
          rcases (Nat.Prime.dvd_mul hℓ).mp hℓa with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h) hℓ2
          · exact h
        have hℓq : ¬ ℓ ∣ p ^ f - 1 := by
          intro h
          have h1 : ℓ ∣ Nat.gcd (Nat.card (N t)) (p * (p ^ f - 1)) :=
            Nat.dvd_gcd hℓa' (dvd_mul_of_dvd_right h p)
          rw [hD.core_coprime] at h1
          exact hℓ.one_lt.ne' (Nat.dvd_one.mp h1)
        have hPNZ : ∀ x : P, ((x : H') : C t) ∈ NZ t := by
          intro x
          apply hφker
          obtain ⟨k, hk⟩ := hPp x
          have h1 : orderOf (φ x) ∣ ℓ ^ k := by
            rw [← hk, ← Subgroup.orderOf_coe x]
            exact orderOf_map_dvd φ _
          have h2 : orderOf (φ x) ∣ p ^ f - 1 := by
            rw [← hMcard]
            exact orderOf_dvd_natCard _
          have hcop : Nat.Coprime (ℓ ^ k) (p ^ f - 1) :=
            Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq)
          exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
        let ψ : P →* NZ t :=
          { toFun := fun x => ⟨((x : H') : C t), hPNZ x⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        exact isCyclic_of_injective ψ (fun x y h => by
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun w : NZ t => (w : C t)) h)
      ·
        refine isCyclic_of_injective (φ.comp (P : Subgroup H').subtype) ?_
        rw [injective_iff_map_eq_one]
        intro x hx
        have hxNZ := hφker x hx
        obtain ⟨k, hk⟩ := hPp x
        have h1 : orderOf ((x : H') : C t) ∣ 2 * Nat.card (N t) := by
          rw [← hNZcard]
          have := orderOf_dvd_natCard (⟨((x : H') : C t), hxNZ⟩ : NZ t)
          rwa [Subgroup.orderOf_mk] at this
        have h2 : orderOf ((x : H') : C t) ∣ ℓ ^ k := by
          rw [← hk, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        have hcop : Nat.Coprime (ℓ ^ k) (2 * Nat.card (N t)) :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓa)
        have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
        rw [orderOf_eq_one_iff] at h3
        apply Subtype.ext
        apply Subtype.ext
        exact h3
  infer_instance

theorem exists_unitary_local_subgroups {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ) (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    ∃ Q₀ H : Subgroup G,
      Nat.card Q₀ = p ^ f ∧ (∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a) ∧ Q₀ ≤ C t ∧
      ¬ p ∣ Q₀.relIndex (C t) ∧
      (∀ u : C t, (u : G) ∈ Q₀ → ∃ b : F, κ u = translation F b) ∧
      H = ((multiplierHom F).range.comap κ).map (C t).subtype ∧
      H ≤ Subgroup.normalizer (Q₀ : Set G) ∧ IsCyclic H ∧ unitaryK t ≤ H ∧
      Nat.card H = (p ^ f - 1) * Nat.card (unitaryK t) := by
  have hp := hD.prime
  obtain ⟨Q₀', hQcard, hQcomm, hQtr, hQnorm⟩ := exists_translation_sylow hD
  obtain ⟨hKcard, hCcard⟩ := unitaryLocalData_card hD
  obtain ⟨-, hH'card⟩ := factorization_two_multiplier_preimage hD n hn S fS ht
  have hH'cyc := multiplier_preimage_isCyclic hD n hn S fS ht
  set H' := (multiplierHom F).range.comap κ
  refine ⟨Q₀'.map (C t).subtype, H'.map (C t).subtype, ?_, ?_, Subgroup.map_subtype_le _, ?_,
    ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (C t).subtype_injective, hQcard]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hQcomm x hx y hy)
  ·
    have hsub : (Q₀'.map (C t).subtype).subgroupOf (C t) = Q₀' :=
      Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective Q₀'
    rw [Subgroup.relIndex, hsub]
    have h := Subgroup.card_mul_index Q₀'
    rw [hQcard, hCcard] at h
    have hidx : Q₀'.index = 2 * Nat.card (N t) * ((p ^ f) ^ 2 - 1) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos f)
      rw [h]
      ring
    rw [hidx]
    intro hdvd
    have hKp := (unitaryK_properties hD).2.2.1
    rw [hKcard] at hKp
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact hKp h1
    · have hpq : p ∣ (p ^ f) ^ 2 :=
        dvd_pow (dvd_pow_self p (by have := hD.one_le; omega)) (by norm_num)
      have h2 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub hpq h1
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos hp.pos f))] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := hu
    have : v = u := Subtype.ext hvu
    subst this
    exact hQtr v hv
  · rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨h * y' * h⁻¹, hQnorm h hh y' hy', rfl⟩
    · rintro ⟨w, hw, hwy⟩
      have hyC : y ∈ C t := by
        have : y = (h : G)⁻¹ * (w : G) * h := by
          rw [show (w : G) = (C t).subtype w from rfl, hwy]
          simp only [Subgroup.coe_subtype]
          group
        rw [this]
        exact (C t).mul_mem ((C t).mul_mem ((C t).inv_mem h.2) w.2) h.2
      refine ⟨⟨y, hyC⟩, ?_, rfl⟩
      have h1 := hQnorm h⁻¹ (H'.inv_mem hh) w hw
      have hw' : w = h * ⟨y, hyC⟩ * h⁻¹ := Subtype.ext (by
        rw [show ((h * ⟨y, hyC⟩ * h⁻¹ : C t) : G) = (h : G) * y * (h : G)⁻¹ from rfl]
        exact hwy)
      rw [hw'] at h1
      simpa [mul_assoc] using h1
  · exact isCyclic_of_injective (H'.equivMapOfInjective _ (C t).subtype_injective).symm.toMonoidHom
      (MulEquiv.injective _)
  · apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_comap]
    have : x ∈ κ.ker := hD.ker_eq ▸ hx
    rw [MonoidHom.mem_ker] at this
    rw [this]
    exact Subgroup.one_mem _
  · rw [Subgroup.card_map_of_injective (C t).subtype_injective, hH'card, hKcard]

theorem not_four_dvd_card_centralizer {t : G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} (hD : UnitaryLocalData t p f F κ)
    (hinv : ∀ y : G, orderOf y = 2 → IsConj y t) {u : G} (hu1 : u ≠ 1)
    (hup : ∃ k : ℕ, orderOf u = p ^ k) : ¬ 4 ∣ Nat.card (Subgroup.centralizer {u}) := by
  classical
  intro h4
  have hp := hD.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, -, -, hNZcard⟩ := NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic
  obtain ⟨-, hCcard⟩ := unitaryLocalData_card hD
  obtain ⟨Q₀, hQcard, -, hQtr, -⟩ := exists_translation_sylow hD
  obtain ⟨k, hk⟩ := hup
  set Cu := Subgroup.centralizer ({u} : Set G)
  let R : Sylow 2 Cu := default
  have hR4 : 4 ∣ Nat.card R := by
    rw [Sylow.card_eq_multiplicity]
    have h2 : 2 ≤ (Nat.card Cu).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
        (by norm_num; exact h4)
    exact dvd_trans (by norm_num : 4 ∣ 2 ^ 2) (Nat.pow_dvd_pow 2 h2)
  have hRnt : Nontrivial (R : Subgroup Cu) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hR4
    omega
  have hZnt : Nontrivial (Subgroup.center (R : Subgroup Cu)) :=
    R.isPGroup'.center_nontrivial
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (R : Subgroup Cu)) 2
    (by
      obtain ⟨j, hj⟩ :=
        (R.isPGroup'.to_subgroup (Subgroup.center (R : Subgroup Cu))).exists_card_eq
      have h1 := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      rw [hj] at h1 ⊢
      rcases j with _ | j
      · simp at h1
      · exact dvd_pow_self 2 (Nat.succ_ne_zero j))
  set y' : G := (((y : (R : Subgroup Cu)) : Cu) : G)
  have hy'2 : orderOf y' = 2 := by
    rw [show y' = (((y : (R : Subgroup Cu)) : Cu) : G) from rfl, Subgroup.orderOf_coe,
      Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy2]
  obtain ⟨g, hg⟩ := isConj_iff.mp (hinv y' hy'2)
  have hyR : ∀ x : (R : Subgroup Cu), (x : G) * y' = y' * x := by
    intro x
    have := Subgroup.mem_center_iff.mp y.2 x
    exact congrArg (fun w : (R : Subgroup Cu) => ((w : Cu) : G)) this
  have huR : ∀ x : (R : Subgroup Cu), (x : G) * u = u * x := by
    intro x
    exact Subgroup.mem_centralizer_singleton_iff.mp (x : Cu).2
  have hu'C : g * u * g⁻¹ ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have h1 := huR y
    calc g * u * g⁻¹ * (g * y' * g⁻¹) = g * (u * y') * g⁻¹ := by group
      _ = g * (y' * u) * g⁻¹ := by rw [show u * y' = y' * u from (h1).symm]
      _ = g * y' * g⁻¹ * (g * u * g⁻¹) := by group
  set ū : C t := ⟨g * u * g⁻¹, hu'C⟩
  have hū1 : ū ≠ 1 := by
    intro h
    apply hu1
    have h' : g * u * g⁻¹ = 1 := congrArg Subtype.val h
    have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [this, h']
    group
  have hūk : ū ^ p ^ k = 1 := by
    apply Subtype.ext
    change (g * u * g⁻¹) ^ p ^ k = 1
    rw [conj_pow, ← hk, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hconjC : ∀ x : (R : Subgroup Cu), g * (x : G) * g⁻¹ ∈ C t := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * (x : G) * g⁻¹ * (g * y' * g⁻¹) = g * ((x : G) * y') * g⁻¹ := by group
      _ = g * (y' * x) * g⁻¹ := by rw [hyR x]
      _ = g * y' * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  obtain ⟨x, hx⟩ : ∃ x : (R : Subgroup Cu), (⟨g * (x : G) * g⁻¹, hconjC x⟩ : C t) ∉ NZ t := by
    by_contra hall
    push Not at hall
    let ψ : (R : Subgroup Cu) →* NZ t :=
      { toFun := fun x => ⟨⟨g * (x : G) * g⁻¹, hconjC x⟩, hall x⟩
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          apply Subtype.ext
          simp only [MulMemClass.coe_mul]
          group }
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h1 := congrArg (fun w : NZ t => ((w : C t) : G)) hab
      simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk] at h1
      apply Subtype.ext
      apply Subtype.ext
      exact mul_left_cancel (mul_right_cancel h1)
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    rw [hNZcard] at hdvd
    have h4' := hR4.trans hdvd
    obtain ⟨m, hm⟩ := hodd
    omega
  set v : C t := ⟨g * (x : G) * g⁻¹, hconjC x⟩
  have hvū : v * ū = ū * v := by
    apply Subtype.ext
    change g * (x : G) * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * (x : G) * g⁻¹)
    calc g * (x : G) * g⁻¹ * (g * u * g⁻¹) = g * ((x : G) * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [huR x]
      _ = g * u * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp R.isPGroup' x
  have hvj : v ^ 2 ^ j = 1 := by
    apply Subtype.ext
    change (g * (x : G) * g⁻¹) ^ 2 ^ j = 1
    rw [conj_pow]
    have : (x : G) ^ 2 ^ j = 1 := by
      rw [← hj, ← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe (x : Cu)]
      exact pow_orderOf_eq_one _
    rw [this, mul_one, mul_inv_cancel]
  have hfac : (Nat.card (C t)).factorization p = f := by
    rw [hCcard, show 2 * Nat.card (N t) * (p ^ f * ((p ^ f) ^ 2 - 1)) =
      p ^ f * (2 * Nat.card (N t) * ((p ^ f) ^ 2 - 1)) by ring]
    apply factorization_prime_pow_mul hp
    intro hdvd
    have hKp := (unitaryK_properties hD).2.2.1
    rw [(unitaryLocalData_card hD).1] at hKp
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact hKp h1
    · have hpq : p ∣ (p ^ f) ^ 2 :=
        dvd_pow (dvd_pow_self p (by have := hD.one_le; omega)) (by norm_num)
      have h2 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub hpq h1
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos hp.pos f))] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  let QS : Sylow p (C t) := Sylow.ofCard Q₀ (by rw [hQcard, hfac])
  have hūp : IsPGroup p (Subgroup.zpowers ū) := by
    apply IsPGroup.of_card (n := (orderOf ū).factorization p)
    rw [Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hūk)
    rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
  obtain ⟨P', hP'⟩ := hūp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (C t) P' QS
  have hcū : c * ū * c⁻¹ ∈ Q₀ := by
    have h1 : ū ∈ (P' : Subgroup (C t)) := hP' (Subgroup.mem_zpowers ū)
    have h2 := Subgroup.smul_mem_pointwise_smul ū (MulAut.conj c) (P' : Subgroup (C t)) h1
    rw [← Sylow.coe_subgroup_smul, hc] at h2
    exact h2
  obtain ⟨b, hb⟩ := hQtr _ hcū
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [translation_zero] at hb
    have hker : c * ū * c⁻¹ ∈ NZ t := by
      rw [← hD.ker_eq, MonoidHom.mem_ker, hb]
    have h1 : orderOf (c * ū * c⁻¹) ∣ 2 * Nat.card (N t) := by
      rw [← hNZcard]
      have := orderOf_dvd_natCard (⟨_, hker⟩ : NZ t)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (c * ū * c⁻¹) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [conj_pow, hūk, mul_one, mul_inv_cancel]
    have hKp := (unitaryK_properties hD).2.2.1
    rw [(unitaryLocalData_card hD).1] at hKp
    have hcop : Nat.Coprime (p ^ k) (2 * Nat.card (N t)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hKp)
    have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
    apply hū1
    have : ū = c⁻¹ * (c * ū * c⁻¹) * c := by group
    rw [this, h3]
    group
  have hcomm : κ (c * v * c⁻¹) * translation F b = translation F b * κ (c * v * c⁻¹) := by
    rw [← hb, ← map_mul, ← map_mul]
    congr 1
    calc c * v * c⁻¹ * (c * ū * c⁻¹) = c * (v * ū) * c⁻¹ := by group
      _ = c * (ū * v) * c⁻¹ := by rw [hvū]
      _ = c * ū * c⁻¹ * (c * v * c⁻¹) := by group
  have hrange : κ (c * v * c⁻¹) ∈ coordinateD F := hD.range_eq ▸ ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ := eq_translation_of_commute F hrange hb0 hcomm
  have hqodd : Odd (Nat.card F) := by
    rw [hD.card_field]
    exact (Nat.odd_iff.mpr (by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hD.ne_two
      · exact h)).pow
  have hodd' := odd_orderOf_translation hqodd b'
  rw [← hb'] at hodd'
  have h2pow : orderOf (κ (c * v * c⁻¹)) ∣ 2 ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, conj_pow, hvj, mul_one, mul_inv_cancel, map_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2pow
  have hone : orderOf (κ (c * v * c⁻¹)) = 1 := by
    rw [hi] at hodd' ⊢
    rcases i with _ | i
    · rfl
    · exfalso
      have h2 : 2 ∣ 2 ^ (i + 1) := dvd_pow_self 2 (Nat.succ_ne_zero i)
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)
  rw [orderOf_eq_one_iff] at hone
  apply hx
  have hvker : c * v * c⁻¹ ∈ NZ t := by
    rw [← hD.ker_eq, MonoidHom.mem_ker]
    exact hone
  have hcen := (NZ_facts hD.orderOf_t hD.core_central hD.core_cyclic).2.1 hvker
  have hvv : v = c * v * c⁻¹ := by
    have h1 := Subgroup.mem_center_iff.mp hcen c⁻¹
    calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
      _ = (c * v * c⁻¹) * c⁻¹ * c := by rw [h1]
      _ = c * v * c⁻¹ := by group
  change v ∈ NZ t
  rw [hvv]
  exact hvker
end CFSG.Semidihedral.UnitaryBranch
