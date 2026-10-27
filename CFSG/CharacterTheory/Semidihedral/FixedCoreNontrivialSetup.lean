module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialModel
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactor
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGL2TorusCentralizer

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action)

theorem pPrimeCore_map_congr {G : Type*} [Group G] {D₁ D₂ : Subgroup G} (h : D₁ = D₂) :
    (CFSG.pPrimeCore 2 D₁).map D₁.subtype = (CFSG.pPrimeCore 2 D₂).map D₂.subtype := by
  subst h
  rfl

theorem trivial_fixed_core_local_data
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥) :
    let q : ℕ := p ^ f
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let B : Subgroup G := (N t).map (C t).subtype
    ∃ (J : Subgroup G) (d : G), LocalData t s₀ d J B W ∧
      Nat.card (C t) = 2 * Nat.card B * q * (q ^ 2 - 1) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
        Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      V ⊔ W = D ∧ Nat.card W = (if q % 4 = 1 then q + 1 else q - 1) / 2 := by
  intro q s₀ V D W B
  classical
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have hq5 : 5 ≤ p ^ f := by omega
  have hq5' : 5 < p ^ f := by omega
  have hcov' := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage
    t s₀ hcov
  set sC : C t := ⟨s₀, hsC⟩ with hsCdef
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hts : t ≠ s₀ := fun h => hst h.symm
  set ι : C t →* G := (C t).subtype with hιdef
  have hιinj : Function.Injective ι := (C t).subtype_injective
  obtain ⟨Wa, hWamem, hWacyc, hWacard, -, -, -, hWaRY, -, ⟨d, hdJ, hd4, hd2, hds, hdW⟩, hCV,
      -, -⟩ :=
    StationaryConfinement.fixed_factor_ambient_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp
      hpodd hf hq5 hmodel hcov' s₀ hsC hs2 hts
  obtain ⟨⟨-, hJY, hJN, -, -⟩, hJn, htJ, hYJN, h9, -⟩ :=
    Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S fS hG t ht2
      hnonab hcentral hnc p f hp hpodd hf hq5 hmodel (Or.inl hcov')
  obtain ⟨hE, ⟨φ, -⟩, ⟨F, hF, hFfin, hFcard, ⟨η⟩⟩, ⟨μ, hμ⟩⟩ := h9 (by omega)
  set Yi : Subgroup (C t) := ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)
    with hYidef
  set H₀ : Subgroup (C t) := Yi ⊓ Subgroup.centralizer (N t : Set (C t)) with hH₀def
  set Ji : Subgroup (C t) := (CFSG.perfectResidual H₀).map H₀.subtype with hJidef
  set J : Subgroup G := Ji.map ι with hJdef
  obtain ⟨U, -, hUmem, -, -, hUcomm, -, -, -, hUA, -⟩ :=
    stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action
      G hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC hts hnonab hcentral hnc p f hp hpodd hf
      hq5' hmodel hcov
  have hA₀' : (N t).map ι ⊓ Subgroup.centralizer {s₀} = ⊥ := hA₀
  have hUeq : U = B := by
    have h : U ⊔ ((N t).map ι ⊓ Subgroup.centralizer {s₀}) = (N t).map ι := hUA
    rw [hA₀', sup_bot_eq] at h
    exact h
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rw [← hUeq] at hx hy
    exact congrArg Subtype.val (hUcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBinv : ∀ x ∈ B, s₀ * x * s₀⁻¹ = x⁻¹ := by
    intro x hx
    rw [← hUeq] at hx
    exact ((hUmem x).mp hx).2
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hNoddx : ∀ z ∈ N t, Odd (orderOf z) := fun z hz =>
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (N t) hz)
  have hJNcomm : ∀ x ∈ Ji, ∀ y ∈ N t, x * y = y * x := by
    intro x hx y hy
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN hx
    exact (Subgroup.mem_centralizer_iff.mp h y hy).symm
  have hJNdisj : Ji ⊓ N t = ⊥ := hE
  have hYmem : ∀ y ∈ Yi, ∃ x ∈ Ji, ∃ z ∈ N t, y = x * z := fun y hy =>
    exists_mul_of_mem_sup hJNcomm (hYJN ▸ hy)
  have hCcard : Nat.card (C t) = 2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1) := by
    have h1 := Yi.card_mul_index
    rw [hY] at h1
    have h2 : Nat.card Yi = Nat.card Ji * Nat.card (N t) := by
      rw [← Nat.card_congr μ.toEquiv, Nat.card_prod]
    have h3 : Nat.card Ji = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr η.toEquiv,
        CFSG.GorensteinWalter.sl2_card_formula, hFcard]
    rw [← h1, h2, h3]
    ring
  have h2F : (2 : F) ≠ 0 :=
    CFSG.GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hFcard]; exact hpodd.pow)
  have hJinv : ∀ x ∈ Ji, x * x = 1 → x = 1 ∨ x = tInC t := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have ho : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
      have hot : orderOf (tInC t) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact ht2
      have h1 : (φ.trans η) ⟨x, hx⟩ = OddFieldSL2.minusIdentity F :=
        (OddFieldSL2.orderOf_eq_two_iff F h2F _).mp
          (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ho])
      have h2 : (φ.trans η) ⟨tInC t, htJ⟩ = OddFieldSL2.minusIdentity F :=
        (OddFieldSL2.orderOf_eq_two_iff F h2F _).mp
          (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hot])
      exact congrArg Subtype.val ((φ.trans η).injective (h1.trans h2.symm))
  have hsC2' : sC * sC = 1 := by rw [← pow_two, ← hsC2, pow_orderOf_eq_one]
  have hsY : sC ∉ Yi := by
    intro hsYi
    obtain ⟨x, hx, z, hz, hxz⟩ := hYmem sC hsYi
    have hcomm := hJNcomm x hx z hz
    have h1 : x * x * (z * z) = 1 := by
      calc x * x * (z * z) = x * (x * z) * z := by group
        _ = x * (z * x) * z := by rw [hcomm]
        _ = x * z * (x * z) := by group
        _ = 1 := by rw [← hxz, hsC2']
    have hxx : x * x ∈ Ji ⊓ N t := by
      refine Subgroup.mem_inf.mpr ⟨Ji.mul_mem hx hx, ?_⟩
      have : x * x = (z * z)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (N t).inv_mem ((N t).mul_mem hz hz)
    rw [hJNdisj, Subgroup.mem_bot] at hxx
    have hzz : z * z = 1 := by rw [hxx, one_mul] at h1; exact h1
    have hz1 := eq_one_of_mul_self_eq_one_of_odd (hNoddx z hz) hzz
    rw [hz1, mul_one] at hxz
    rcases hJinv x hx hxx with h | h
    · rw [h] at hxz
      rw [hxz, orderOf_one] at hsC2
      exact absurd hsC2 (by decide)
    · exact hsCt (hxz.trans h)
  have hVcl : Subgroup.closure ({t, s₀} : Set G) = V :=
    StationaryOddLocalization.closure_pair_eq_zpowers_sup t s₀
  have hDeq : D = C t ⊓ Subgroup.centralizer ({s₀} : Set G) := by
    rw [← StationaryConfinement.centralizer_closure_pair t s₀, hVcl]
  have hWR : W = (CFSG.pPrimeCore 2 (C t ⊓ Subgroup.centralizer ({s₀} : Set G) :
      Subgroup G)).map (C t ⊓ Subgroup.centralizer ({s₀} : Set G)).subtype :=
    pPrimeCore_map_congr hDeq
  have hRY : W ≤ Yi.map ι := by
    rw [hWR]
    rintro _ ⟨x, hx, rfl⟩
    have hodd : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe]
      exact (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2)
        (G := (C t ⊓ Subgroup.centralizer ({s₀} : Set G) : Subgroup G)))).of_dvd_nat
          (Subgroup.orderOf_dvd_natCard _ hx)
    have hxC : (x : G) ∈ C t := (Subgroup.mem_inf.mp x.2).1
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    apply mem_of_index_two_of_odd hY
    rw [← Subgroup.orderOf_mk] at hodd
    exact hodd
  have hWWa : W = Wa := by
    have h : Wa ⊔ ((N t).map ι ⊓ Subgroup.centralizer {s₀}) =
        (CFSG.pPrimeCore 2 (C t ⊓ Subgroup.centralizer ({s₀} : Set G) : Subgroup G)).map
          (C t ⊓ Subgroup.centralizer ({s₀} : Set G)).subtype ⊓ Yi.map ι := hWaRY
    rw [hA₀', sup_bot_eq, ← hWR, inf_eq_left.mpr hRY] at h
    exact h.symm
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hs2' : orderOf s₀ = 2 := hs2
  have hs1 : s₀ * s₀ = 1 := by rw [← pow_two, ← hs2', pow_orderOf_eq_one]
  have ht1' : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; exact absurd ht2 (by decide)
  have hs1' : s₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hs2'; exact absurd hs2' (by decide)
  have htsc : Commute t s₀ := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hJle : J ≤ C t := Subgroup.map_subtype_le Ji
  have hBle : B ≤ C t := Subgroup.map_subtype_le (N t)
  have hWD : W ≤ D := Subgroup.map_subtype_le _
  have htJ' : t ∈ J := ⟨tInC t, htJ, rfl⟩
  have hDV : V ⊔ W = D := by
    have h : Subgroup.centralizer (Subgroup.closure ({t, s₀} : Set G) : Set G) =
        Subgroup.closure ({t, s₀} : Set G) ⊔
          (CFSG.pPrimeCore 2 (C t ⊓ Subgroup.centralizer ({s₀} : Set G) : Subgroup G)).map
            (C t ⊓ Subgroup.centralizer ({s₀} : Set G)).subtype := hCV
    rw [hVcl, ← hWR] at h
    exact h.symm
  have hWcard : Nat.card W = (if q % 4 = 1 then q + 1 else q - 1) / 2 := by
    rw [hWWa]
    exact hWacard
  have hWmem : ∀ x, x ∈ W ↔ x ∈ J ∧ x * s₀ = s₀ * x ∧ Odd (orderOf x) := by
    intro x
    rw [hWWa, hWamem]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, Subgroup.mem_centralizer_singleton_iff.mp h2, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨⟨h1, Subgroup.mem_centralizer_singleton_iff.mpr h2⟩, h3⟩⟩
  have hA₀i : N t ⊓ Subgroup.centralizer ({sC} : Set (C t)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ι z ∈ (N t).map ι ⊓ Subgroup.centralizer {s₀} := by
      refine ⟨⟨z, hz.1, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
    rw [hA₀', Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (hιinj (by rw [hz', map_one]))
  have hcentW : ∀ w ∈ W, w ≠ 1 → ∀ x ∈ J, x * w = w * x → x * s₀ = s₀ * x := by
    intro w hw hw1 x hx hxw
    obtain ⟨xi, hxi, rfl⟩ := hx
    have hamb := (ActualFourGroupCentralizer.original_ambient_subgroups sC).1
    have hWR' : W = ((CFSG.pPrimeCore 2 (ActualFourGroupCentralizer.D sC)).map
        (ActualFourGroupCentralizer.D sC).subtype).map ι := by
      rw [hWR, ← StationaryConfinement.ambient_core_of_subgroup_map (C t)
        (ActualFourGroupCentralizer.D sC)]
      exact pPrimeCore_map_congr hamb.symm
    rw [hWR'] at hw
    obtain ⟨y, ⟨r, hr, rfl⟩, rfl⟩ := hw
    have hrR : r ∈ ActualFourGroupCentralizer.R sC := by
      show r ∈ CFSG.piCore KleinFourOddKernel.oddPrimes (ActualFourGroupCentralizer.D sC)
      rw [KleinFourOddKernel.piCore_odd_eq_pPrimeCore]
      exact hr
    have hne : (⟨r, hrR⟩ : ActualFourGroupCentralizer.R sC) ≠ 1 := by
      intro h
      have hr1 : r = 1 := congrArg Subtype.val h
      exact hw1 (by rw [hr1, map_one, map_one])
    have hcomm : xi * (r : C t) = (r : C t) * xi := Subtype.ext hxw
    have hnu := commute_s_mod_N_of_commute_odd_core n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel hCcard sC hsC2 hsCt hA₀i ⟨r, hrR⟩ hne xi hcomm
    have hk : xi * sC * xi⁻¹ * sC⁻¹ ∈ Ji ⊓ N t := by
      refine ⟨?_, ?_⟩
      · have h1 : sC * xi⁻¹ * sC⁻¹ ∈ Ji := hJn.conj_mem _ (Ji.inv_mem hxi) sC
        have h2 : xi * sC * xi⁻¹ * sC⁻¹ = xi * (sC * xi⁻¹ * sC⁻¹) := by group
        rw [h2]
        exact Ji.mul_mem hxi h1
      · have h1 : nu t (xi * sC * xi⁻¹ * sC⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hnu]
          group
        exact (QuotientGroup.eq_one_iff _).mp h1
    rw [hJNdisj, Subgroup.mem_bot] at hk
    have hc : xi * sC = sC * xi := by
      calc xi * sC = xi * sC * xi⁻¹ * sC⁻¹ * (sC * xi) := by group
        _ = sC * xi := by rw [hk, one_mul]
    exact congrArg Subtype.val hc
  have hcover : ∀ c ∈ C t, ∃ x ∈ J, ∃ y ∈ B, c = x * y ∨ c = x * y * s₀ := by
    intro c hc
    by_cases hcY : (⟨c, hc⟩ : C t) ∈ Yi
    · obtain ⟨x, hx, z, hz, hxz⟩ := hYmem _ hcY
      exact ⟨ι x, ⟨x, hx, rfl⟩, ι z, ⟨z, hz, rfl⟩, Or.inl (congrArg Subtype.val hxz)⟩
    · have hcs : (⟨c, hc⟩ : C t) * sC ∈ Yi :=
        (Subgroup.mul_mem_iff_of_index_two hY).mpr (iff_of_false hcY hsY)
      obtain ⟨x, hx, z, hz, hxz⟩ := hYmem _ hcs
      refine ⟨ι x, ⟨x, hx, rfl⟩, ι z, ⟨z, hz, rfl⟩, Or.inr ?_⟩
      have h : (⟨c, hc⟩ : C t) = x * z * sC := by
        rw [← hxz, mul_assoc, hsC2', mul_one]
      exact congrArg Subtype.val h
  have hoddmem : ∀ c ∈ C t, Odd (orderOf c) → c ∈ J ⊔ B := by
    intro c hc hodd
    have hcY : (⟨c, hc⟩ : C t) ∈ Yi := by
      apply mem_of_index_two_of_odd hY
      rw [Subgroup.orderOf_mk]
      exact hodd
    obtain ⟨x, hx, z, hz, hxz⟩ := hYmem _ hcY
    have hc' : c = ι x * ι z := congrArg Subtype.val hxz
    rw [hc']
    exact Subgroup.mul_mem_sup ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩
  have hCJs : ∀ x ∈ J, x * s₀ = s₀ * x → x ∈ Subgroup.zpowers t ⊔ W := by
    intro x hxJ hxs
    have hxD : x ∈ D := by
      rw [hDeq]
      exact ⟨hJle hxJ, Subgroup.mem_centralizer_singleton_iff.mpr hxs⟩
    rw [← hDV] at hxD
    have hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
      Subgroup.mem_centralizer_iff.mp (hWD hw) v hv
    obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup hVW hxD
    have hts' : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers s₀, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Commute.zpow_zpow htsc i j
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hts' hv
    have hwJ : w ∈ J := ((hWmem w).mp hw).1
    have haJ : a ∈ J := by
      rcases zpowers_cases_of_mul_self ht1 a ha with h | h
      · rw [h]
        exact J.one_mem
      · rw [h]
        exact htJ'
    rcases zpowers_cases_of_mul_self hs1 b hb with h | h
    · rw [h, mul_one]
      exact Subgroup.mul_mem_sup ha hw
    · exfalso
      have hbJ : b ∈ J := by
        have h2 : b = a⁻¹ * (a * b * w) * w⁻¹ := by group
        rw [h2]
        exact J.mul_mem (J.mul_mem (J.inv_mem haJ) hxJ) (J.inv_mem hwJ)
      rw [h] at hbJ
      obtain ⟨y, hy, hy'⟩ := hbJ
      apply hsY
      have h3 : y = sC := Subtype.ext hy'
      rw [← h3]
      exact hJY hy
  have hBcard : Nat.card B = Nat.card (N t) := Subgroup.card_map_of_injective hιinj
  refine ⟨J, d, ?_, by rw [hBcard]; exact hCcard,
    ⟨F, hF, hFfin, hFcard, ⟨(Ji.equivMapOfInjective ι hιinj).symm.trans (φ.trans η)⟩⟩,
    hDV, hWcard⟩
  exact
    { t_sq := ht1
      t_ne_one := ht1'
      s_sq := hs1
      s_ne := hst
      s_ne_one := hs1'
      ts := htsc
      J_le := hJle
      J_conj := by
        intro c hc x hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hJn.conj_mem y hy ⟨c, hc⟩, rfl⟩
      t_mem := htJ'
      J_inv := by
        intro x hx hx2
        obtain ⟨y, hy, rfl⟩ := hx
        have hy2 : y * y = 1 := hιinj (by rw [map_mul, map_one]; exact hx2)
        rcases hJinv y hy hy2 with h | h
        · left
          rw [h, map_one]
        · right
          rw [h]
          rfl
      B_le := hBle
      B_conj := by
        intro c hc x hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y hy ⟨c, hc⟩, rfl⟩
      B_comm := hBcomm
      B_odd := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        show Odd (orderOf (y : G))
        rw [Subgroup.orderOf_coe]
        exact hNoddx y hy
      JB_comm := by
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact congrArg Subtype.val (hJNcomm a ha b hb)
      JB_disj := by
        rw [eq_bot_iff]
        rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
        have hab' : b = a := hιinj hab
        subst hab'
        have hb' : b ∈ Ji ⊓ N t := ⟨ha, hb⟩
        rw [hJNdisj, Subgroup.mem_bot] at hb'
        exact Subgroup.mem_bot.mpr (by rw [hb', map_one])
      s_inv := hBinv
      cover := hcover
      odd_mem := hoddmem
      W_mem := hWmem
      W_cyclic := hWWa ▸ hWacyc
      CJs := hCJs
      d_mem := hdJ
      d_sq := by rw [← pow_two]; exact hd2
      d_s := hds
      d_inv := hWWa ▸ hdW
      cent_W := hcentW }

end CFSG.Semidihedral.FixedCoreNontrivial
