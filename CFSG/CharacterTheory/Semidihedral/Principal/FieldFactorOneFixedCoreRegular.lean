module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCore
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreDegrees
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.RegularityInvertedOddFactor

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
open CFSG.Semidihedral.Principal.FreeSix CFSG.Semidihedral.StationaryConfinement

theorem actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n)))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥) :
    let s₀ : G := fS (s n)
    let Na : Subgroup G := (N t).map (C t).subtype
    let A₀ : Subgroup G := Na ⊓ Subgroup.centralizer {s₀}
    let qe : ℕ := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀})) : ℤ) ≤
      padicValNat p (Nat.card G) ∧
    (∀ x : G, x ∈ Na → s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ Na = A₀ ∧
    N t ≠ ⊥ ∧ IsCyclic (N t) ∧ Nat.card (N t) ∣ qe / 2 ∧ ¬ p ∣ Nat.card (N t) := by
  intro s₀ Na A₀ qe
  let : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have hts : t ≠ s₀ := fun h => hst h.symm
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have hSC : (S : Subgroup G) ≤ C t := sylow_le_centralizer_of_eq hn fS ht
  have htS : t ∈ (S : Subgroup G) := hz ▸ (fS (z n)).2
  have htZ : ∀ x ∈ (S : Subgroup G), x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hSC hx)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have hsS : s₀ ∈ (S : Subgroup G) := (fS (s n)).2
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hqodd : Odd (p ^ f) := hpodd.pow
  set V : Subgroup G := Subgroup.closure {t, s₀} with hVdef
  set D : Subgroup G := Subgroup.centralizer (V : Set G) with hDdef
  set M : Subgroup G := Subgroup.normalizer (V : Set G) with hMdef
  set K : Subgroup G := M ⊓ C t with hKdef
  obtain ⟨W, -, -, hWcard, -, -, ⟨eD, heD⟩, -, -, -, -, hsurj, -, -, hKD,
      ⟨d, hdK, hdD, -, -, -, -⟩, hMN, ⟨ω, hω1, hωW⟩, hall⟩ :=
    actual_field_factor_one_fixed_odd_core_gives_six_element_torus_character_orbit G hGnonab
      hrecognition n hn S fS t htS htZ ht1 s₀ hsS hs2 hst hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hcov hY hA₀
  have htsc : t * s₀ = s₀ * t := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hss : s₀ * s₀ = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hVK : IsKleinFour V :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s₀ ht2 hs2 hsC hts
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hsV : s₀ ∈ V := Subgroup.subset_closure (by simp)
  have hVS : V ≤ (S : Subgroup G) := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact hsS
  have hcTC : cT t = C t := StationaryOddLocalization.centralizer_zpowers_eq t
  have hsC' : s₀ ∈ cT t := hcTC ▸ hsC
  have hDmem : ∀ x : G, t * x = x * t → s₀ * x = x * s₀ → x ∈ dV V := fun x h1 h2 =>
    mem_centralizer_closure_pair_iff.mpr ⟨h1.symm, h2.symm⟩
  have hAD : ∀ a : A₀, (a : G) = (eD (1, a, 1) : G) := fun a => by rw [heD]; simp
  let ιE : A₀ × W →* G := D.subtype.comp (eD.toMonoidHom.comp (MonoidHom.inr V (A₀ × W)))
  have hιE : ∀ x : A₀ × W, ιE x = (x.1 : G) * x.2 := fun x => by
    change ((eD (1, x.1, x.2) : D) : G) = _
    rw [heD]
    simp
  have hιEinj : Function.Injective ιE := by
    intro x y hxy
    have h : eD (1, x.1, x.2) = eD (1, y.1, y.2) := Subtype.ext hxy
    have h' := eD.injective h
    simp only [Prod.mk.injEq, true_and] at h'
    exact Prod.ext h'.1 h'.2
  set E : Subgroup G := ιE.range with hEdef
  have hED : E ≤ dV V := by
    rintro _ ⟨x, rfl⟩
    exact (eD (1, x.1, x.2)).2
  have hVE : V ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, ⟨y, rfl⟩⟩
    have h1 : eD (⟨ιE y, hxV⟩, 1, 1) = eD (1, y.1, y.2) := by
      apply Subtype.ext
      rw [heD, heD]
      simp only [mul_one, one_mul, OneMemClass.coe_one]
      exact hιE y
    have h2 := congrArg Prod.fst (eD.injective h1)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  have hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e := by
    intro x hx
    obtain ⟨⟨v, a, w⟩, hvaw⟩ := eD.surjective ⟨x, hx⟩
    have h : (v : G) * a * w = x := by
      have h0 := congrArg Subtype.val hvaw
      rw [heD] at h0
      exact h0
    refine ⟨v, v.2, ιE (a, w), ⟨(a, w), rfl⟩, ?_⟩
    rw [hιE, ← h]
    exact mul_assoc _ _ _
  have hA₀odd : Odd (Nat.card A₀) := by
    have h1 : Nat.card A₀ ∣ Nat.card Na := Subgroup.card_dvd_of_le inf_le_left
    rw [Subgroup.card_map_of_injective (C t).subtype_injective] at h1
    exact hNodd.of_dvd_nat h1
  have hEodd : Odd (Nat.card E) := by
    rw [hEdef, ← Nat.card_congr (MonoidHom.ofInjective hιEinj).toEquiv, Nat.card_prod]
    exact hA₀odd.mul (hWcard ▸ odd_half_torusOrder hqodd)
  have hdC : d ∈ C t := hdK.2
  have hdM : d ∈ M := hdK.1
  have hds : d * s₀ * d⁻¹ = t * s₀ := by
    have hmem : d * s₀ * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdM s₀).mp hsV
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    rcases mem_closure_pair_cases htsc htt hss hmem with h | h | h | h
    · exfalso
      have : s₀ = 1 := by
        calc s₀ = d⁻¹ * (d * s₀ * d⁻¹) * d := by group
          _ = 1 := by rw [h]; group
      rw [show (fS (s n) : G) = 1 from this, orderOf_one] at hs2
      omega
    · exfalso
      apply hst
      calc s₀ = d⁻¹ * (d * s₀ * d⁻¹) * d := by group
        _ = d⁻¹ * (t * d) := by rw [h, mul_assoc]
        _ = t := by rw [← hdt]; group
    · exfalso
      apply hdD
      apply hDmem
      · exact hdt.symm
      · calc s₀ * d = (d * s₀ * d⁻¹) * d := by rw [h]
          _ = d * s₀ := by group
    · exact h
  have hdC' : d ∈ cT t := hcTC ▸ hdC
  have hK' : ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ d⁻¹ * x ∈ dV V := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · right
      have hxK : x ∈ K := ⟨hx.2, hcTC ▸ hx.1⟩
      have hidx : (D.subgroupOf K).index = 2 := hKD
      have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨d, hdK⟩⁻¹) (b := ⟨x, hxK⟩)).mpr
      have hmem : (⟨d, hdK⟩⁻¹ * ⟨x, hxK⟩ : K) ∈ D.subgroupOf K := by
        apply h
        simp only [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
        exact iff_of_false hdD hxD
      exact hmem
  have hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1 := fun x hx =>
    hω1 x (Subgroup.mem_sup_left hx)
  have hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) →
      m ∈ dV V := by
    intro m hm hst'
    have hconj : conjugateLinearCharacter ⟨m, hMN hm⟩ ω = ω := by
      refine MonoidHom.ext fun x => ?_
      rw [conjugateLinearCharacter_apply]
      exact hst' x _ rfl
    exact ((hall ω hω1 hωW).2.1 ⟨m, hMN hm⟩ hm).mp hconj
  obtain ⟨-, hZS⟩ := central_involution_facts hn S fS htS htZ ht1
  have hZ' : ∀ x : (S : Subgroup G),
      x ∈ Subgroup.center (S : Subgroup G) ↔ (x : G) ∈ Subgroup.zpowers t := by
    intro x
    rw [← hZS, Subgroup.mem_center_iff]
    constructor
    · intro h
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact congrArg Subtype.val (h ⟨y, hy⟩)
    · rintro ⟨-, hx⟩ y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
  obtain ⟨hfour, -⟩ := free_six_semidihedral_hypotheses V hVK t htV S hVS hn fS hZ'
  have hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y := fun x y hx hy =>
    (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG x hx).trans
      (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG y hy).symm
  let eC : C t ≃* cT t := MulEquiv.subgroupCongr hcTC.symm
  have hclasses : ∀ w : cT t, orderOf w = 2 →
      IsConj w ⟨t, element_mem_centralizer_zpowers t⟩ ∨ IsConj w ⟨s₀, hsC'⟩ := by
    intro w hw
    have hw' : orderOf (eC.symm w) = 2 := by rw [MulEquiv.orderOf_eq]; exact hw
    have hwG : orderOf ((eC.symm w : C t) : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw'
    rcases (isConj_centered_involution_iff hn S fS hG fS hcent (eC.symm w)).mp
        (hinv _ _ hwG ht2) with h | h
    · left
      have h' : w = eC (tInC t) := by rw [← h, MulEquiv.apply_symm_apply]
      rw [h']
      exact IsConj.refl _
    · right
      have h' := eC.toMonoidHom.map_isConj h
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h'
      exact h'
  obtain ⟨-, -, -, -, -, -, hdeg, -⟩ :=
    actual_field_factor_one_fixed_core_defect_four_degrees_coprime G hGnonab hrecognition n hn S
      fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀
  have hSn : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n (by omega)]
  have h2n : 2 ^ n ∣ Nat.card (cT t) := hcTC ▸ hSn ▸ Subgroup.card_dvd_of_le hSC
  have hv2 : n ≤ padicValNat 2 (Nat.card (cT t)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h2n
  have hcardV : Nat.card (V.subgroupOf (cT t)) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_cT hVK htV)).toEquiv, hVK.card_four]
    rfl
  have hpdeg : ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
      (basisC : FiniteIrreducibleCharacterBasis (cT t)) (label : basisC.index),
      coefficientBlockDefect basisC ideal 2 label (V.subgroupOf (cT t)) →
      ∀ θ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) label,
        ¬ p ∣ Module.finrank ℂ (basisC.representation θ).vector := by
    intro ideal _ _ basisC label hD θ hθ
    obtain ⟨-, -, hall2⟩ :=
      block_class_defect_witness_character_degree_dvd basisC ideal 2 label _ hD
    obtain ⟨-, hdvd⟩ := hall2 2 hcardV
    have h4 : 4 ∣ Module.finrank ℂ (basisC.representation θ).vector :=
      (pow_dvd_pow 2 (show 2 ≤ padicValNat 2 (Nat.card (cT t)) - 2 by omega)).trans
        (hdvd θ hθ)
    have hirr : (basisC.representation θ).character ∘ eC ∈ CFSG.BlocksIrr (C t) :=
      blocksIrr_comp_mulEquiv eC ⟨(basisC.representation θ).vector, inferInstance,
        inferInstance, inferInstance, (basisC.representation θ).representation,
        basisC.irreducible θ, rfl⟩
    refine hdeg _ hirr _ ?_ h4
    change (basisC.representation θ).character (eC 1) = _
    rw [map_one]
    exact Representation.char_one _
  have hcl := closure_pair_cT_eq_subgroupOf hsC'
  have hval0 := three_local_blocks_valuation hVK htV hsV ht1 ht2 hs2 hst hsC' hcl hDmem hED hVE
    hDVE hEodd hdC' hdM hds hK' hsurj hfour ω hωV hωstab hinv hclasses p hp hpdeg
  have hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
      2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {s₀})) : ℤ) ≤
        padicValNat p (Nat.card G) := by
    rw [card_centralizer_cT t s₀ hsC', hcTC] at hval0
    exact hval0
  obtain ⟨U, -, hUmem, -, hUN, -, -, -, -, -, -, -, hUnorm, hA₀cyc, hA₀dvd, -, -, -, -, -, -, -,
      -, -⟩ :=
    stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action G
      hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC hts hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hcov
  obtain ⟨-, hconf, -, -⟩ :=
    stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element G hGnonab
      hrecognition n hn S fS t s₀ ht2 hs2 hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel
      hcov
  have hNamem : ∀ x : G, x ∈ Na ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨⟨x, hx⟩, hxN, rfl⟩
  have hU : ∀ x : G, x ∈ U ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t ∧
      (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹ := by
    intro x
    rw [hUmem, hNamem]
    constructor
    · rintro ⟨⟨hx, hxN⟩, hxs⟩
      exact ⟨hx, hxN, hxs⟩
    · rintro ⟨hx, hxN, hxs⟩
      exact ⟨⟨hx, hxN⟩, hxs⟩
  have hCNa : C t ≤ Subgroup.normalizer (Na : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (inferInstance : (N t).Normal).conj_mem y hy ⟨c, hc⟩, rfl⟩
  have hUnormal : (U.subgroupOf (C t)).Normal := by
    constructor
    intro x hx c
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc := hUnorm (hCNa c.2)
    exact (Subgroup.mem_normalizer_iff.mp hc x).mp hx
  have hconfU : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ C t := fun u hu hu1 =>
    hconf u (hUN hu) hu1
  obtain ⟨-, -, hUbot, hNs⟩ :=
    regularity_eliminates_confined_normal_inverted_odd_factor hG n hn S fS t ht hnonab hcentral
      hnc p f hp hpodd hf hmodel hval U hU hUnormal hconfU
  have hNaA : Na = A₀ := by
    apply le_antisymm _ inf_le_left
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (hNs y hy).symm⟩
  have hcardN : Nat.card (N t) = Nat.card A₀ := by
    rw [← hNaA]
    exact (Subgroup.card_map_of_injective (C t).subtype_injective).symm
  refine ⟨hval, fun x hx hxs => ?_, hNaA, ?_, ?_, hcardN ▸ hA₀dvd, ?_⟩
  · have hxU : x ∈ U := (hUmem x).mpr ⟨hx, hxs⟩
    rw [hUbot] at hxU
    exact Subgroup.mem_bot.mp hxU
  · intro hN
    apply hA₀
    change A₀ = ⊥
    rw [← hNaA]
    change (N t).map (C t).subtype = ⊥
    rw [hN, Subgroup.map_bot]
  · have hNacyc : IsCyclic Na := hNaA ▸ hA₀cyc
    have e := (N t).equivMapOfInjective (C t).subtype (C t).subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · rw [hcardN]
    intro h
    exact not_dvd_half_torusOrder hp (dvd_pow_self p (by omega)) hqodd (h.trans hA₀dvd)

end CFSG.Semidihedral.Principal
