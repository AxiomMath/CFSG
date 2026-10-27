module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterData
public import CFSG.CharacterTheory.Semidihedral.Principal.ConfinedInvertedOddSubgroup
public import CFSG.CharacterTheory.Semidihedral.Principal.RegularityInvertedOddFactor
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierLinear
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialDGroup
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialSetup
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusBasic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element)

theorem card_map_mul_card_ker_subgroupOf {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (A : Subgroup X) :
    Nat.card (A.map f) * Nat.card (f.ker.subgroupOf A) = Nat.card A := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.domRestrict A).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  exact h1.symm

theorem exists_conj_eq_of_isKleinFour {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (V : Subgroup G)
    (hVS : V ≤ (S : Subgroup G)) (hV : IsKleinFour V) (T : Subgroup G) (hT : IsKleinFour T) :
    ∃ g : G, T.map (MulAut.conj g).toMonoidHom = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hTp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S S'
  have hT'S : T.map (MulAut.conj h⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : x ∈ ((h • S : Sylow 2 G) : Subgroup G) := hh ▸ hS' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
    simpa [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, MulAut.conj_apply] using hxS
  have : IsKleinFour T := hT
  have : IsKleinFour V := hV
  have : IsKleinFour (T.map (MulAut.conj h⁻¹).toMonoidHom) :=
    isKleinFour_of_mulEquiv (T.equivMapOfInjective _ (MulAut.conj h⁻¹).injective)
  obtain ⟨g, -, hg⟩ := CFSG.Semidihedral.Local.kleinFour_conj_in_sylow hn S fS V _ hVS hT'S
  refine ⟨g⁻¹ * h⁻¹, ?_⟩
  have hcomp : (MulAut.conj (g⁻¹ * h⁻¹)).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply]
    group
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.id_apply]
    group
  rw [hcomp, ← Subgroup.map_map, hg, Subgroup.map_map, hid, Subgroup.map_id]

theorem exists_equalParameterData
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
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
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥)
    (hN : N t ≠ ⊥) (d : G) (F' : Type) [Field F'] [Finite F']
    (φ : torusH G t (fS (s n) : G) ⧸ CFSG.pPrimeCore 2 (torusH G t (fS (s n) : G)) ≃*
      CFSG.GorensteinWalter.PGL2 F')
    (hcl : TorusNormalizerClauses G t (fS (s n) : G) d (p ^ f) F' φ)
    (hq' : Nat.card F' = p ^ f) :
    ∃ (d₁ : G) (J : Subgroup G) (F : Type) (_ : Field F) (_ : Finite F)
      (κ : C t →* Equiv.Perm (Omega F)),
      EqualParameterData G t (fS (s n) : G) d d₁ J p f F κ F' φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite G
  obtain ⟨hzt, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  set s₀ : G := (fS (s n) : G) with hs₀def
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  set B : Subgroup G := (N t).map (C t).subtype with hBdef
  obtain ⟨JL, d₁, hL, hCcard, hsl2, hDV, hWcard⟩ := trivial_fixed_core_local_data G hGnonab
    hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀
  have hBne : B ≠ ⊥ := fun hbot =>
    hN ((Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp hbot)
  have hBodd : Odd (Nat.card B) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hconf : ∀ u ∈ B, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ C t :=
    (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element G hGnonab
      hrecognition n hn S fS t s₀ ht2 hs2 hsC (fun h => hst h.symm) hnonab hcentral hnc p f hp
      hpodd hf (by omega) hmodel hcov).2.1
  have hBnormal : (B.subgroupOf (C t)).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    push_cast
    exact hL.B_conj c c.2 x hx
  have hCI := Principal.confined_normal_inverted_odd_subgroup_primes_do_not_divide_centralizer_index
    n hn S fS t ht B (Subgroup.map_subtype_le _) hBodd hBnormal hL.s_inv hconf
  have hSC : (S : Subgroup G) ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
  have hV : IsKleinFour V := Principal.supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have hsurj : Function.Surjective V.normalizerMonoidHom := MonoidHom.range_eq_top.mp
    ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS hV).1
  obtain ⟨F, hFf, hFfin, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hA1 : Nat.card A = 1 :=
    SimpleLayerFrontier.field_group_card_eq_one_of_index_two n hn S fS hG t ht2 hnonab p f F A
      rho data hY
  have hAbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A hA1
  have hlift : SemilinearOddExtensions.liftedField F A = ⊥ := by
    rw [SemilinearOddExtensions.liftedField, hAbot, Subgroup.map_bot]
  set κ : C t →* Equiv.Perm (Omega F) := localAction F rho with hκdef
  have hker : κ.ker = NZ t := by
    have hk := permutationCover_kernel F A rho data.faithful data.full_image
    ext c
    rw [MonoidHom.mem_ker, ← hk, MonoidHom.mem_ker, ← permutationCover_value F A rho
      data.full_image c]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hrange : κ.range = coordinateD F := by
    have hk : (kappa t).range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    change ((coordinateE F).subtype.comp (rho.comp (kappa t))).range = coordinateD F
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hk, ← MonoidHom.range_eq_map,
      data.full_image, OddFieldLift.Gamma, hlift, sup_bot_eq,
      SemilinearOddExtensions.linearLayer, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (coordinateD_le_E F)]
  have hKmap : (K t).map κ = coordinateG F := by
    have h1 : (K t).map κ = (((K t).map (kappa t)).map rho).map (coordinateE F).subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1]
    change ((ActualSimpleLayerLocalPackage.J t).map rho).map (coordinateE F).subtype = _
    rw [data.residual_image, OddFieldLift.SpecialGamma, hlift, sup_bot_eq,
      SemilinearOddExtensions.specialLayer, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((coordinateG_le_D F).trans (coordinateD_le_E F))]
  have hKle : (K t).map κ ≤ (JL.subgroupOf (C t)).map κ := by
    rw [K_eq_odd_order_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hcJB : (c : G) ∈ JL ⊔ B := hL.odd_mem c c.2 (by
      show Odd (orderOf (c : G))
      rw [Subgroup.orderOf_coe]
      exact hc)
    obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup hL.JB_comm hcJB
    obtain ⟨b', hb', rfl⟩ := hb
    have hjC : j ∈ C t := hL.J_le hj
    have hc' : c = ⟨j, hjC⟩ * b' := Subtype.ext hjb
    refine ⟨⟨j, hjC⟩, hj, ?_⟩
    have hb'κ : κ b' = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact (le_sup_left : N t ≤ NZ t) hb'
    rw [hc', map_mul, hb'κ, mul_one]
  have hFodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hpodd, hf, data.field_card⟩
  have hGcard : Nat.card (coordinateG F) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [← Nat.card_congr (pslEquivCoordinateG F).toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula F hFodd, data.field_card]
  have hJcard : Nat.card (JL.subgroupOf (C t)) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.J_le).toEquiv]
    obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := hsl2
    rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF₀]
  have htJ : tInC t ∈ JL.subgroupOf (C t) := hL.t_mem
  have hker2 : 2 ≤ Nat.card (κ.ker.subgroupOf (JL.subgroupOf (C t))) := by
    have hne : κ.ker.subgroupOf (JL.subgroupOf (C t)) ≠ ⊥ := by
      intro hbot
      have hmem : (⟨tInC t, htJ⟩ : JL.subgroupOf (C t)) ∈
          κ.ker.subgroupOf (JL.subgroupOf (C t)) := by
        rw [Subgroup.mem_subgroupOf, hker]
        exact (le_sup_right : Z t ≤ NZ t) (Subgroup.mem_zpowers _)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hL.t_ne_one (congrArg (fun x : JL.subgroupOf (C t) => ((x : C t) : G)) hmem)
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hJmap : Nat.card ((JL.subgroupOf (C t)).map κ) ≤ Nat.card (coordinateG F) := by
    have h1 := card_map_mul_card_ker_subgroupOf κ (JL.subgroupOf (C t))
    rw [hJcard] at h1
    rw [hGcard, Nat.le_div_iff_mul_le (by norm_num)]
    calc Nat.card ((JL.subgroupOf (C t)).map κ) * 2 ≤
        Nat.card ((JL.subgroupOf (C t)).map κ) *
          Nat.card (κ.ker.subgroupOf (JL.subgroupOf (C t))) := Nat.mul_le_mul_left _ hker2
      _ = p ^ f * ((p ^ f) ^ 2 - 1) := h1
  have hlayer : (JL.subgroupOf (C t)).map κ = coordinateG F :=
    (Subgroup.eq_of_le_of_card_ge (hKmap ▸ hKle) hJmap).symm
  have hnot : ¬ (p ^ f) ^ 3 ∣ Nat.card G := by
    intro hcube
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4B, -⟩ := hcl
    rw [hq'] at h4B
    have hp1 : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by
      exact_mod_cast dvd_pow_self p (by omega : f ≠ 0)
    have hpnd1 : ¬ (p : ℤ) ∣ 1 := by
      intro h
      have := Int.eq_one_of_dvd_one (by positivity) h
      have := hp.one_lt
      omega
    have hpB : ¬ p ∣ Nat.card B := by
      intro h
      apply hpnd1
      have h1 : (p : ℤ) ∣ 4 * (Nat.card B : ℤ) :=
        dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h) 4
      change (p : ℤ) ∣ 4 * (Nat.card B : ℤ) at h1
      rw [h4B] at h1
      have h2 := dvd_sub hp1 h1
      have h3 : ((p ^ f : ℕ) : ℤ) - (((p ^ f : ℕ) : ℤ) -
          (if p ^ f % 4 = 1 then 1 else -1)) = (if p ^ f % 4 = 1 then 1 else -1) := by ring
      rw [h3] at h2
      split_ifs at h2 with h4
      · exact h2
      · exact (dvd_neg).mp h2
    have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have hp2 : ¬ p ∣ 2 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      have := hp.two_le
      have : p = 2 := by omega
      subst this
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    have hpq2 : ¬ p ∣ (p ^ f) ^ 2 - 1 := by
      intro h
      have h1 : p ∣ (p ^ f) ^ 2 := dvd_pow hpq (by norm_num)
      have h2 := Nat.dvd_sub h1 h
      rw [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by
        have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
    have hvC : padicValNat p (Nat.card (C t)) = f := by
      rw [hCcard, padicValNat.mul (by positivity) (by
          have : 1 < (p ^ f) ^ 2 := by nlinarith
          omega),
        padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by norm_num) hB0,
        padicValNat.eq_zero_of_not_dvd hp2, padicValNat.eq_zero_of_not_dvd hpB,
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hpq2]
      ring
    have hWcomm : ∀ x ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype, ∀ y ∈ (CFSG.pPrimeCore 2
          (Subgroup.centralizer (V : Set G))).map (Subgroup.centralizer (V : Set G)).subtype,
        x * y = y * x := hL.W_comm
    have hWodd : Odd (Nat.card ((CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.centralizer (V : Set G)).subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2)
        (G := Subgroup.centralizer (V : Set G)))
    have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
    have hdisj : Disjoint V ((CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype) := by
      rw [Subgroup.disjoint_def]
      intro x hxV hxW
      exact eq_one_of_mem_of_odd hVp hxV (hL.W_odd x hxW)
    obtain ⟨hDcard, -⟩ := Principal.klein_centralizer_odd_core V _ hV hWodd hWcomm hDV hdisj
    have hDeq : C t ⊓ Subgroup.centralizer ({s₀} : Set G) =
        Subgroup.centralizer (V : Set G) := by
      rw [← StationaryConfinement.centralizer_closure_pair t s₀,
        StationaryOddLocalization.closure_pair_eq_zpowers_sup t s₀]
    have hpW : ¬ p ∣ Nat.card ((CFSG.pPrimeCore 2 (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype) := by
      intro h
      rw [hWcard] at h
      have h2 : p ∣ 2 * ((if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) / 2) :=
        dvd_mul_of_dvd_right h 2
      split_ifs at h2 with h4
      · rw [show 2 * ((p ^ f + 1) / 2) = p ^ f + 1 by
          obtain ⟨k, hk⟩ := hpodd.pow (n := f)
          omega] at h2
        exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h2))
      · rw [show 2 * ((p ^ f - 1) / 2) = p ^ f - 1 by
          obtain ⟨k, hk⟩ := hpodd.pow (n := f)
          omega] at h2
        have h3 := Nat.dvd_sub hpq h2
        rw [show p ^ f - (p ^ f - 1) = 1 by omega] at h3
        exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    have hvD : padicValNat p (Nat.card (C t ⊓ Subgroup.centralizer ({s₀} : Set G) :
        Subgroup G)) = 0 := by
      rw [hDeq, hDcard]
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · have h4 : p ∣ 2 ^ 2 := by norm_num; exact h1
        exact hp2 (hp.dvd_of_dvd_pow h4)
      · exact hpW h1
    have hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) ≤
        padicValNat p (Nat.card G) := by
      have h3 : 3 * f ≤ padicValNat p (Nat.card G) := by
        rw [← padicValNat_dvd_iff_le Nat.card_pos.ne', mul_comm, pow_mul]
        exact hcube
      have e1 : (padicValNat p (Nat.card (C t)) : ℤ) = f := by exact_mod_cast hvC
      have e2 : (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) =
          0 := by exact_mod_cast hvD
      rw [e1, e2]
      have h4 : (3 : ℤ) * (f : ℤ) ≤ (padicValNat p (Nat.card G) : ℤ) := by exact_mod_cast h3
      linarith
    have hU : ∀ x : G, x ∈ B ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t ∧
        (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹ := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy, hL.s_inv _ ⟨y, hy, rfl⟩⟩
      · rintro ⟨hx, hxN, -⟩
        exact ⟨⟨x, hx⟩, hxN, rfl⟩
    obtain ⟨-, -, hUbot, -⟩ := Principal.regularity_eliminates_confined_normal_inverted_odd_factor
      hG n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hmodel hval B hU hBnormal hconf
    exact hBne hUbot
  obtain ⟨a, -, b, -, hab1, hab2⟩ := exists_commutator_three_cycle hV htV hsV hL.t_ne_one
    hL.s_ne_one hL.s_ne.symm hsurj
  refine ⟨d₁, JL, F, hFf, hFfin, κ,
    { prime := hp
      odd := hpodd
      one_le := hf
      q_gt := hq
      card_F := data.field_card
      card_F' := hq'
      clauses := hcl
      localData := hL
      sl2 := hsl2
      card_C := hCcard
      B_ne_bot := hBne
      confine := hconf
      sylow_normalizer := fun ℓ hℓ hℓB P Q hQC hQ hPQ =>
        ((hCI.1 ℓ hℓ hℓB P).1 Q hQC hQ hPQ)
      not_cube := hnot
      ker_κ := hker
      range_κ := hrange
      layer_κ := hlayer
      conj_t := fun x hx => Principal.isConj_of_orderOf_eq_two hn S fS ht hx
      four_conj := fun T hT => exists_conj_eq_of_isKleinFour hn S fS V hVS hV T hT
      three_cycle := ⟨a * b * a⁻¹ * b⁻¹, hab1, hab2⟩
      sylow_two := ⟨S, hVS, hSC⟩ }⟩

end CFSG.Semidihedral.FixedCoreNontrivial
