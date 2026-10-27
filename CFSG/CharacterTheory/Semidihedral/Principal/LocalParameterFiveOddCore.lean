module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOddCoreSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveDegreeEight
public import CFSG.CharacterTheory.Semidihedral.Principal.QuaternionCosetSixteenBound

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
open LocalParameterFiveOddCore

theorem simple_local_parameter_five_odd_core_has_order_one_or_three
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ)
    (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1) :
    let T₀ : Subgroup (H t) := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y : Subgroup (C t) := T₀.comap (nu t)
    (N t = ⊥ ∨ (IsCyclic (N t) ∧ Nat.card (N t) = 3)) ∧
    ∃ c : C t, orderOf c = 5 ∧
      let J : Subgroup (C t) := Subgroup.normalClosure {c}
      ⁅J, N t⁆ = ⊥ ∧ J.map (nu t) = T₀ ∧ Y = J ⊔ N t ∧
      ∀ Q : Sylow 2 J,
        let Q' : Subgroup (C t) := (Q : Subgroup J).map J.subtype
        Nonempty (QuaternionGroup 2 ≃* Q') ∧ tInC t ∈ Q' ∧
          (∀ x ∈ Q', orderOf x = 2 → x = tInC t) ∧ ⁅Q', N t⁆ = ⊥ ∧
          ∀ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
            (basis.representation principal).character = 1 →
            ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
              [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2],
            ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
              ∀ q ∈ Q', q ≠ 1 → ∀ u ∈ N t,
                (basis.representation χ).character ((q : G) * (u : G)) =
                  (basis.representation χ).character (q : G) := by
  intro T₀ Y
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨hn4, hCt, hDt, hGc, -, -, -⟩ := simple_local_parameter_five_is_regular_with_exact_order
    hGnonab n hn S fS t ht hnonab hcentral hnc hmodel
  subst hn4
  obtain ⟨hz, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨χ, ψ, -, hχB, -, -, -, hχfaith, -, hχrat, -, hχ1, -, hχt, -, hχN, -, hη, hNdvd, -⟩ :=
    simple_local_parameter_five_faithful_rational_centralizer_degree_eight hGnonab 4 hn S fS t ht
      hnonab hcentral hnc hmodel basis principal hprincipal ideal
  obtain ⟨hE, hEchar, -, hEdim, -, hηrat, hηfaith, -, hηinv⟩ := hη (basis.representation χ) rfl
  set ρC : Representation ℂ (C t) (basis.representation χ).vector :=
    (basis.representation χ).representation.comp (C t).subtype
  set E : Submodule ℂ (basis.representation χ).vector :=
    Module.End.eigenspace (ρC (tInC t)) (-1)
  set ρE := ρC.subrepresentation E hE
  have hχN' : ∀ u ∈ N t, (basis.representation χ).character (t * (u : G)) = 5 :=
    fun u hu => (hχN u hu).1
  clear hχN
  have hdegχ : Module.finrank ℂ (basis.representation χ).vector = 21 := by
    have h := (basis_character_one basis χ).1
    rw [hχ1] at h
    exact_mod_cast h.symm
  have hNodd : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hρEchar : ∀ c : C t, ρE.character c = ((basis.representation χ).character c -
      (basis.representation χ).character (t * c)) / 2 := fun c => congrFun hEchar c
  let τN : FiniteComplexRepresentation.{0, 0} (N t) :=
    { vector := E
      representation := ρE.comp (N t).subtype }
  have hτNfaith : Function.Injective τN.representation := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hηfaith x x.2 hx)
  have hτNrat : ∀ x, ∃ q : ℚ, τN.character x = q := by
    intro x
    obtain ⟨q, hq⟩ := hηrat (x : C t)
    refine ⟨q, ?_⟩
    change ρE.character (x : C t) = q
    rw [hρEchar]
    exact hq
  have hτNdeg : Module.finrank ℂ τN.vector = 8 := hEdim
  have hτNinv : ∀ (c : C t) (x : N t),
      τN.character ((MulAut.conjNormal (H := N t) c) x) = τN.character x := by
    intro c x
    change ρE.character (((MulAut.conjNormal (H := N t) c) x : N t) : C t) =
      ρE.character (x : C t)
    rw [MulAut.conjNormal_apply, hρEchar, hρEchar]
    exact hηinv c x x.2
  set CN : Subgroup (N t) :=
    ((Subgroup.centralizer {(fS (s 4) : G)}).comap (C t).subtype).subgroupOf (N t)
  have hNcard : Nat.card (N t) = Nat.card CN * CN.index := (CN.card_mul_index).symm
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r 4)).property _
  have hVS : (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s 4) : G) : Subgroup G) ≤
      (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s 4)).property)
  have htV : t ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s 4) : G) : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have hfus : ∀ v ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s 4) : G) : Subgroup G),
      v ≠ 1 → ∃ g ∈ Subgroup.normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s 4) : G) : Subgroup G) : Set G),
        g * v * g⁻¹ = t := fun v hv hv1 =>
    CFSG.Semidihedral.Local.klein_four_normalizer_conj_transitive 4 hn S fS _ hVS
      (supplied_four_group_isKleinFour hn fS ht) hv htV hv1 ht1
  have h7a : ¬ 7 ∣ Nat.card CN := prime_not_dvd_card_oddCore_centralizer_of_five hn fS ht hfus
    (by norm_num : Nat.Prime 7) (by decide) (by norm_num) (basis.representation χ)
    (by rw [hdegχ]; norm_num) hχrat hχfaith hχt (fun y hy => hχN' y hy) hDt
  have h7b : ¬ 7 ∣ CN.index := by
    intro h7
    have hle := CFSG.LyonsUnitaryFour.factorization_le_of_faithful_rational_character
      (basis.representation χ) hχfaith hχrat (p := 7) (by norm_num)
    rw [hdegχ, show (21 : ℕ) / (7 - 1) = 3 by norm_num, show Nat.factorial 3 = 6 by rfl,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 6), add_zero] at hle
    have hdvd : 7 ^ 4 ∣ Nat.card G := by
      rw [hGc]
      have h1 : 7 ∣ 126000 * Nat.card CN := Dvd.dvd.mul_right (by norm_num) _
      have h2 : 7 ^ 3 ∣ CN.index ^ 3 := pow_dvd_pow_of_dvd h7 3
      have := mul_dvd_mul h1 h2
      rwa [← pow_succ'] at this
    have := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').mp hdvd
    omega
  have h7 : ¬ 7 ∣ Nat.card (N t) := by
    rw [hNcard]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
    · exact h7a h
    · exact h7b h
  have hN405 : Nat.card (N t) ∣ 3 ^ 4 * 5 := by
    have hcop : Nat.Coprime (Nat.card (N t)) 7 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7))
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hNdvd
  have hSC : (S : Subgroup G) ≤ C t := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hz]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center 4 (by norm_num)))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : (S : Subgroup G)) : G)) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
    exact h'
  let φS : SemidihedralGroup 4 →* C t :=
    MonoidHom.codRestrict ((S : Subgroup G).subtype.comp fS.toMonoidHom) (C t)
      (fun x => hSC (fS x).2)
  have hφSinj : Function.Injective φS := by
    intro x y hxy
    apply fS.injective
    apply Subtype.ext
    exact congrArg (fun c : C t => (c : G)) hxy
  set Q₀ : Subgroup (C t) := (quaternionSubgroup 4).map φS with hQ₀
  have hQ₀equiv : QuaternionGroup 2 ≃* Q₀ :=
    (quaternionEquiv 4 hn).trans (Subgroup.equivMapOfInjective _ φS hφSinj)
  have hQ₀card : Nat.card Q₀ = 8 := by
    rw [← Nat.card_congr hQ₀equiv.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ₀K : Q₀ ≤ K t := by
    rw [hQ₀, quaternionSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    apply (actual_order_four_residual_and_square 4 hn S fS hG t ht2 _ _).1
    rw [orderOf_injective φS hφSinj]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← quaternionEquiv_rotation 4 hn, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
        QuaternionGroup.orderOf_a_one]
      norm_num
    · rw [← quaternionEquiv_generator 4 hn, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
        QuaternionGroup.orderOf_xa]
  have htQ₀ : tInC t ∈ Q₀ := by
    refine ⟨z 4, z_mem_quaternionSubgroup 4 (by norm_num), ?_⟩
    apply Subtype.ext
    exact hz
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ₀card]; norm_num)
  have huniqK : ∀ v ∈ K t, orderOf v = 2 → v = tInC t := fun v hv hv2 =>
    eq_tInC_of_mem_K_of_orderOf_eq_two 4 hn S fS hG t ht2 hv hv2
  set Q₀G : Subgroup G := Q₀.map (C t).subtype with hQ₀G
  have hQ₀Gcard : Nat.card Q₀G = 8 := by
    rw [hQ₀G, Subgroup.card_map_of_injective (C t).subtype_injective, hQ₀card]
  have hQ₀G2 : IsPGroup 2 Q₀G := hQ₀2.map _
  have htQ₀G : t ∈ Q₀G := ⟨tInC t, htQ₀, rfl⟩
  have hQ₀Gt : ∀ u ∈ Q₀G, u ≠ 1 → t ∈ Subgroup.zpowers u := by
    rintro _ ⟨q, hq, rfl⟩ hq1
    have hq1' : q ≠ 1 := fun h => hq1 (by rw [h]; rfl)
    have h := mem_zpowers_of_unique_involution hQ₀2
      (fun v hv hv2 => huniqK v (hQ₀K hv) hv2) hq hq1'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h' := congrArg (fun y : C t => (y : G)) hk
    simp only [Subgroup.coe_zpow] at h'
    exact h'
  have h5 : ¬ 5 ∣ Nat.card (N t) := by
    intro h5
    obtain ⟨P, hPcard, hP⟩ := exists_card_five_subgroup_of_pow_five hN405 h5 τN hτNfaith
      hτNrat (by rw [hτNdeg]; norm_num)
    set P₅ : Subgroup G := (P.map (N t).subtype).map (C t).subtype with hP₅
    have hP₅card : Nat.card P₅ = 5 := by
      rw [hP₅, Subgroup.card_map_of_injective (C t).subtype_injective,
        Subgroup.card_map_of_injective (N t).subtype_injective, hPcard]
    have hP₅C : P₅ ≤ C t := by
      rw [hP₅]
      exact Subgroup.map_subtype_le _
    have hP₅normal : ∀ c ∈ C t, ∀ x ∈ P₅, c * x * c⁻¹ ∈ P₅ := by
      intro c hc x hx
      obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hx
      have hw5 : w ^ 5 = 1 := by
        have := Subgroup.orderOf_dvd_natCard P hw
        rw [hPcard] at this
        exact orderOf_dvd_iff_pow_eq_one.mp this
      set w' : N t := MulAut.conjNormal (H := N t) (⟨c, hc⟩ : C t) w with hw'
      have hw'5 : w' ^ 5 = 1 := by rw [hw', ← map_pow, hw5, map_one]
      refine ⟨((w' : N t) : C t), ⟨w', hP w' hw'5, rfl⟩, ?_⟩
      rw [hw', MulAut.conjNormal_apply]
      rfl
    obtain ⟨u', hu'⟩ : ∃ u : P₅, orderOf u = 5 :=
      exists_prime_orderOf_dvd_card' 5 (by rw [hP₅card])
    set u : G := (u' : G) with hudef
    have huP : u ∈ P₅ := u'.2
    have hu5 : orderOf u = 5 := by rw [hudef, Subgroup.orderOf_coe, hu']
    have hPu : P₅ = Subgroup.zpowers u := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huP)
      rw [hP₅card, Nat.card_zpowers, hu5]
    have hoddcent : ∀ x : C t, Odd (orderOf x) → (x : G) * u = u * x := by
      intro x hx
      have hnorm : (x : G) * u * (x : G)⁻¹ ∈ Subgroup.zpowers u := by
        rw [← hPu]
        exact hP₅normal x x.2 u huP
      have hm : (x : G) ^ orderOf x = 1 := by
        rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      have h := pow_gcd_conj_eq_of_normalizes (by norm_num : Nat.Prime 5) hu5 hnorm hm
      have hgcd : Nat.gcd (orderOf x) (5 - 1) = 1 := by
        rw [show (5 : ℕ) - 1 = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hx)
      rw [hgcd, pow_one] at h
      calc (x : G) * u = (x : G) * u * (x : G)⁻¹ * x := by group
        _ = u * x := by rw [h]
    have hKP : K t ≤ (Subgroup.centralizer (P₅ : Set G)).comap (C t).subtype := by
      rw [K_eq_odd_order_closure, Subgroup.closure_le]
      intro x hx
      change (x : G) ∈ Subgroup.centralizer (P₅ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hPu] at hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (show Commute u (x : G) from (hoddcent x hx).symm) k)).eq
    have hQ₀GP : Q₀G ≤ Subgroup.centralizer (P₅ : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hKP (hQ₀K hq)
    have hker : ∃ x ∈ P₅, (basis.representation χ).character x ≠
        (basis.representation χ).character 1 := by
      refine ⟨u, huP, character_ne_one_of_not_mem_ker _ ?_⟩
      intro hk
      have hu1 : u = 1 := hχfaith ((MonoidHom.mem_ker.mp hk).trans (map_one _).symm)
      rw [hu1, orderOf_one] at hu5
      norm_num at hu5
    obtain ⟨hbound, -⟩ := normal_odd_prime_principal_quaternion_eigenspace_bound basis ideal
      principal hprincipal hχB (basis.representation χ).representation rfl ht2 P₅
      ⟨hP₅C, hP₅normal⟩ (by norm_num : Nat.Prime 5) (by decide) hP₅card Q₀G
      ⟨by rw [hQ₀G]; exact Subgroup.map_subtype_le Q₀, hQ₀GP⟩ hQ₀G2 htQ₀G hQ₀Gt
      (fun x _ => hχrat x) hker
    rw [hQ₀Gcard, show (basis.representation χ).representation.character t = 5 from hχt,
      hdegχ] at hbound
    norm_num at hbound
  have hN81 : Nat.card (N t) ∣ 3 ^ 4 := by
    have hcop : Nat.Coprime (Nat.card (N t)) 5 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5))
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hN405
  obtain ⟨k, hk4, hNk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hN81
  have hN3 : IsPGroup 3 (N t) := IsPGroup.of_card hNk
  have hNle : Nat.card (N t) ≤ 81 := by
    rw [hNk]
    calc 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 81 := by norm_num
  have hcent5 : ∀ c : C t, orderOf c = 5 → ∀ x : N t, c * (x : C t) * c⁻¹ = x := by
    intro c hc x
    have hα : (MulAut.conjNormal (H := N t) c) ^ 5 = 1 := by
      rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    have h := order_five_automorphism_small_three_group_rational_character_obstruction hN3 hNle
      _ hα τN hτNfaith hτNrat (by rw [hτNdeg]; norm_num) (hτNinv c)
    have h' := congrArg (fun α : MulAut (N t) => ((α x : N t) : C t)) h
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using h'
  set K' : Subgroup (C t) := Subgroup.centralizer (N t : Set (C t)) with hK'
  have hK'n : K'.Normal := Subgroup.normal_centralizer
  have h5C : 5 ∣ Nat.card (C t) := by
    rw [hCt]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by norm_num) _) _
  obtain ⟨c₅, hc₅⟩ := exists_prime_orderOf_dvd_card' 5 h5C
  have hc₅K' : c₅ ∈ K' := by
    rw [hK', Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hcent5 c₅ hc₅ ⟨x, hx⟩
    calc x * c₅ = c₅ * x * c₅⁻¹ * c₅ := by rw [h]
      _ = c₅ * x := by group
  have hc₅K : c₅ ∈ K t := by
    rw [K_eq_odd_order_closure]
    exact Subgroup.subset_closure (show Odd (orderOf c₅) by rw [hc₅]; decide)
  set Jc : Subgroup (C t) := Subgroup.normalClosure {c₅}
  have hJcK' : Jc ≤ K' := Subgroup.normalClosure_le_normal (by
    rw [Set.singleton_subset_iff]
    exact hc₅K')
  have hJcK : Jc ≤ K t := Subgroup.normalClosure_le_normal (by
    rw [Set.singleton_subset_iff]
    exact hc₅K)
  have hc₅Jc : c₅ ∈ Jc := Subgroup.subset_normalClosure (Set.mem_singleton c₅)
  have hLJ := generalizedFitting_eq_J_of_field_group_trivial 4 hn S fS hG t ht2 hnonab hcentral
    hnc 5 1 (by norm_num) (by decide) le_rfl hmodel (fun a _ ha => Nat.dvd_one.mp ha)
  obtain ⟨hNZK, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs 4 hn S fS hG t ht2
  have hKcomap : K t = (J t).comap (kappa t) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact (sup_eq_left.mpr hNZK).symm
  have hYK : Y = K t := by
    change ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) = K t
    rw [Subgroup.comap_comap, barKappa_comp_nu, hLJ, ← hKcomap]
  have hκ1 : kappa t c₅ ≠ 1 := by
    intro h1
    have hmem : c₅ ∈ NZ t := (QuotientGroup.eq_one_iff c₅).mp h1
    obtain ⟨m, hm, w, hw, hmw⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hw2 : w * w = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have htt : tInC t ^ 2 = 1 := by
        have : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
        exact this ▸ pow_orderOf_eq_one (tInC t)
      rw [← zpow_add, ← two_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast,
        htt, one_zpow]
    have hwc : ∀ y : C t, w * y = y * w := by
      intro y
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hc : Commute (tInC t) y := (Subgroup.mem_center_iff.mp (tInC_central t) y).symm
      exact (hc.zpow_left j).eq
    have hsq : c₅ ^ 2 = m ^ 2 := by
      rw [← hmw, pow_two, pow_two]
      calc m * w * (m * w) = m * (w * m) * w := by group
        _ = m * (m * w) * w := by rw [hwc m]
        _ = m * m * (w * w) := by group
        _ = m * m := by rw [hw2, mul_one]
    have hc₅N : c₅ ∈ N t := by
      have h6 : c₅ = (c₅ ^ 2) ^ 3 := by
        rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, ← hc₅, pow_orderOf_eq_one,
          one_mul, pow_one]
      rw [h6, hsq]
      exact (N t).pow_mem ((N t).pow_mem hm 2) 3
    have hdvd : orderOf c₅ ∣ Nat.card (N t) := by
      have := orderOf_dvd_natCard (⟨c₅, hc₅N⟩ : N t)
      rwa [Subgroup.orderOf_mk] at this
    rw [hc₅, hNk] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_three).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd))
    norm_num at this
  have hJcL : Jc.map (kappa t) = CFSG.generalizedFitting (Gamma t) := by
    have hle : Jc.map (kappa t) ≤ CFSG.generalizedFitting (Gamma t) := by
      rw [hLJ]
      exact Subgroup.map_mono hJcK
    apply le_antisymm hle
    have hMn : (Jc.map (kappa t)).Normal :=
      (Subgroup.normalClosure_normal).map _ (QuotientGroup.mk'_surjective _)
    have hsub : ((Jc.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t))).Normal :=
      hMn.subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Jc.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t))) with h | h
    · exfalso
      have hmem : (⟨kappa t c₅, hle (Subgroup.mem_map_of_mem _ hc₅Jc)⟩ :
          CFSG.generalizedFitting (Gamma t)) ∈
          (Jc.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t)) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hc₅Jc)
      rw [h, Subgroup.mem_bot] at hmem
      exact hκ1 (congrArg Subtype.val hmem)
    · intro x hx
      have hmem : (⟨x, hx⟩ : CFSG.generalizedFitting (Gamma t)) ∈
          (Jc.map (kappa t)).subgroupOf (CFSG.generalizedFitting (Gamma t)) :=
        h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
  have htJc : tInC t ∈ Jc := by
    obtain ⟨P₂⟩ : Nonempty (Sylow 2 (CFSG.generalizedFitting (Gamma t))) := inferInstance
    have hP₂ : Nat.card (P₂ : Subgroup (CFSG.generalizedFitting (Gamma t))) ≠ 1 := by
      intro h1
      apply hnc P₂
      have : Subsingleton (P₂ : Subgroup (CFSG.generalizedFitting (Gamma t))) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp P₂.isPGroup'
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hP₂ (by rw [hj, pow_zero])
    have h2L : 2 ∣ Nat.card (CFSG.generalizedFitting (Gamma t)) := by
      have h := Subgroup.card_subgroup_dvd_card (P₂ : Subgroup (CFSG.generalizedFitting (Gamma t)))
      rw [hj] at h
      exact (dvd_pow_self 2 hj0).trans h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2L
    have hyJc : (y : Gamma t) ∈ Jc.map (kappa t) := by
      rw [hJcL]
      exact y.2
    obtain ⟨x, hxJc, hxy⟩ := hyJc
    have h2x : 2 ∣ orderOf x := by
      have h := orderOf_map_dvd (kappa t) x
      rw [hxy, Subgroup.orderOf_coe, hy] at h
      exact h
    have hw2 : orderOf (x ^ (orderOf x / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' h2x
    have hwJc : x ^ (orderOf x / 2) ∈ Jc := Jc.pow_mem hxJc _
    rw [← huniqK _ (hJcK hwJc) hw2]
    exact hwJc
  have hZJc : Z t ≤ Jc := Subgroup.zpowers_le.mpr htJc
  have hNK : N t ≤ K t := le_sup_left.trans hNZK
  have hJcNK : Jc ⊔ N t = K t := by
    apply le_antisymm (sup_le hJcK hNK)
    intro x hx
    have hxL : kappa t x ∈ Jc.map (kappa t) := by
      rw [hJcL, hLJ]
      exact Subgroup.mem_map_of_mem _ hx
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hxL
    have hle : Jc ⊔ NZ t ≤ Jc ⊔ N t := sup_le le_sup_left (sup_le le_sup_right
      (hZJc.trans le_sup_left))
    exact hle hxL
  have hKidx : (K t).index = 2 := by
    rw [hKcomap, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hJindex]
  have hKcard : Nat.card (K t) = 120 * 3 ^ k := by
    have h := (K t).card_mul_index
    rw [hKidx, hCt, mul_assoc, ← hNcard, hNk] at h
    omega
  have hQ₀Jc : Q₀ ≤ Jc := by
    have : Jc.Normal := Subgroup.normalClosure_normal
    exact le_of_le_sup_of_odd Jc (N t) Q₀ (hQ₀K.trans hJcNK.ge) hQ₀2 hNodd
  have hJc2 : (Nat.card Jc).factorization 2 = 3 := by
    have hpos : Nat.card Jc ≠ 0 := Nat.card_pos.ne'
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have h16 : 2 ^ 4 ∣ Nat.card Jc :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mpr hlt
      have hdvd : Nat.card Jc ∣ 120 * 3 ^ k := hKcard ▸ Subgroup.card_dvd_of_le hJcK
      have h16' := h16.trans hdvd
      have hcop : Nat.Coprime (2 ^ 4) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
      have := hcop.dvd_of_dvd_mul_right h16'
      norm_num at this
    · have h8 : 2 ^ 3 ∣ Nat.card Jc := by
        have h := Subgroup.card_dvd_of_le hQ₀Jc
        rw [hQ₀card] at h
        exact h
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp h8
  have hQ₀Jccard : Nat.card (Q₀.subgroupOf Jc) = 2 ^ (Nat.card Jc).factorization 2 := by
    rw [hJc2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀Jc).toEquiv, hQ₀card]
    norm_num
  set P₀ : Sylow 2 Jc := Sylow.ofCard (Q₀.subgroupOf Jc) hQ₀Jccard with hP₀
  have hQ : ∀ Q : Sylow 2 Jc,
      let Q' : Subgroup (C t) := (Q : Subgroup Jc).map Jc.subtype
      Nonempty (QuaternionGroup 2 ≃* Q') ∧ tInC t ∈ Q' ∧
        (∀ x ∈ Q', orderOf x = 2 → x = tInC t) ∧ Q' ≤ K' ∧ Q' ≤ K t ∧ IsPGroup 2 Q' ∧
        Nat.card Q' = 8 := by
    intro Q Q'
    have hQ'le : Q' ≤ Jc := Subgroup.map_subtype_le _
    have e₁ : (Q : Subgroup Jc) ≃* Q' :=
      Subgroup.equivMapOfInjective (Q : Subgroup Jc) Jc.subtype Jc.subtype_injective
    have e₂ : (P₀ : Subgroup Jc) ≃* Q₀ := by
      rw [hP₀, Sylow.coe_ofCard]
      exact Subgroup.subgroupOfEquivOfLe hQ₀Jc
    have e : QuaternionGroup 2 ≃* Q' :=
      hQ₀equiv.trans (e₂.symm.trans ((Sylow.equiv P₀ Q).trans e₁))
    have hQ'card : Nat.card Q' = 8 := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hQ'2 : IsPGroup 2 Q' := IsPGroup.of_card (n := 3) (by rw [hQ'card]; norm_num)
    have huniq : ∀ x ∈ Q', orderOf x = 2 → x = tInC t := fun x hx hx2 =>
      huniqK x (hJcK (hQ'le hx)) hx2
    refine ⟨⟨e⟩, ?_, huniq, hQ'le.trans hJcK', hQ'le.trans hJcK, hQ'2, hQ'card⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Q') 2 (by rw [hQ'card]; norm_num)
    rw [← huniq v v.2 (by rw [Subgroup.orderOf_coe, hv])]
    exact v.2
  set NG : Subgroup G := (N t).map (C t).subtype
  have hNGcard : Nat.card NG = Nat.card (N t) :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  have hcoset : ∀ Q : Sylow 2 Jc, ∀ (basis' : FiniteIrreducibleCharacterBasis G)
      (principal' : basis'.index), (basis'.representation principal').character = 1 →
      ∀ (ideal' : Ideal ComplexAlgebraicIntegers) [ideal'.IsMaximal]
        [CharP (ComplexAlgebraicIntegers ⧸ ideal') 2],
      ∀ χ' ∈ coefficientBlock basis' (localizedComplexIntegerRing ideal') principal',
        ∀ q ∈ (Q : Subgroup Jc).map Jc.subtype, q ≠ 1 → ∀ u ∈ N t,
          (basis'.representation χ').character ((q : G) * (u : G)) =
            (basis'.representation χ').character (q : G) := by
    intro Q basis' principal' hprincipal' ideal' _ _ χ' hχ' q hq hq1 u hu
    obtain ⟨-, -, huniq, hQK', -, hQ2, hQcard⟩ := hQ Q
    have htq : tInC t ∈ Subgroup.zpowers q := mem_zpowers_of_unique_involution hQ2 huniq hq hq1
    have hq8 : orderOf (q : G) ∣ 2 ^ 3 := by
      rw [Subgroup.orderOf_coe]
      have h := Subgroup.orderOf_dvd_natCard _ hq
      rw [hQcard] at h
      exact h
    have hqN : ∀ m ∈ N t, (q : G) * (m : G) = (m : G) * (q : G) := by
      intro m hm
      have h := Subgroup.mem_centralizer_iff.mp (hQK' hq) m hm
      exact congrArg Subtype.val h.symm
    refine principal_character_coset_constant_of_normal basis' ideal' 2 principal' hprincipal'
      hχ' hq8 NG ?_ ?_ ?_ ⟨u, hu, rfl⟩
    · rintro _ ⟨m, hm, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (show Commute (q : G) (m : G) from hqN m hm) j)).eq
    · intro g hg n hn
      obtain ⟨m, hm, rfl⟩ := hn
      have hgt : g ∈ C t := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htq
        rw [Subgroup.mem_centralizer_singleton_iff]
        have htj : t = (q : G) ^ j := by
          have h' := congrArg (fun y : C t => (y : G)) hj
          simp only [Subgroup.coe_zpow] at h'
          exact h'.symm
        rw [htj]
        exact (Subgroup.mem_centralizer_iff.mp hg _ (Subgroup.zpow_mem_zpowers _ j)).symm
      refine ⟨⟨g, hgt⟩ * m * ⟨g, hgt⟩⁻¹, (inferInstance : (N t).Normal).conj_mem m hm _, ?_⟩
      rfl
    · rw [hNGcard]
      exact CFSG.pPrimeCore_coprime_card
  obtain ⟨Q⟩ : Nonempty (Sylow 2 Jc) := inferInstance
  obtain ⟨⟨eQ⟩, -, huniqQ, hQK', -, -, -⟩ := hQ Q
  set Q' : Subgroup (C t) := (Q : Subgroup Jc).map Jc.subtype
  set QG : Subgroup G := Q'.map (C t).subtype
  let eG : QuaternionGroup 2 ≃* QG :=
    eQ.trans (Subgroup.equivMapOfInjective Q' (C t).subtype (C t).subtype_injective)
  have hteG : ((eG (QuaternionGroup.a 2) : QG) : G) = t := by
    have hord : orderOf ((eQ (QuaternionGroup.a 2) : Q') : C t) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a]
      decide
    have h := huniqQ _ (eQ (QuaternionGroup.a 2)).2 hord
    change (((eQ (QuaternionGroup.a 2) : Q') : C t) : G) = t
    rw [h]
    rfl
  have hNQG : NG ≤ Subgroup.centralizer (QG : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp (hQK' hq) m hm
    exact congrArg Subtype.val h.symm
  have hconstG : ∀ q ∈ QG, q ≠ 1 → ∀ n ∈ NG,
      (basis.representation χ).representation.character (q * n) =
        (basis.representation χ).representation.character q := by
    rintro _ ⟨q, hq, rfl⟩ hq1 _ ⟨m, hm, rfl⟩
    exact hcoset Q basis principal hprincipal ideal χ hχB q hq (fun h => hq1 (by rw [h]; rfl))
      m hm
  obtain ⟨hNcases, -⟩ := quaternion_coset_constant_rational_odd_sixteen_bound
    (basis.representation χ).representation QG eG hteG NG hNQG (by rw [hNGcard]; exact hNodd)
    (fun n _ hn => hχfaith (hn.trans (map_one _).symm)) (fun n _ => hχrat n) hconstG
    (by rw [hdegχ, show (basis.representation χ).representation.character t = 5 from hχt]
        norm_num)
  have hNfinal : N t = ⊥ ∨ (IsCyclic (N t) ∧ Nat.card (N t) = 3) := by
    rcases hNcases with h | ⟨hcyc, h3⟩
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp h)
    · refine Or.inr ⟨(MulEquiv.isCyclic (Subgroup.equivMapOfInjective (N t) (C t).subtype
        (C t).subtype_injective)).mpr hcyc, hNGcard ▸ h3⟩
  refine ⟨hNfinal, c₅, hc₅, ?_⟩
  intro J
  refine ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJcK', ?_, hYK.trans hJcNK.symm, ?_⟩
  · have hNν : (N t).map (nu t) = ⊥ := QuotientGroup.map_mk'_self (N t)
    calc Jc.map (nu t) = (Jc ⊔ N t).map (nu t) := by rw [Subgroup.map_sup, hNν, sup_bot_eq]
      _ = Y.map (nu t) := by rw [hJcNK, hYK]
      _ = T₀ := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  · intro Q Q'
    obtain ⟨hQe, htQ, huniq, hQK', -, -, -⟩ := hQ Q
    exact ⟨hQe, htQ, huniq, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQK', hcoset Q⟩

end CFSG.Semidihedral.Principal
