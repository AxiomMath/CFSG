module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreSupport
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactor
public import CFSG.CharacterTheory.Semidihedral.IndexTwoSL2Degree
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectDegreeDivisibility

public section

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
open CFSG.Semidihedral.IndexTwoSL2Degree CFSG.Semidihedral.StationaryConfinement

theorem actual_field_factor_one_fixed_core_defect_four_degrees_coprime
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
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let V : Subgroup G := Subgroup.closure {t, s₀}
    let Na : Subgroup G := (N t).map (C t).subtype
    let A₀ : Subgroup G := Na ⊓ Subgroup.centralizer {s₀}
    let qe : ℕ := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    E = ⊥ ∧ (∃ μ : J × N t ≃* Y, ∀ x : J × N t, (μ x : C t) = x.1 * x.2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (∃ U : Subgroup G, (∀ x : G, x ∈ U ↔ x ∈ Na ∧ s₀ * x * s₀⁻¹ = x⁻¹) ∧ U ≤ Na ∧
        IsMulCommutative U ∧ (U.subgroupOf Na).Characteristic ∧
        Nat.Coprime (Nat.card U) (U.relIndex Na) ∧ (U.subgroupOf Na).Normal ∧
        U ⊔ A₀ = Na ∧ U ⊓ A₀ = ⊥) ∧
      IsCyclic A₀ ∧ Nat.card A₀ ∣ qe / 2 ∧
      (∀ χ ∈ CFSG.BlocksIrr (C t), ∀ m : ℕ, χ 1 = m → 4 ∣ m → ¬ p ∣ m) ∧
      ∀ [Fintype (C t)] (basis : FiniteIrreducibleCharacterBasis (C t))
        (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
        [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (label : basis.index),
        coefficientBlockDefect basis ideal 2 label (V.subgroupOf (C t)) →
        ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
          ¬ p ∣ Module.finrank ℂ (basis.representation χ).vector := by
  intro s₀ L T₀ Y H₀ J E V Na A₀ qe
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  have hts : t ≠ s₀ := fun h => hst h.symm
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have hcov' := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage t
    s₀ hcov
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  obtain ⟨U, -, hUmem, -, hUN, hUcomm, hUchar, hUhall, hUnormal, hUA, hUA', hUcard, hUnorm,
      hA₀cyc, hA₀dvd, -, -, -, -, -, -, -, -, hE⟩ :=
    stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action G
      hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC hts hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hcov
  have hE1 : E = ⊥ := by
    by_contra hEne
    have hEa : (J ⊓ N t).map (C t).subtype ≠ ⊥ := by
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective]
    exact hA₀ (hE hEa).2.2.1
  obtain ⟨-, hJnormal, -, -, hJN, hYJN, -, -, -, -, -, -,
      ⟨F, hF, hFfin, -, π, hFcard, -, -, hπsurj, hπker⟩, -, -, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift n hn S fS
      hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq.le hmodel).1 hcov'
  replace hJN : ⁅J, N t⁆ = ⊥ := hJN
  replace hYJN : Y = J ⊔ N t := hYJN
  have hJcomm : ∀ j ∈ J, ∀ x ∈ N t, j * x = x * j := by
    intro j hj x hx
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN hj
    exact (Subgroup.mem_centralizer_iff.mp h x hx).symm
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπker]
    change E.subgroupOf J = ⊥
    rw [hE1, Subgroup.bot_subgroupOf]
  let eJ : J ≃* Matrix.SpecialLinearGroup (Fin 2) F := MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  have hdisj : J ⊓ N t = ⊥ := hE1
  obtain ⟨μ, hμ⟩ := exists_mulEquiv_prod_two hYJN.symm hdisj hJcomm
  have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
  have hUC : U ≤ C t := hUN.trans hNaC
  have hA₀Na : A₀ ≤ Na := inf_le_left
  have hA₀C : A₀ ≤ C t := hA₀Na.trans hNaC
  have hCNa : C t ≤ Subgroup.normalizer (Na : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (inferInstance : (N t).Normal).conj_mem y hy ⟨c, hc⟩, rfl⟩
  have hNamap : Na = (N t).map (C t).subtype := rfl
  let Uc : Subgroup (C t) := U.comap (C t).subtype
  let Ac : Subgroup (C t) := A₀.comap (C t).subtype
  have hUcN : Uc ≤ N t := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hUN hx
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hAcN : Ac ≤ N t := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hA₀Na hx
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hUcnorm : N t ≤ Subgroup.normalizer (Uc : Set (C t)) := by
    intro y _
    have hyU := hUnorm (hCNa y.2)
    rw [Subgroup.mem_normalizer_iff] at hyU ⊢
    intro x
    exact hyU x
  have hUAc : Disjoint Uc Ac := by
    rw [Subgroup.disjoint_def]
    intro x hxU hxA
    have h : (x : G) ∈ U ⊓ A₀ := ⟨hxU, hxA⟩
    rw [hUA', Subgroup.mem_bot] at h
    exact Subtype.ext h
  have hrange : (C t).subtype.range = C t := Subgroup.range_subtype _
  have hUAcN : Uc ⊔ Ac = N t := by
    apply Subgroup.map_injective (C t).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_comap_eq_self (hrange.symm ▸ hUC),
      Subgroup.map_comap_eq_self (hrange.symm ▸ hA₀C), hUA]
  have hUccomm : IsMulCommutative Uc := isMulCommutative_comap_subtype (C t) hUcomm
  have hAccomm : IsMulCommutative Ac :=
    isMulCommutative_comap_subtype (C t) (@IsCyclic.isMulCommutative _ _ hA₀cyc)
  have hcardUc : Nat.card Uc = Nat.card U := card_comap_subtype_of_le hUC
  have hcardAc : Nat.card Ac = Nat.card A₀ := card_comap_subtype_of_le hA₀C
  have hrelU : U.relIndex Na = Nat.card A₀ := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := Na)
    have h2 := Subgroup.relIndex_mul_card (H := A₀) (K := Na)
    rw [inf_eq_left.mpr hUN] at h1
    rw [inf_eq_left.mpr hA₀Na, ← hUcard] at h2
    have hpos : 0 < Nat.card U := Nat.card_pos
    have h3 : U.relIndex Na * Nat.card U = Nat.card A₀ * Nat.card U := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hcop : Nat.Coprime (Nat.card Uc) (Nat.card Ac) := by
    rw [hcardUc, hcardAc, ← hrelU]
    exact hUhall
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hpA : ¬ p ∣ Nat.card Ac := by
    rw [hcardAc]
    intro h
    exact not_dvd_half_torusOrder hp (dvd_pow_self p (by omega)) hqodd (h.trans hA₀dvd)
  have hdeg : ∀ χ ∈ CFSG.BlocksIrr (C t), ∀ m : ℕ, χ 1 = m → 4 ∣ m → ¬ p ∣ m := by
    let : Fintype (C t) := Fintype.ofFinite _
    let : Fintype F := Fintype.ofFinite F
    have : Y.Normal := Subgroup.normal_of_index_eq_two hY
    have h :=
      index_two_SL2_times_odd_abelian_by_abelian_group_has_no_four_characteristic_degree
      hp hpodd hf hFcard Y hY J (N t) hYJN.symm (disjoint_iff.mpr hdisj) hJcomm eJ hNodd Uc Ac
      hUcN hAcN hUcnorm hUAc hUAcN hUccomm hAccomm hcop hpA
    intro χ hχ m hm h4
    exact (h.2.2 χ hχ m hm).1 h4
  refine ⟨hE1, ⟨μ, hμ⟩, ⟨F, hF, hFfin, hFcard, ⟨eJ⟩⟩,
    ⟨U, hUmem, hUN, hUcomm, hUchar, hUhall, hUnormal, hUA, hUA'⟩, hA₀cyc, hA₀dvd, hdeg, ?_⟩
  intro _ basis ideal _ _ label hD χ hχ
  have hVK : IsKleinFour V :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s₀ ht2 hs2 hsC hts
  have hVC : V ≤ C t := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact hsC
  have hcardV : Nat.card (V.subgroupOf (C t)) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hVK.card_four]
    rfl
  obtain ⟨-, -, hall⟩ := block_class_defect_witness_character_degree_dvd basis ideal 2 label _ hD
  obtain ⟨-, hdvd⟩ := hall 2 hcardV
  have hχdvd := hdvd χ hχ
  have hSC : (S : Subgroup G) ≤ C t := sylow_le_centralizer_of_eq hn fS ht
  have hSn : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr fS.toEquiv, CFSG.Semidihedral.card n (by omega)]
  have h2n : 2 ^ n ∣ Nat.card (C t) := hSn ▸ Subgroup.card_dvd_of_le hSC
  have hv : n ≤ padicValNat 2 (Nat.card (C t)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h2n
  have h4 : 4 ∣ Module.finrank ℂ (basis.representation χ).vector :=
    (pow_dvd_pow 2 (show 2 ≤ padicValNat 2 (Nat.card (C t)) - 2 by omega)).trans hχdvd
  exact hdeg _ ⟨(basis.representation χ).vector, inferInstance, inferInstance, inferInstance,
    (basis.representation χ).representation, basis.irreducible χ, rfl⟩ _
    (Representation.char_one _) h4

end CFSG.Semidihedral.Principal
