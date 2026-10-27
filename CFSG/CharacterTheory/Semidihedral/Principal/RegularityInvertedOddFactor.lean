module

public import CFSG.CharacterTheory.Semidihedral.Principal.RegularityInvertedOddFactorSupport
public import CFSG.CharacterTheory.BlockBasics.LocalRing
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem regularity_eliminates_confined_normal_inverted_odd_factor
    {G : Type} [Group G]
    [Fintype G] (hG : ∀ U : Subgroup G, U.index ≠ 2) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hval : 3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) : ℤ) ≤
      padicValNat p (Nat.card G))
    (U : Subgroup G)
    (hU : ∀ x : G, x ∈ U ↔ ∃ hx : x ∈ C t, (⟨x, hx⟩ : C t) ∈ N t ∧
      (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹)
    (hUnormal : (U.subgroupOf (C t)).Normal)
    (hconf : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ C t) :
    ((C t).index : ℤ) = (Nat.card U : ℤ) ^ 2 * ((p ^ f : ℕ) : ℤ) ^ 2 *
        (((p ^ f : ℕ) : ℤ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * (p ^ f : ℕ) + 1) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card U → ∀ P : Sylow ℓ U,
        (∀ Q : Subgroup G, Q ≤ C t → IsPGroup ℓ Q → (P : Subgroup U).map U.subtype ≤ Q →
          Subgroup.normalizer (Q : Set G) ≤ C t) ∧
        ∀ Q : Sylow ℓ (C t),
          (P : Subgroup U).map U.subtype ≤ (Q : Subgroup (C t)).map (C t).subtype →
          ∃ T : Sylow ℓ G, (T : Subgroup G) = (Q : Subgroup (C t)).map (C t).subtype) ∧
      U = ⊥ ∧ ∀ x : C t, x ∈ N t → (fS (s n) : G) * x = x * (fS (s n) : G) := by
  obtain ⟨-, ht2, hcent, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  set s₀ : C t := ⟨(fS (s n) : G), hsC⟩ with hs₀def
  have hs₀ : orderOf s₀ = 2 := by rw [← hs2, ← Subgroup.orderOf_coe]
  have hs₀t : s₀ ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  set q : ℕ := p ^ f with hqdef
  have hq1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, -, -,
      hvalues⟩ :=
    actual_nonsimple_layer_characteristic_valuation_degree_formulas n hn S fS hG t ht2 hnonab
      hcentral hnc p f hp hpodd hf hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal fS hcent hval
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGorder, -⟩ := hvalues
  rw [hcard] at hGorder
  obtain ⟨-, F', hfield, hfinite, A, a, -, hAodd, -, -, -, -, -, -, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG
      t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, -, -, hSO, hDmap, -, hN0mem⟩ := hall s₀ hs₀ hs₀t
  have hDcard : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
      Nat.card (ActualFourGroupCentralizer.D s₀) := by
    rw [← hDmap, Subgroup.card_map_of_injective Subtype.val_injective]
  set a₀ := Nat.card (ActualFourGroupCentralizer.N0 s₀) with ha₀
  set b₀ := (ActualFourGroupCentralizer.N0 s₀).index with hb₀
  have ha₀pos : 0 < a₀ := Nat.card_pos
  have hb₀pos : 0 < b₀ := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hApos : 0 < Nat.card A := hAodd.pos
  have hsign : ActualFourGroupCentralizer.torusSign q = if q % 4 = 1 then 1 else -1 := by
    rcases hSO.sign with ⟨h1, h1'⟩ | ⟨h3, h3'⟩
    · rw [h1', ite_eq_left h1]
    · rw [h3', ite_eq_right (by omega)]
  have hindexQ : ((C t).index : ℚ) = (b₀ : ℚ) ^ 2 * (q : ℚ) ^ 2 *
      ((q : ℚ) ^ 2 - (if q % 4 = 1 then 1 else -1 : ℤ) * q + 1) := by
    have hCcard : (Nat.card (C t) : ℚ) = 2 * a₀ * b₀ * Nat.card A * q * ((q : ℚ) ^ 2 - 1) := by
      exact_mod_cast hSO.C_card
    have hdcard : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℚ) =
        2 * a₀ * Nat.card A * ((q : ℚ) + (if q % 4 = 1 then 1 else -1 : ℤ)) := by
      rw [hDcard]
      have h := hSO.D_card
      rw [hsign] at h
      exact_mod_cast h
    have hmul : (Nat.card G : ℚ) = Nat.card (C t) * (C t).index := by
      exact_mod_cast (Subgroup.card_mul_index (C t)).symm
    apply regular_index_arithmetic (g := Nat.card G) (c := Nat.card (C t))
      (d := Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)})) (a := a₀)
      (h := Nat.card A) _ (by exact_mod_cast hq1) (by positivity) (by positivity)
      (by positivity) hCcard hdcard _ hmul
    · split_ifs <;> norm_num
    · exact hGorder
  have hindex : ((C t).index : ℤ) = (b₀ : ℤ) ^ 2 * (q : ℤ) ^ 2 *
      ((q : ℤ) ^ 2 - (if q % 4 = 1 then 1 else -1) * q + 1) := by
    exact_mod_cast hindexQ
  have hNodd : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hs₀N : s₀ ∉ N t := CFSG.OddInversion.notMem_of_odd_card hNodd hs₀
  have hs₀norm : s₀ ∈ Subgroup.normalizer ((N t : Subgroup (C t)) : Set (C t)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨-, -, hJcard⟩ := CFSG.OddInversion.odd_inversion_coset_count hNodd hs₀norm hs₀N hs₀
  have hUimage : (U : Set G) = Subtype.val '' CFSG.OddInversion.invertedSet (N t) s₀ := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_image, CFSG.OddInversion.mem_invertedSet]
    rw [hU]
    constructor
    · rintro ⟨hx, hxN, hxs⟩
      exact ⟨⟨x, hx⟩, ⟨hxN, Subtype.ext (by simpa using hxs)⟩, rfl⟩
    · rintro ⟨y, ⟨hyN, hys⟩, rfl⟩
      exact ⟨y.2, hyN, by simpa using congrArg Subtype.val hys⟩
  have hN0 : (Subgroup.centralizer ({s₀} : Set (C t))).subgroupOf (N t) =
      ActualFourGroupCentralizer.N0 s₀ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, hN0mem]
    exact eq_comm
  have hUcard : Nat.card U = b₀ := by
    have h1 : Nat.card U = Nat.card (CFSG.OddInversion.invertedSet (N t) s₀) := by
      rw [← SetLike.coe_sort_coe, hUimage, Nat.card_image_of_injective Subtype.val_injective]
    rw [h1, hJcard, Subgroup.relIndex, hN0]
  have hUC : U ≤ C t := fun x hx => ((hU x).mp hx).1
  have hUodd : Odd (Nat.card U) := by
    rw [hUcard]
    exact Odd.of_dvd_nat hNodd (Subgroup.index_dvd_card _)
  have hinv : ∀ w ∈ Subgroup.centralizer ({t} : Set G), orderOf w = 2 → w ≠ t →
      ∀ x ∈ U, w * x * w⁻¹ = x⁻¹ := by
    intro w hwC hw2 hwt x hxU
    have hconjG : IsConj w t :=
      (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG w hw2).trans
        (InvolutionFusion.ambient_involution_isConj_z n hn S fS hG t ht2).symm
    rcases (isConj_centered_involution_iff hn S fS hG fS hcent ⟨w, hwC⟩).mp hconjG with h | h
    · exact absurd (congrArg Subtype.val h) hwt
    · obtain ⟨c, hc⟩ := isConj_iff.mp h
      have hc' : (c : G) * w * (c : G)⁻¹ = (fS (s n) : G) := by
        have := congrArg Subtype.val hc
        simpa [coe_centeredReflection] using this
      have hyU : (c : G) * x * (c : G)⁻¹ ∈ U := by
        have hx' : (⟨x, hUC hxU⟩ : C t) ∈ U.subgroupOf (C t) := hxU
        have := hUnormal.conj_mem _ hx' c
        exact this
      obtain ⟨-, -, hys⟩ := (hU _).mp hyU
      have hw : w = (c : G)⁻¹ * (fS (s n) : G) * c := by rw [← hc']; group
      calc w * x * w⁻¹
          = (c : G)⁻¹ * ((fS (s n) : G) * ((c : G) * x * (c : G)⁻¹) * (fS (s n) : G)⁻¹) * c := by
            rw [hw]; group
        _ = x⁻¹ := by rw [hys]; group
  have hlocal : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card U → ∀ P : Sylow ℓ U,
      (∀ Q : Subgroup G, Q ≤ C t → IsPGroup ℓ Q → (P : Subgroup U).map U.subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t) ∧
      ∀ Q : Sylow ℓ (C t),
        (P : Subgroup U).map U.subtype ≤ (Q : Subgroup (C t)).map (C t).subtype →
        ∃ T : Sylow ℓ G, (T : Subgroup G) = (Q : Subgroup (C t)).map (C t).subtype := by
    intro ℓ hℓ hℓU P
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hPbot : (P : Subgroup U).map U.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective]
      exact P.ne_bot_of_dvd_card hℓU
    have hN : ∀ Q : Subgroup G, Q ≤ C t → (P : Subgroup U).map U.subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t := fun Q hQC hPQ =>
      normalizer_le_centralizer_of_confined ht2 hUodd hinv hconf (Subgroup.map_subtype_le _)
        hPbot hPQ hQC
    refine ⟨fun Q hQC _ hPQ => hN Q hQC hPQ, fun Q hPQ => ?_⟩
    exact exists_sylow_eq_map_of_normalizer_le Q
      (hN _ (Subgroup.map_subtype_le _) hPQ)
  have hU1 : Nat.card U = 1 := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hℓU⟩ := Nat.exists_prime_and_dvd hne
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow ℓ U))
    have hPp : IsPGroup ℓ (((P : Subgroup U).map U.subtype).comap (C t).subtype) :=
      (P.isPGroup'.map U.subtype).comap_of_injective (C t).subtype Subtype.val_injective
    obtain ⟨Q, hQ⟩ := hPp.exists_le_sylow
    have hPQ : (P : Subgroup U).map U.subtype ≤ (Q : Subgroup (C t)).map (C t).subtype := by
      intro x hx
      have hxC : x ∈ C t := hUC (Subgroup.map_subtype_le _ hx)
      exact ⟨⟨x, hxC⟩, hQ hx, rfl⟩
    obtain ⟨T, hT⟩ := (hlocal ℓ hℓ hℓU P).2 Q hPQ
    have hTC : (T : Subgroup G) ≤ C t := by
      rw [hT]
      exact Subgroup.map_subtype_le _
    have hdvd : ℓ ∣ (C t).index := by
      have h : (ℓ : ℤ) ∣ ((C t).index : ℤ) := by
        rw [hindex, ← hUcard]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
          (dvd_pow (Int.natCast_dvd_natCast.mpr hℓU) two_ne_zero) _) _
      exact_mod_cast h
    exact T.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hTC))
  have hb₀1 : b₀ = 1 := hUcard ▸ hU1
  refine ⟨by rw [hindex, hUcard], hlocal, Subgroup.eq_bot_of_card_eq U hU1, ?_⟩
  intro x hx
  have hxN0 : (⟨x, hx⟩ : N t) ∈ ActualFourGroupCentralizer.N0 s₀ := by
    rw [Subgroup.index_eq_one.mp hb₀1]
    exact Subgroup.mem_top _
  have h := (hN0mem ⟨x, hx⟩).mp hxN0
  exact congrArg Subtype.val h

end CFSG.Semidihedral.Principal
