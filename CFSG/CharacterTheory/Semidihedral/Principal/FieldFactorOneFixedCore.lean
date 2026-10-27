module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreTorus
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinement
public import CFSG.CharacterTheory.Semidihedral.Principal.ConfinedOddFactorTorusOrbit

public section

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
open CFSG.Semidihedral.StationaryConfinement

theorem actual_field_factor_one_fixed_odd_core_gives_six_element_torus_character_orbit
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (t : G) (htS : t ∈ (S : Subgroup G)) (htZ : ∀ x ∈ (S : Subgroup G), x * t = t * x)
    (ht1 : t ≠ 1) (s : G) (hsS : s ∈ (S : Subgroup G)) (hs : orderOf s = 2) (hst : s ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t s)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {s} ≠ ⊥) :
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let V : Subgroup G := Subgroup.closure {t, s}
    let A₀ : Subgroup G := (N t).map (C t).subtype ⊓ Subgroup.centralizer {s}
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    let K : Subgroup G := M ⊓ C t
    let qe : ℕ := if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1
    ∃ W : Subgroup G,
      (∀ x : G, x ∈ W ↔ x ∈ J.map (C t).subtype ∧ x * s = s * x ∧ Odd (orderOf x)) ∧
      IsCyclic W ∧ Nat.card W = qe / 2 ∧ Odd (qe / 2) ∧ 1 < qe / 2 ∧
      (∃ e : (V × A₀ × W) ≃* D, ∀ x : V × A₀ × W, (e x : G) = x.1 * x.2.1 * x.2.2) ∧
      (A₀.subgroupOf K).Normal ∧ ⁅(S : Subgroup G), A₀⁆ = ⊥ ∧
      Subgroup.centralizer (A₀ : Set G) ≤ C t ∧
      Subgroup.normalizer (A₀ : Set G) ⊓ M = K ∧
      Function.Surjective V.normalizerMonoidHom ∧ V.normalizerMonoidHom.ker = D.subgroupOf M ∧
      K.relIndex M = 3 ∧ D.relIndex K = 2 ∧
      (∃ d ∈ K, d ∉ D ∧ orderOf d = 4 ∧ d ^ 2 = t ∧ (∀ a ∈ A₀, d * a = a * d) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧
      M ≤ Subgroup.normalizer (D : Set G) ∧
      (∃ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A₀ → ω x = 1) ∧
        ∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) ∧
      ∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A₀ → ω x = 1) →
        (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
        (∀ x : D, ω x = 1 ↔ (x : G) ∈ V ⊔ A₀) ∧
        (∀ m : Subgroup.normalizer (D : Set G), (m : G) ∈ M →
          (conjugateLinearCharacter m ω = ω ↔ (m : G) ∈ D)) ∧
        (conjugateLinearCharacters M ω).ncard = 6 ∧
        (∀ χ ∈ conjugateLinearCharacters M ω, (conjugateLinearCharacters K χ).ncard = 2) ∧
        ((conjugateLinearCharacters M ω).image (conjugateLinearCharacters K)).ncard = 3 := by
  intro L T₀ Y H₀ J V A₀ D M K qe
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : (S : Subgroup G) ≤ C t := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htZ x hx)
  obtain ⟨ht, hZ⟩ := central_involution_facts hn S fS htS htZ ht1
  have hsC : s ∈ C t := hSC hsS
  have hts : t ≠ s := fun h => hst h.symm
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have : Group.IsPerfect G := StationaryLayerCover.isPerfect_of_nonabelian hGnonab
  have hcov' := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage t s
    hcov
  obtain ⟨W, hWmem, hWcyc, hWcard, hDVAW, hA₀K, hSA₀, d, hdK, hdD, hd4, hd2, -, hdA, hdW, hdx⟩ :=
    field_factor_one_torus_local_data G n hn S fS hG t ht hSC s hsS hs hst hnonab hcentral hnc
      p f hp hpodd hf hq.le hmodel hcov' hY
  obtain ⟨-, hcent, -, -⟩ :=
    stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
      G hGnonab hrecognition n hn S fS t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hcov
  have hCA : Subgroup.centralizer (A₀ : Set G) ≤ C t := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₀
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans
      (hcent a (Subgroup.mem_inf.mp ha).1 ha1')
  have hVK : IsKleinFour V :=
    StationaryOddLocalization.actual_involution_pair_isKleinFour t s ht hs hsC hts
  have hVS : V ≤ (S : Subgroup G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact hsS
  have hsurj : Function.Surjective V.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp ((Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS
      hVK).1
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hAodd : Odd (Nat.card A₀) := by
    have h1 : Nat.card A₀ ∣ Nat.card ((N t).map (C t).subtype) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [Subgroup.card_map_of_injective (C t).subtype_injective] at h1
    exact hNodd.of_dvd_nat h1
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hWodd : Odd (Nat.card W) := hWcard ▸ odd_half_torusOrder hqodd
  have hW1 : 1 < Nat.card W := hWcard ▸ one_lt_half_torusOrder hq
  obtain ⟨hNMA, hMN, hex, hall, hMK, hKD⟩ :=
    confined_odd_factor_gives_free_six_element_torus_character_orbit S t hZ ht V hVK htV (C t)
      D M K rfl rfl rfl rfl hsurj A₀ W hDVAW hAodd hWcyc hWodd hW1 hA₀K hSA₀ hCA
      ⟨d, hdK, hdD, hdx⟩
  exact ⟨W, hWmem, hWcyc, hWcard, odd_half_torusOrder hqodd, one_lt_half_torusOrder hq, hDVAW,
    hA₀K, hSA₀, hCA, hNMA, hsurj, Subgroup.normalizerMonoidHom_ker V, hMK, hKD,
    ⟨d, hdK, hdD, hd4, hd2, hdA, hdW⟩, hMN, hex, hall⟩

end CFSG.Semidihedral.Principal
