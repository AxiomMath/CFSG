module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueDataLocal
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueDataCharacters
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueSetup
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueInterim

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.Principal
  (actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor)
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element)

theorem exists_dValueData
    (hθ : CentralizerCharacterTrivialStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hLnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq4 : p ^ f % 4 = 1)
    (hq5 : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥) :
    ∃ (_ : Fintype G) (D : UnitaryDValue.DValueData G), D.m = 2 ∧ D.p = p ∧ D.f = f ∧
      Nat.card D.A = Nat.card (N t) ∧ D.CharacterExtend ∧ D.CharacterTrivial ∧
      D.PrincipalPair := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpne : p ≠ 2 := fun h => (Nat.not_even_iff_odd.mpr hpodd) (h ▸ even_two)
  have hG2 : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  have : Group.IsPerfect G := StationaryLayerCover.isPerfect_of_nonabelian hGnonab
  obtain ⟨hz, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  set s₀ : G := (fS (s n) : G) with hs₀
  set A : Subgroup G := (N t).map (C t).subtype with hAdef
  obtain ⟨-, hNcent, hNcyc, -, hNdvd, ⟨F, hF, hFfin, κ, hD⟩, hCcard, hDcard, hGcard⟩ :=
    unitary_order_formulas G hGnonab hrec n hn S fS t ht hLnonab hcentral hnc p f hp hpodd hf hq4
      hq5 hmodel hcov hY hA₀
  obtain ⟨hval, -, hNA, -⟩ :=
    actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor
      G hGnonab hrec n hn S fS t ht hLnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov hY hA₀
  have hconf := (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
    G hGnonab hrec n hn S fS t s₀ ht2 hs2 hsC hst.symm hLnonab hcentral hnc p f hp hpodd hf hq5
    hmodel hcov).2.1
  obtain ⟨hSC, -⟩ := sylow_le_and_normalizer_le_centralizer n hn S fS ht
  have hsS : s₀ ∈ (S : Subgroup G) := (fS (s n)).2
  have htS : t ∈ (S : Subgroup G) := hz ▸ (fS (z n)).2
  have hcover := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage
    t s₀ hcov
  obtain ⟨W, hWmem, hWcyc, hWcard, ⟨eD, heD⟩, -, -, d, hdK, -, -, -, hds, -, hdW, -⟩ :=
    Principal.FieldFactorOneFixedCore.field_factor_one_torus_local_data G n hn S fS hG2 t ht2 hSC
      s₀ hsS hs2 hst hLnonab hcentral hnc p f hp hpodd hf hq5.le hmodel hcover hY
  have hqe : (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) = p ^ f + 1 :=
    ite_eq_left_iff.mpr (fun h => absurd hq4 h)
  rw [hqe] at hWcard
  obtain ⟨g, hgt, hgs⟩ := exists_cycling_element n hn S fS htS hsS ht2 hs2 hsC hst.symm
  have hAcard : Nat.card A = Nat.card (N t) :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hAcent : ∀ a ∈ A, ∀ g ∈ Subgroup.centralizer ({t} : Set G), g * a = a * g := by
    rintro _ ⟨r, hr, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hNcent hr) ⟨g, hg⟩)
  have hAcyc : IsCyclic A := by
    let ρ := Subgroup.equivMapOfInjective (N t) (C t).subtype (C t).subtype_injective
    exact isCyclic_of_surjective ρ.toMonoidHom ρ.surjective
  have hAodd : ∀ a ∈ A, Odd (orderOf a) := fun a ha =>
    (hAcard ▸ hNodd).of_dvd_nat (Subgroup.orderOf_dvd_natCard A ha)
  have hts : t * s₀ = s₀ * t := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have ht2' : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hs2' : s₀ * s₀ = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hVK := StationaryOddLocalization.actual_involution_pair_isKleinFour t s₀ ht2 hs2 hsC
    hst.symm
  obtain ⟨hCcomm, hCinv, hWA₀⟩ := torus_product_facts hts ht2' hs2' hVK eD heD
    (fun a ha b hb => (hAcent a ha.1 b (Subgroup.map_subtype_le _ hb.1)).symm) hWcyc
    (fun a ha => hAodd a ha.1) (fun w hw => ((hWmem w).mp hw).2.2)
  have hWA : W ⊓ A = ⊥ := by
    rw [← hWA₀]
    exact congrArg (W ⊓ ·) hNA
  have hWle : W ≤ Subgroup.centralizer {t} ⊓ Subgroup.centralizer {s₀} := by
    intro w hw
    obtain ⟨hwJ, hws, -⟩ := (hWmem w).mp hw
    exact ⟨Subgroup.map_subtype_le _ hwJ, Subgroup.mem_centralizer_singleton_iff.mpr hws⟩
  have hWcent : ∀ w ∈ W, w ≠ 1 →
      Subgroup.centralizer {t} ⊓ Subgroup.centralizer {w} ≤ Subgroup.centralizer {s₀} := by
    intro w hw hw1
    refine centralizer_le_of_torus hD hDcard hCcomm (hWle hw) ?_ ?_
    · rw [← hWcard]
      exact Subgroup.orderOf_dvd_natCard W hw
    · intro hwA
      have hmem : w ∈ W ⊓ A := ⟨hw, hwA⟩
      rw [hWA] at hmem
      exact hw1 hmem
  have hchar := unitary_principal_characters G hGnonab n hn S fS t ht hLnonab hcentral hnc p f hp
    hpodd hf hq4 hmodel hval
  obtain ⟨π, hπ⟩ := unitary_retraction hG2 n hn S fS t ht hLnonab hcentral hnc p f hp hpodd hf
    hq5 hmodel hcov hY hNcent hNdvd
  have h2dvd : 2 ∣ p ^ f + 1 := ⟨(p ^ f + 1) / 2, by omega⟩
  refine ⟨inferInstance,
    { p := p, f := f, m := 2, x := t, z := s₀, y := d, t := g, A := A, W := W, S := S,
      prime_p := hp, ne_two := hpne, one_le_f := hf, five_lt_q := hq5,
      m_pow := ⟨1, (pow_one 2).symm⟩, m_dvd := h2dvd, odd_quot := ⟨p ^ f / 4, by omega⟩,
      index_ne_two := hG2, x_order := ht2,
      involution_conj := fun i hi => hz ▸ InvolutionFusion.ambient_involution_isConj_z n hn S fS
        hG2 i hi,
      z_order := hs2, z_comm := hts, z_ne := hst,
      A_le := Subgroup.map_subtype_le _, A_central := hAcent, A_cyclic := hAcyc,
      A_odd := hAcard ▸ hNodd,
      A_dvd := by
        rw [hAcard]
        exact (Nat.dvd_div_iff_mul_dvd h2dvd).mp hNdvd,
      A_confine := hconf,
      card_G := by rw [hAcard]; exact hGcard,
      card_N := by rw [hAcard]; exact hCcard,
      card_C := by rw [hAcard]; exact hDcard,
      C_comm := hCcomm, C_involutions := hCinv, W_cyclic := hWcyc,
      W_card := by omega, W_le := hWle, W_inf_A := hWA,
      y_comm := (Subgroup.mem_centralizer_singleton_iff.mp hdK.2).symm, y_z := hds,
      y_W := hdW, t_x := hgt, t_z := hgs, S_le := hSC, W_centralizer := hWcent,
      real_odd_degree := fun basis χ hreal hodd => (hchar basis).2 χ hreal hodd },
    rfl, rfl, rfl, hAcard, ?_, ?_, ?_⟩
  ·
    intro θ₀
    let ρ := Subgroup.equivMapOfInjective (N t) (C t).subtype (C t).subtype_injective
    refine ⟨θ₀.comp (ρ.toMonoidHom.comp π), ?_, ?_⟩
    · intro c hc
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨c, hc⟩
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hk
      have h1 : orderOf (π c) ∣ 2 ^ k := hk ▸ orderOf_map_dvd π c
      have h2 : orderOf (π c) ∣ Nat.card (N t) := orderOf_dvd_natCard _
      have hπc : π c = 1 := by
        rw [← orderOf_eq_one_iff]
        exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k
          (Nat.coprime_two_left.mpr hNodd)) h1 h2
      change θ₀ (ρ (π c)) = 1
      rw [hπc, map_one, map_one]
    · intro c hc
      obtain ⟨r, hr, hrc⟩ := id hc
      have hcr : c = r := Subtype.ext hrc.symm
      have h1 : π c = ⟨r, hr⟩ := by
        rw [hcr]
        exact hπ ⟨r, hr⟩
      change θ₀ (ρ (π c)) = θ₀ ⟨c, hc⟩
      rw [h1]
      congr 1
      exact Subtype.ext hrc
  ·
    intro θ hθS hθN
    exact hθ G hGnonab n hn S fS t ht hLnonab hcentral hnc p f hp hpodd hf (by omega) hmodel θ
      hθS hθN
  ·
    intro basis
    exact (hchar basis).1

end CFSG.Semidihedral.UnitaryBranch
