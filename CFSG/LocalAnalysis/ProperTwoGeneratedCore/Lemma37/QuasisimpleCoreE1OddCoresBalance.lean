module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZ
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentULabels
public import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

private instance instDecEqPermFinFiveE1Odd : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem perm5_pow_four_of_commute : ∀ τ ρ : Perm (Fin 5), τ * τ = 1 → 4 ≤ τ.support.card →
    ρ * τ = τ * ρ → ρ ^ 4 = 1 := by
  decide +kernel

section General

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem involutionOddCore_eq_map_pPrimeCore (a : X) : involutionOddCore a =
    (CFSG.pPrimeCore 2 (Subgroup.centralizer {a})).map (Subgroup.centralizer {a}).subtype := by
  rw [involutionOddCore, oddCore_eq_pPrimeCore]

omit [Finite X] in
theorem involutionOddCore_le_centralizer (a : X) :
    involutionOddCore a ≤ Subgroup.centralizer {a} :=
  Subgroup.map_subtype_le _

omit [Finite X] in
theorem conj_mem_involutionOddCore {a g c : X} (hg : g ∈ Subgroup.centralizer {a})
    (hc : c ∈ involutionOddCore a) : g * c * g⁻¹ ∈ involutionOddCore a := by
  rw [involutionOddCore_eq_map_pPrimeCore] at hc ⊢
  exact conj_mem_map_subtype hg hc

omit [Finite X] in
theorem isPGroup_zpowers_of_mul_self {a : X} (haa : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem involutionOddCore_inf_le_of_isCharacteristicP {a b : X} (haa : a * a = 1)
    (hab : a * b = b * a) (hchar : CFSG.IsCharacteristicP 2
      (Subgroup.centralizer {b} ⧸ CFSG.pPrimeCore 2 (Subgroup.centralizer {b}))) :
    involutionOddCore a ⊓ Subgroup.centralizer {b} ≤ involutionOddCore b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPa : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) =
      Subgroup.centralizer {a} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPH : Subgroup.zpowers a ≤ Subgroup.centralizer {b} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hab)
  have key := CFSG.pPrimeCore_common_centralizer_eq X 2 _ _ hPH
    (isPGroup_zpowers_of_mul_self haa) hchar
  rw [hPa] at key
  set I := Subgroup.centralizer {b} ⊓ Subgroup.centralizer ({a} : Set X) with hI
  have hY : involutionOddCore a ⊓ Subgroup.centralizer {b} ≤
      (CFSG.pPrimeCore 2 I).map I.subtype := by
    refine le_map_pPrimeCore_of_odd (N := I) (fun g hg => ⟨1, Subgroup.one_mem _, g, hg,
      one_mul g⟩) le_rfl (le_inf inf_le_right (inf_le_left.trans
        (involutionOddCore_le_centralizer a))) (fun g hg => ?_) ?_
    · refine mem_normalizer_of_forall_conj_mem fun c hc => ⟨conj_mem_involutionOddCore hg.2 hc.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.1 hc.2) (Subgroup.inv_mem _ hg.1)⟩
    · exact (odd_card_involutionOddCore a).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  rw [key] at hY
  rw [involutionOddCore_eq_map_pPrimeCore b]
  exact hY.trans inf_le_left

end General

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem self_mul_self : (u : J ⧸ Subgroup.center J) * (u : J ⧸ Subgroup.center J) = 1 := by
  rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
    d.caseC3BCD.caseC3Word_mul_self_eq_one_iff]
  decide

theorem mem_involutionOddCore_self {v g : J ⧸ Subgroup.center J}
    (hvu : v ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) (hvv : v * v = 1)
    (hgen : CaseC3.Genuine (Subgroup.center J) ((u : J ⧸ Subgroup.center J) * v))
    (h1 : (u : J ⧸ Subgroup.center J) * v ≠ 1)
    (hgu : g ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) (hgv : g * v = v * g)
    (hodd : Odd (orderOf g)) : g ∈ involutionOddCore (u : J ⧸ Subgroup.center J) := by
  set C := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} with hC
  set s : C := centralizerSelf u * ⟨v, hvu⟩ with hs
  set c : C := ⟨g, hgu⟩ with hc
  have hvu' : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hvu
  have hgu' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgu
  have hs1 : s ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have h8 := Equiv.Perm.sum_cycleType ((d.phiU s : alternatingGroup (Fin 9)) : Perm (Fin 9))
  rw [d.cycleType_phiU_of_genuine hs1 hgen, d.coe_phiU, card_support_permNine] at h8
  dsimp only at h8
  have h4le : (d.rho4C s).support.card ≤ 4 := Finset.card_le_univ _
  have hτ : 4 ≤ (d.rho5C s).support.card := by
    have h8' : ({2, 2, 2, 2} : Multiset ℕ).sum = 8 := rfl
    omega
  have hss : s * s = 1 := Subtype.ext (by
    change (u : J ⧸ Subgroup.center J) * v * (u * v) = 1
    rw [show (u : J ⧸ Subgroup.center J) * v * (u * v) = u * (v * u) * v by group, hvu',
      show (u : J ⧸ Subgroup.center J) * (u * v) * v = u * u * (v * v) by group,
      d.self_mul_self, hvv, one_mul])
  have hcs : c * s = s * c := Subtype.ext (by
    change g * (u * v) = u * v * g
    rw [← mul_assoc, hgu', mul_assoc, hgv, ← mul_assoc])
  have h5 := perm5_pow_four_of_commute _ (d.rho5C c) (by rw [← map_mul, hss, map_one]) hτ
    (by rw [← map_mul, ← map_mul, hcs])
  have hc4 : d.rho4C c * fourRep = fourRep * d.rho4C c := by
    have hcu : c * centralizerSelf u = centralizerSelf u * c := Subtype.ext hgu'
    have := congrArg d.rho4C hcu
    rwa [map_mul, map_mul, d.rho4C_self] at this
  have h4 := perm4_pow_four_of_commute _ hc4
  have hφ : d.phiU c ^ 4 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, d.coe_phiU, ← map_pow, Prod.pow_mk, h4, h5, Prod.mk_one_one,
      map_one, OneMemClass.coe_one])
  have hφ1 : d.phiU c = 1 := by
    have h1 : orderOf (d.phiU c) ∣ 4 := orderOf_dvd_of_pow_eq_one hφ
    have h2 : orderOf (d.phiU c) ∣ orderOf g := by
      rw [← Subgroup.orderOf_mk g hgu]
      exact orderOf_map_dvd _ _
    have hcop : Nat.Coprime 4 (orderOf g) := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hker : c ∈ CFSG.pPrimeCore 2 C := by
    rw [← d.ker_phiU]
    exact hφ1
  rw [involutionOddCore_eq_map_pPrimeCore]
  exact ⟨c, hker, rfl⟩

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem involutionOddCore_inf_le_of_genuine
    {a b : J ⧸ Subgroup.center J} (haa : a * a = 1)
    (hab : a * b = b * a) (hbb : b * b = 1) (hb1 : b ≠ 1)
    (hbg : CaseC3.Genuine (Subgroup.center J) b) :
    involutionOddCore a ⊓ Subgroup.centralizer {b} ≤ involutionOddCore b :=
  involutionOddCore_inf_le_of_isCharacteristicP haa hab
    (d.card_and_isCharacteristicP_of_genuine htype hbb hb1 hbg).2

theorem mem_involutionOddCore_of_not_genuine {b v g : J ⧸ Subgroup.center J} (hbb : b * b = 1)
    (hb1 : b ≠ 1) (hbg : ¬ CaseC3.Genuine (Subgroup.center J) b)
    (hvb : v ∈ Subgroup.centralizer {b}) (hvv : v * v = 1)
    (hgen : CaseC3.Genuine (Subgroup.center J) (b * v)) (h1 : b * v ≠ 1)
    (hgb : g ∈ Subgroup.centralizer {b}) (hgv : g * v = v * g) (hodd : Odd (orderOf g)) :
    g ∈ involutionOddCore b := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp (d.isConj_self_of_not_genuine htype hbb hb1 hbg)
  set ub := (u : J ⧸ Subgroup.center J) with hub
  have hvb' : v * (h * ub * h⁻¹) = h * ub * h⁻¹ * v :=
    Subgroup.mem_centralizer_singleton_iff.mp hvb
  have hgb' : g * (h * ub * h⁻¹) = h * ub * h⁻¹ * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hgb
  have key := d.mem_involutionOddCore_self (v := h⁻¹ * v * h) (g := h⁻¹ * g * h)
    (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc h⁻¹ * v * h * ub = h⁻¹ * (v * (h * ub * h⁻¹)) * h := by group
        _ = h⁻¹ * (h * ub * h⁻¹ * v) * h := by rw [hvb']
        _ = ub * (h⁻¹ * v * h) := by group))
    (by rw [show h⁻¹ * v * h * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h by group, hvv]; group)
    (by
      have h' := CaseC3.genuine_conj _ hgen h
      rwa [show h⁻¹ * (h * ub * h⁻¹ * v) * h = ub * (h⁻¹ * v * h) by group] at h')
    (fun h0 => h1 (by
      rw [show h * ub * h⁻¹ * v = h * (ub * (h⁻¹ * v * h)) * h⁻¹ by group, h0]; group))
    (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc h⁻¹ * g * h * ub = h⁻¹ * (g * (h * ub * h⁻¹)) * h := by group
        _ = h⁻¹ * (h * ub * h⁻¹ * g) * h := by rw [hgb']
        _ = ub * (h⁻¹ * g * h) := by group))
    (by rw [show h⁻¹ * g * h * (h⁻¹ * v * h) = h⁻¹ * (g * v) * h by group, hgv]; group)
    (by
      rwa [← SemiconjBy.orderOf_eq h⁻¹ (show SemiconjBy h⁻¹ g (h⁻¹ * g * h) by
        rw [SemiconjBy]; group)])
  rw [← MulAut.conj_apply, ← involutionOddCore_map]
  exact ⟨h⁻¹ * g * h, key, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem le_involutionOddCore_of_not_genuine {b : J ⧸ Subgroup.center J} (hbb : b * b = 1)
    (hb1 : b ≠ 1) (hbg : ¬ CaseC3.Genuine (Subgroup.center J) b)
    {V Y : Subgroup (J ⧸ Subgroup.center J)} (hVb : V ≤ Subgroup.centralizer {b})
    (hV2 : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4)
    (hVgen : ∀ v ∈ V, v ≠ 1 → CaseC3.Genuine (Subgroup.center J) (b * v) ∧ b * v ≠ 1)
    (hYb : Y ≤ Subgroup.centralizer {b}) (hYodd : Odd (Nat.card Y))
    (hVY : V ≤ Subgroup.normalizer (Y : Set (J ⧸ Subgroup.center J))) :
    Y ≤ involutionOddCore b := by
  refine (le_of_eq (CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two V Y (fun v => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two, hV2 _ v.2, OneMemClass.coe_one])) (by rw [hV4]; norm_num)
    (fun h2 => (Nat.not_even_iff_odd.mpr hYodd) (even_iff_two_dvd.mpr h2)) hVY)).trans
    (iSup₂_le fun v hv => ?_)
  intro g hg
  have hv1 : (v : J ⧸ Subgroup.center J) ≠ 1 := fun h => hv (Subtype.ext h)
  obtain ⟨hgen, hne⟩ := hVgen v v.2 hv1
  exact d.mem_involutionOddCore_of_not_genuine htype hbb hb1 hbg (hVb v.2) (hV2 v v.2) hgen hne
    (hYb hg.1) (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
    (hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hg.1))

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
