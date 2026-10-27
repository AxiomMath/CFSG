module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OmegaBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZ

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

theorem orbit_centralizer_conj_eq_image {G α : Type*} [Group G] [MulAction G α] {g s : G}
    {ω : α} (hg : g • ω = ω) :
    MulAction.orbit (Subgroup.centralizer {g * s * g⁻¹}) ω =
      (fun β => g • β) '' MulAction.orbit (Subgroup.centralizer {s}) ω := by
  ext β
  refine ⟨fun hβ => ⟨g⁻¹ • β, (smul_mem_orbit_centralizer_iff hg).mp (by rwa [smul_inv_smul]),
    smul_inv_smul g β⟩, ?_⟩
  rintro ⟨β', hβ', rfl⟩
  exact (smul_mem_orbit_centralizer_iff hg).mpr hβ'

theorem c3Conj_thirtytwo_eight : ∀ w : Fin 64, (c3Conj w 32 = 32 ∨ c3Conj w 32 = 8) ∧
    (c3Conj w 8 = 32 ∨ c3Conj w 8 = 8) := by decide

theorem e1E_cases_conj_two : ∀ w : Fin 64, e1E w → w ≠ 0 → w ≠ 40 →
    w = 32 ∨ w = 8 ∨ ∃ t : Fin 64, c3Conj t 2 = w := by decide +kernel

theorem omega_words : c3Conj 1 32 = 8 ∧ c3Conj 1 2 = 2 ∧ c3Mul 32 8 = 40 ∧
    c3Mul 32 2 = c3Mul 2 32 ∧ c3Mul 2 2 = 0 := by decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

@[expose] noncomputable def deltaW (w : Fin 64) :
    Set ((J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) :=
  MulAction.orbit (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x w}) d.omegaZ

theorem deltaW_thirtytwo : d.deltaW 32 =
    MulAction.orbit (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) d.omegaZ := by
  rw [deltaW, CaseC3BCD.caseC3Word_thirtytwo]

theorem omegaZ_mem_deltaW (w : Fin 64) : d.omegaZ ∈ d.deltaW w :=
  MulAction.mem_orbit_self _

theorem word_smul_mem_deltaW_iff (t w : Fin 64)
    {β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))} :
    caseC3Word (Subgroup.center J) u m y x t • β ∈ d.deltaW (c3Conj t w) ↔ β ∈ d.deltaW w := by
  rw [deltaW, deltaW, ← d.caseC3BCD.caseC3Word_conj]
  exact smul_mem_orbit_centralizer_iff (d.word_smul_omegaZ t)

theorem smul_eq_self_of_mem_deltaW {w : Fin 64}
    {β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hβ : β ∈ d.deltaW w) : caseC3Word (Subgroup.center J) u m y x w • β = β :=
  smul_eq_self_of_mem_orbit_centralizer (d.word_smul_omegaZ w) hβ

theorem ncard_deltaW_conj (t w : Fin 64) : (d.deltaW (c3Conj t w)).ncard = (d.deltaW w).ncard := by
  rw [deltaW, deltaW, ← d.caseC3BCD.caseC3Word_conj,
    orbit_centralizer_conj_eq_image (d.word_smul_omegaZ t)]
  exact Set.ncard_image_of_injective _ (MulAction.injective _)

theorem ncard_deltaW_thirtytwo : (d.deltaW 32).ncard = 5 := by
  rw [deltaW_thirtytwo]
  exact d.ncard_orbit_omegaZ

theorem ncard_deltaW_eight : (d.deltaW 8).ncard = 5 := by
  rw [← omega_words.1, ncard_deltaW_conj, ncard_deltaW_thirtytwo]

theorem deltaW_inter : d.deltaW 32 ∩ d.deltaW 8 = {d.omegaZ} := by
  ext β
  rw [Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨h32, h8⟩ => d.eq_omegaZ_of_genuine
    (d.map_le_centralizer_forty (d.caseC3BCD.caseC3Word_mem 40)) d.caseC3BCD.genuine_forty
    d.forty_ne_one ?_, fun h => h ▸ ⟨d.omegaZ_mem_deltaW 32, d.omegaZ_mem_deltaW 8⟩⟩
  rw [← omega_words.2.2.1, ← d.caseC3BCD.caseC3Word_mul, mul_smul,
    d.smul_eq_self_of_mem_deltaW h8, d.smul_eq_self_of_mem_deltaW h32]

theorem ncard_deltaX : (d.deltaW 32 ∪ d.deltaW 8).ncard = 9 := by
  have h := Set.ncard_union_add_ncard_inter (d.deltaW 32) (d.deltaW 8)
  rw [d.deltaW_inter, Set.ncard_singleton, d.ncard_deltaW_thirtytwo, d.ncard_deltaW_eight] at h
  omega

theorem word_smul_mem_deltaX (t : Fin 64)
    {β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hβ : β ∈ d.deltaW 32 ∪ d.deltaW 8) :
    caseC3Word (Subgroup.center J) u m y x t • β ∈ d.deltaW 32 ∪ d.deltaW 8 := by
  obtain ⟨h32, h8⟩ := c3Conj_thirtytwo_eight t
  rcases hβ with hβ | hβ
  · have h := (d.word_smul_mem_deltaW_iff t 32).mpr hβ
    rcases h32 with h' | h' <;> rw [h'] at h
    exacts [Or.inl h, Or.inr h]
  · have h := (d.word_smul_mem_deltaW_iff t 8).mpr hβ
    rcases h8 with h' | h' <;> rw [h'] at h
    exacts [Or.inl h, Or.inr h]

theorem three_le_ncard_deltaW_inter
    (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥) :
    3 ≤ (d.deltaW 32 ∩ d.deltaW 2).ncard := by
  obtain ⟨hinj, hsurj⟩ := d.phiU_bijective_of_oddCore_eq_bot hOu
  obtain ⟨j₁, hj₁⟩ := d.exists_smul_omegaZ_eq_iff
  have hb := d.caseC3BCD
  have hy2 := CaseC3BCD.caseC3Word_two (Z := Subgroup.center J) (u := u) (m := m) (y := y)
    (x := x)
  have hyu : (y : J ⧸ Subgroup.center J) ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hy2,
      ← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
      hb.caseC3Word_mul, hb.caseC3Word_mul, omega_words.2.2.2.1]
  set yC : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} := ⟨_, hyu⟩
  have hy5 : d.rho5C yC = d.rho5 d.yBar := by
    rw [show yC = d.toCentralizer ⟨y, d.y_mem⟩ from Subtype.ext rfl, rho5C, liftC_toCentralizer]
    rfl
  have hsign : sign (d.rho5C yC) = -1 := by rw [hy5]; exact d.sign_rho5_yBar
  have hyy : d.rho5C yC * d.rho5C yC = 1 := by
    rw [← map_mul, show yC * yC = 1 from Subtype.ext (by
      change (y : J ⧸ Subgroup.center J) * (y : J ⧸ Subgroup.center J) = 1
      rw [← hy2, hb.caseC3Word_mul, omega_words.2.2.2.2, CaseC3BCD.caseC3Word_zero]), map_one]
  have hfix : d.rho5C yC j₁ = j₁ := by
    have h := (hj₁ yC 1).mp (by
      rw [one_smul]
      change (y : J ⧸ Subgroup.center J) • d.omegaZ = d.omegaZ
      rw [← hy2]
      exact d.word_smul_omegaZ 2)
    rwa [map_one, Perm.one_apply] at h
  have key : ∀ i : Fin 5, d.rho5C yC i = i → i ≠ j₁ →
      ∃ c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
        (c : J ⧸ Subgroup.center J) ∈
          Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 2} ∧ d.rho5C c j₁ = i := by
    intro i hi hij
    obtain ⟨hs, hc, hmap⟩ := perm5_swap_mul _ j₁ i hyy hsign hfix hi hij
    have hσA : permNine (1, swap j₁ i * d.rho5C yC) ∈ alternatingGroup (Fin 9) := by
      rw [mem_alternatingGroup, sign_permNine, hs, Perm.sign_one, mul_one]
    have hσC : (⟨_, hσA⟩ : alternatingGroup (Fin 9)) ∈ Subgroup.centralizer {altRep2A} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change permNine (1, swap j₁ i * d.rho5C yC) * altRep2 =
        altRep2 * permNine (1, swap j₁ i * d.rho5C yC)
      rw [altRep2_eq_permNine, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul,
        mul_one, one_mul, mul_one]
    obtain ⟨c, hcσ⟩ := hsurj _ hσC
    have hc' : permNine (d.rho4C c, d.rho5C c) = permNine (1, swap j₁ i * d.rho5C yC) := by
      rw [← coe_phiU, hcσ]
    have h45 := Prod.mk.inj (permNine_injective hc')
    refine ⟨c, ?_, by rw [h45.2, hmap]⟩
    have hcomm : c * yC = yC * c := hinj (Subtype.ext (by
      rw [coe_phiU, coe_phiU, map_mul, map_mul, map_mul, map_mul, h45.1, h45.2, one_mul, mul_one,
        hc]))
    rw [Subgroup.mem_centralizer_singleton_iff, hy2]
    exact congrArg Subtype.val hcomm
  obtain ⟨j, j', hj, hj', hjj', hyj, hyj'⟩ := perm5_exists_two_fixed _ hyy hsign j₁ hfix
  obtain ⟨c, hcy, hcj⟩ := key j hyj hj
  obtain ⟨c', hcy', hcj'⟩ := key j' hyj' hj'
  have hmem : ∀ c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      (c : J ⧸ Subgroup.center J) ∈
        Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 2} →
      (c : J ⧸ Subgroup.center J) • d.omegaZ ∈ d.deltaW 32 ∩ d.deltaW 2 := fun c hc =>
    ⟨d.deltaW_thirtytwo ▸ ⟨c, rfl⟩, ⟨⟨_, hc⟩, rfl⟩⟩
  have hne : ∀ c c' : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      d.rho5C c j₁ ≠ d.rho5C c' j₁ →
        (c : J ⧸ Subgroup.center J) • d.omegaZ ≠ (c' : J ⧸ Subgroup.center J) • d.omegaZ :=
    fun c c' h h' => h ((hj₁ c c').mp h')
  have hsub : ({d.omegaZ, (c : J ⧸ Subgroup.center J) • d.omegaZ,
      (c' : J ⧸ Subgroup.center J) • d.omegaZ} : Set _) ⊆ d.deltaW 32 ∩ d.deltaW 2 := by
    rintro β (rfl | rfl | rfl)
    exacts [⟨d.omegaZ_mem_deltaW 32, d.omegaZ_mem_deltaW 2⟩, hmem c hcy, hmem c' hcy']
  have h3 : ({d.omegaZ, (c : J ⧸ Subgroup.center J) • d.omegaZ,
      (c' : J ⧸ Subgroup.center J) • d.omegaZ} : Set _).ncard = 3 := by
    rw [Set.ncard_eq_three]
    refine ⟨_, _, _, ?_, ?_, hne c c' (by rw [hcj, hcj']; exact hjj'), rfl⟩
    · have h := hne 1 c (by rw [hcj, map_one, Perm.one_apply]; exact Ne.symm hj)
      rwa [OneMemClass.coe_one, one_smul] at h
    · have h := hne 1 c' (by rw [hcj', map_one, Perm.one_apply]; exact Ne.symm hj')
      rwa [OneMemClass.coe_one, one_smul] at h
  rw [← h3]
  exact Set.ncard_le_ncard hsub

theorem three_le_ncard_deltaW_inter'
    (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥) :
    3 ≤ (d.deltaW 8 ∩ d.deltaW 2).ncard := by
  have hsub : (fun β => caseC3Word (Subgroup.center J) u m y x 1 • β) ''
      (d.deltaW 32 ∩ d.deltaW 2) ⊆ d.deltaW 8 ∩ d.deltaW 2 := by
    rintro _ ⟨β, ⟨h32, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← omega_words.1]
      exact (d.word_smul_mem_deltaW_iff 1 32).mpr h32
    · rw [← omega_words.2.1]
      exact (d.word_smul_mem_deltaW_iff 1 2).mpr h2
  calc 3 ≤ (d.deltaW 32 ∩ d.deltaW 2).ncard := d.three_le_ncard_deltaW_inter hOu
    _ = ((fun β => caseC3Word (Subgroup.center J) u m y x 1 • β) ''
        (d.deltaW 32 ∩ d.deltaW 2)).ncard :=
      (Set.ncard_image_of_injective _ (MulAction.injective _)).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem ncard_deltaW_two : (d.deltaW 2).ncard = 5 := by
  obtain ⟨h, hh, hhu⟩ := d.exists_centralizer_conj_two htype
  rw [deltaW, CaseC3BCD.caseC3Word_two, ← hhu, orbit_centralizer_conj_eq_image (d.smul_omegaZ hh),
    Set.ncard_image_of_injective _ (MulAction.injective _)]
  exact d.ncard_orbit_omegaZ

theorem deltaW_two_subset
    (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥) :
    d.deltaW 2 ⊆ d.deltaW 32 ∪ d.deltaW 8 := by
  have hA : 3 ≤ (d.deltaW 2 ∩ d.deltaW 32).ncard := by
    rw [Set.inter_comm]; exact d.three_le_ncard_deltaW_inter hOu
  have hA' : 3 ≤ (d.deltaW 2 ∩ d.deltaW 8).ncard := by
    rw [Set.inter_comm]; exact d.three_le_ncard_deltaW_inter' hOu
  set A := d.deltaW 2 ∩ d.deltaW 32
  set A' := d.deltaW 2 ∩ d.deltaW 8
  have hAA : (A ∩ A').ncard ≤ 1 := by
    rw [← Set.ncard_singleton d.omegaZ, ← d.deltaW_inter]
    exact Set.ncard_le_ncard fun β hβ => ⟨hβ.1.2, hβ.2.2⟩
  have hU := Set.ncard_union_add_ncard_inter A A'
  have hsub : A ∪ A' ⊆ d.deltaW 2 := Set.union_subset Set.inter_subset_left Set.inter_subset_left
  have heq : A ∪ A' = d.deltaW 2 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [d.ncard_deltaW_two htype]; omega)
  intro β hβ
  rw [← heq] at hβ
  rcases hβ with hβ | hβ
  exacts [Or.inl hβ.2, Or.inr hβ.2]

theorem deltaW_subset_deltaX
    (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥)
    {w : Fin 64} (hw : e1E w) (hw0 : w ≠ 0) (hw40 : w ≠ 40) :
    d.deltaW w ⊆ d.deltaW 32 ∪ d.deltaW 8 := by
  rcases e1E_cases_conj_two w hw hw0 hw40 with rfl | rfl | ⟨t, rfl⟩
  · exact Set.subset_union_left
  · exact Set.subset_union_right
  · intro β hβ
    rw [← smul_inv_smul (caseC3Word (Subgroup.center J) u m y x t) β] at hβ ⊢
    exact d.word_smul_mem_deltaX t
      (d.deltaW_two_subset htype hOu ((d.word_smul_mem_deltaW_iff t 2).mp hβ))

theorem smul_mem_deltaX_of_mem_centralizer
    (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥)
    (hOz : CFSG.pPrimeCore 2
      (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = ⊥)
    {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    {β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hβ : β ∈ d.deltaW 32 ∪ d.deltaW 8) : g • β ∈ d.deltaW 32 ∪ d.deltaW 8 := by
  have hb := d.caseC3BCD
  have key : ∀ w : Fin 64, e1E w → w ≠ 0 → w ≠ 40 → β ∈ d.deltaW w →
      g • β ∈ d.deltaW 32 ∪ d.deltaW 8 := by
    intro w hw hw0 hw40 hβw
    have hE := d.conj_mem_e1EBar_sup_pPrimeCore htype hg (hb.caseC3Word_mem_e1EBar_iff.mpr hw)
    rw [hOz, Subgroup.map_bot, sup_bot_eq] at hE
    obtain ⟨w', hw', hw'g⟩ := hb.mem_e1EBar_iff.mp hE
    have hw'0 : w' ≠ 0 := by
      rintro rfl
      rw [CaseC3BCD.caseC3Word_zero, eq_comm, conj_eq_one_iff, hb.caseC3Word_eq_one_iff] at hw'g
      exact hw0 hw'g
    have hw'40 : w' ≠ 40 := by
      rintro rfl
      apply hw40
      rw [← hb.caseC3Word_inj]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc caseC3Word (Subgroup.center J) u m y x w =
            g⁻¹ * (g * caseC3Word (Subgroup.center J) u m y x w * g⁻¹) * g := by group
        _ = g⁻¹ * caseC3Word (Subgroup.center J) u m y x 40 * g := by rw [← hw'g]
        _ = caseC3Word (Subgroup.center J) u m y x 40 := by
          rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
    have h := (smul_mem_orbit_centralizer_iff (d.smul_omegaZ hg)).mpr hβw
    rw [← hw'g] at h
    exact d.deltaW_subset_deltaX htype hOu hw' hw'0 hw'40 h
  rcases hβ with hβ | hβ
  · exact key 32 (by decide) (by decide) (by decide) hβ
  · exact key 8 (by decide) (by decide) (by decide) hβ

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
