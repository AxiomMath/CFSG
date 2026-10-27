module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.DadeInductionExtendedSupportTypeII
import CFSG.FeitThompson.Representations.TypeIIIVExtendedDadeSupport
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Representations.TypeIFrobeniusCoherentFamily
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem derSignalizer_eq_dadeT [Finite G] (M : Subgroup G) :
    Prep05.derSignalizer M = Prep06.dadeT M := by
  funext a
  have hd : Prep05.derSignalizer M
      = Prep05.signalizerOn (((⁅M, M⁆ : Subgroup G) : Set G) \ {1}) := rfl
  by_cases ha : a ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1}
  · rw [hd, Prep05.signalizerOn_of_mem ha, Prep06.dadeT_of_mem ha,
      Prep05.signalizer_eq, Prep06.sigSignalizer_eq]
    rfl
  · rw [hd, Prep05.signalizerOn_of_notMem ha, Prep06.dadeT_of_notMem ha]

theorem extendZero_eq_extendByZero {X : Subgroup G} (f : ↥X → ℂ) :
    Prep05.extendZero f = extendByZero X f := by
  funext x
  by_cases hx : x ∈ X
  · rw [extendByZero_of_mem _ hx]
    exact X.subtype_injective.extend_apply f 0 ⟨x, hx⟩
  · rw [extendByZero_of_notMem _ _ hx]
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨a, rfl⟩
    exact hx a.2

theorem indToTop_eq_indClassFun [Fintype G] (X : Subgroup G) (f : ↥X → ℂ) :
    Prep05.indToTop X f = indClassFun X f := by
  have h : (Fintype.ofFinite G) = (inferInstance : Fintype G) := Subsingleton.elim _ _
  change @indClassFun G _ X (Fintype.ofFinite G) f = _
  rw [h]

theorem tauDerived_eq [Finite G] (M W₁ W₂ : Subgroup G) (f : ↥M → ℂ) :
    Prep05.tauDerived M W₁ W₂ f =
      dadeSupportExtension (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M) (extendByZero M f) := by
  have h1 : Prep05.tauDerived M W₁ W₂ f =
      dadeSupportExtension (Prep06.dadeA0 M W₁ W₂) (Prep05.derSignalizer M)
        (Prep05.extendZero f) := rfl
  rw [h1, derSignalizer_eq_dadeT, extendZero_eq_extendByZero]

theorem one_lt_sigmaMultiplicity_of_ne [Finite G] {a : G} {M N : Subgroup G}
    (hM : M ∈ sigmaSupportingMaximals a) (hN : N ∈ sigmaSupportingMaximals a) (hne : M ≠ N) :
    1 < sigmaMultiplicity a := by
  rw [sigmaMultiplicity_eq_ncard]
  exact Set.one_lt_ncard_iff_nontrivial_and_finite.2 ⟨⟨M, hM, N, hN, hne⟩, Set.toFinite _⟩

theorem mem_of_conj_mem_of_isDadeData [Finite G] {M : Subgroup G} {A : Set G}
    {J : G → Subgroup G} (hD : IsDadeData M A J)
    (hCle : ∀ a ∈ A, centralizer ({a} : Set G) ≤ M)
    {a : G} (ha : a ∈ A) {g : G} (hag : g * a * g⁻¹ ∈ A) : g ∈ M := by
  obtain ⟨x, hx, hxeq⟩ := hD.fusion ha hag (isConj_iff.2 ⟨g, rfl⟩)
  have hgx : x⁻¹ * g ∈ centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : x * a * x⁻¹ = g * a * g⁻¹ := hxeq
    have h3 : a = x⁻¹ * (g * a * g⁻¹) * x := by rw [← h2]; group
    calc (x⁻¹ * g) * a = x⁻¹ * (g * a * g⁻¹) * (g * g⁻¹) * g := by group
      _ = x⁻¹ * (g * a * g⁻¹) * g := by group
      _ = (x⁻¹ * (g * a * g⁻¹) * x) * (x⁻¹ * g) := by group
      _ = a * (x⁻¹ * g) := by rw [← h3]
  have hmemM := hCle a ha hgx
  have he : g = x * (x⁻¹ * g) := by group
  rw [he]; exact mul_mem hx hmemM

theorem isTIWithNormalizer_of_isDadeData [Finite G] {M : Subgroup G} {A : Set G}
    {J : G → Subgroup G} (hD : IsDadeData M A J) (hne : A.Nonempty)
    (hCle : ∀ a ∈ A, centralizer ({a} : Set G) ≤ M) :
    IsTIWithNormalizer A M where
  nonempty := hne
  one_notMem := hD.one_notMem
  normalizer_eq := by
    refine le_antisymm (fun g hg => ?_) (fun m hm => ?_)
    · obtain ⟨a, ha⟩ := hne
      have himg := Subgroup.mem_normalizer_iff_conj_image_eq.1 hg
      have hmem : g * a * g⁻¹ ∈ A := himg ▸ ⟨a, ha, rfl⟩
      exact mem_of_conj_mem_of_isDadeData hD hCle ha hmem
    · refine Subgroup.mem_normalizer_iff_conj_image_eq.2 (le_antisymm ?_ ?_)
      · rintro x ⟨y, hy, rfl⟩
        exact hD.conj_mem hy hm
      · intro x hx
        refine ⟨m⁻¹ * x * m, ?_, ?_⟩
        · simpa using hD.conj_mem hx (inv_mem hm)
        · simp only [MulAut.conj_apply]; group
  disjoint_conj_image := by
    intro g hg
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    exact hg (mem_of_conj_mem_of_isDadeData hD hCle hy (by simpa using hx))

theorem eq_bot_of_isDadeData_of_centralizer_le [Finite G] {M : Subgroup G} {A : Set G}
    {J : G → Subgroup G} (hD : IsDadeData M A J)
    {a : G} (ha : a ∈ A) (hCle : centralizer ({a} : Set G) ≤ M) : J a = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h1 : J a ≤ M ⊓ centralizer ({a} : Set G) :=
    le_inf ((hD.le_centralizer ha).trans hCle) (hD.le_centralizer ha)
  have h2 : J a ≤ J a ⊓ (M ⊓ centralizer ({a} : Set G)) := le_inf le_rfl h1
  rw [hD.inf_eq_bot ha] at h2
  exact h2

theorem extendByZero_conj_invariant {M : Subgroup G} {f : ↥M → ℂ} (hf : IsClassFun f)
    {m : G} (hm : m ∈ M) (z : G) :
    extendByZero M f (m⁻¹ * z * m) = extendByZero M f z := by
  by_cases hzM : z ∈ M
  · have hcm : m⁻¹ * z * m ∈ M := mul_mem (mul_mem (inv_mem hm) hzM) hm
    rw [extendByZero_of_mem _ hcm, extendByZero_of_mem _ hzM]
    refine hf.apply_eq (isConj_iff.2 ⟨(⟨m, hm⟩ : ↥M), Subtype.ext ?_⟩)
    change m * (m⁻¹ * z * m) * m⁻¹ = z
    group
  · have hcm : m⁻¹ * z * m ∉ M := by
      intro h
      refine hzM ?_
      have hmem : m * (m⁻¹ * z * m) * m⁻¹ ∈ M := mul_mem (mul_mem hm h) (inv_mem hm)
      have he : m * (m⁻¹ * z * m) * m⁻¹ = z := by group
      rwa [he] at hmem
    rw [extendByZero_of_notMem _ _ hcm, extendByZero_of_notMem _ _ hzM]

theorem centralizer_le_of_mem_dadeA0
    (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : Statements.FPF_type_I_frobenius.{u})
    (h₆ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₇ : Statements.FTS_signalizer_supporting_type_exterior.{u})
    (h₈ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₉ : Statements.FTS_type_I_dade_support.{u})
    [Finite G] (hG : Prep06.IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (hMIII : IsTypeIII M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {a : G} (ha : a ∈ Prep06.dadeA0 M W₁ W₂) :
    centralizer ({a} : Set G) ≤ M := by
  have : Fintype G := Fintype.ofFinite G
  have hsimple := hG.simple
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG03 : Prep03.IsAmbient G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG05 : Prep05.IsMinimalSimpleOdd G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG07 : IsFTAmbient G := ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩
  have hkappaM : (kappaPrimes M).Nonempty :=
    (FNI_p_configuration_kappa_factors h₁ h₂ G hG04 M U W₁ W₂ hM hc).1
  have hSM : sigmaCore M = ⁅M, M⁆ := (h₃ G hG05 M hM).2 (Or.inl hMIII)
  rw [Prep06.dadeA0_eq] at ha
  rcases ha with ha | ha
  ·
    by_contra hCM
    obtain ⟨g, hgc, hgM⟩ := Set.not_subset.1 hCM
    have ha1 : a ≠ 1 := by simpa using ha.2
    have hsig : a ∈ sigmaCore M := hSM ▸ ha.1
    have hgca : g⁻¹ * a * g = a := by
      have hcomm : a * g = g * a := (Subgroup.mem_centralizer_iff.1 hgc) a rfl
      calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
        _ = g⁻¹ * (g * a) := by rw [hcomm]
        _ = a := by group
    have hNco : IsCoatom (M.map (MulAut.conj g : G →* G)) := isCoatom_map_conj hM g
    have hNsig : a ∈ sigmaCore (M.map (MulAut.conj g : G →* G)) := by
      rw [mem_sigmaCore_map_conj_iff, hgca]; exact hsig
    have hNne : M ≠ M.map (MulAut.conj g : G →* G) := by
      intro h
      have hnorm : normalizer (M : Set G) = M :=
        normalizer_coe_eq_of_isCoatom hG.nonabelian hM
      refine hgM (SetLike.mem_coe.2 ?_)
      rw [← hnorm]
      refine Subgroup.mem_normalizer_iff_conj_image_eq.2 ?_
      have hset := congrArg (fun X : Subgroup G => (X : Set G)) h.symm
      simpa [Subgroup.coe_map] using hset
    have hk : 1 < sigmaMultiplicity a :=
      one_lt_sigmaMultiplicity_of_ne (mem_sigmaSupportingMaximals.2 ⟨hM, hsig⟩)
        (mem_sigmaSupportingMaximals.2 ⟨hNco, hNsig⟩) hNne
    have haU : a ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, hsig, ha1⟩
    obtain ⟨⟨L, ⟨hLco, hLle⟩, hLuniq⟩, -⟩ := h₈ G hG09 a haU hk
    have hL : IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) L :=
      ⟨hLco, hLle, fun {Y} hY hYle => hLuniq Y ⟨hY, hYle⟩⟩
    obtain ⟨htype, -, -, -, hI, -⟩ := h₇ G hG09 a haU hk L hL
    rcases htype with hLI | hLII
    ·
      obtain ⟨hAset, -⟩ := FCH_type_I_frobenius_coherent_family h₄ h₉ G hG03 L hLco hLI
      obtain ⟨⟨haL, ha1', hcent⟩, hout⟩ := hI hLI
      refine hout ?_
      have hmem : a ∈ {x : G | x ∈ L ∧ x ≠ 1 ∧ Prep03.cent1 (Prep03.hallCoreIn L) x ≠ ⊥} :=
        ⟨haL, ha1', hcent⟩
      rw [hAset] at hmem
      exact hmem
    ·
      obtain ⟨E₀, V₁, V₂, hcfg, -⟩ := hLII.exists_isPConfigurationIIToIV
      obtain ⟨hkL, -, -⟩ :=
        FNI_p_configuration_kappa_factors h₁ h₂ G hG04 L E₀ V₁ V₂ hLco
          hcfg.isWitnessedPConfiguration
      obtain ⟨hkM, -⟩ := h₆ G hG07 M hM L hLco a hsig ha1 hCM hLle hkL
      exact absurd hkM (Set.nonempty_iff_ne_empty.1 hkappaM)
  ·
    exact centralizer_le_M_of_mem_mixedConj hc ha

theorem FPF_type_iii_full_support_ti_induction
    (h₁ : Statements.FNI_kappa_local_pair.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₄ : Statements.FPF_type_I_frobenius.{u})
    (h₅ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₆ : Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₇ : Statements.FTS_signalizer_supporting_type_exterior.{u})
    (h₈ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₉ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_iii_full_support_ti_induction.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hMIII hc A₀ hA₀
  have : Fintype G := Fintype.ofFinite G
  have hG06 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hA₀eq : A₀ = Prep06.dadeA0 M W₁ W₂ := hA₀
  subst hA₀eq
  obtain ⟨hsub, -, -, hD, -⟩ := h₅ G hG06 M U W₁ W₂ hM (Or.inl hMIII) hc
  have hCle : ∀ a ∈ Prep06.dadeA0 M W₁ W₂, centralizer ({a} : Set G) ≤ M := fun a ha =>
    centralizer_le_of_mem_dadeA0 h₁ h₂ h₃ h₄ h₆ h₇ h₈ h₉ hG06 hM hMIII hc ha
  have hne : (Prep06.dadeA0 M W₁ W₂).Nonempty := by
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_W₂
    exact ⟨(w : G), Prep06.sdiff_subset_dadeA0 M W₁ W₂
      ⟨hc.hallCore_le_commutator (hc.le_hallCore_W₂ w.2), by simpa using hw⟩⟩
  have hTI : IsTIWithNormalizer (Prep06.dadeA0 M W₁ W₂) M :=
    isTIWithNormalizer_of_isDadeData hD hne hCle
  refine ⟨hne, hTI.normalizer_eq, ?_, ?_, ?_⟩
  ·
    intro g hg
    exact Set.disjoint_iff_inter_eq_empty.1 (hTI.disjoint_image_conj_inv hg)
  ·
    intro a ha
    have hle := hCle a ha
    refine ⟨?_, ?_⟩
    · rw [Prep05.centralizerIn_eq, centralizer_coe_zpowers, inf_eq_right.2 hle]
    · rw [derSignalizer_eq_dadeT]
      exact eq_bot_of_isDadeData_of_centralizer_le hD ha hle
  ·
    intro f hf hf0
    have hvanish : ∀ z : G, z ∉ Prep06.dadeA0 M W₁ W₂ → extendByZero M f z = 0 := by
      intro z hz
      by_cases hzM : z ∈ M
      · rw [extendByZero_of_mem _ hzM]; exact hf0 ⟨z, hzM⟩ hz
      · rw [extendByZero_of_notMem _ _ hzM]
    have hconj : ∀ m ∈ M, ∀ z : G, extendByZero M f (m⁻¹ * z * m) = extendByZero M f z :=
      fun m hm z => extendByZero_conj_invariant hf hm z
    rw [tauDerived_eq, dadeSupportExtension_eq_indClassFun hD hTI hvanish hconj,
      indToTop_eq_indClassFun]
    congr 1
    funext x
    exact extendByZero_apply_coe M f x

end CFSG.FeitThompson.Proofs

end
