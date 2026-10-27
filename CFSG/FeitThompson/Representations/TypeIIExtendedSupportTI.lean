module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NonTypeISigmaCoreIdentities
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Local.ResidualExteriorPowerTI
import CFSG.FeitThompson.Representations.TypeIIIVExtendedDadeSupport
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

theorem coe_sup_E_W₁ (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    ((E ⊔ W₁ : Subgroup G) : Set G) = (E : Set G) * (W₁ : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left E W₁ hc.le_normalizer_E

theorem isInternalSemidirectProduct_E_sup_W₁ (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    FreeCore.IsInternalSemidirectProduct (E ⊔ W₁) E W₁ where
  sup_eq := rfl
  le_normalizer := sup_le le_normalizer hc.le_normalizer_E
  disjoint := disjoint_iff.2 (le_bot_iff.1
    (le_trans (inf_le_inf_right W₁ hc.le_commutator_E) hc.disjoint_commutator_W₁.le_bot))

theorem sigmaCore_inf_sup_E_W₁ (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hHS : (hallCore ↥M).map M.subtype = sigmaCore M) : sigmaCore M ⊓ (E ⊔ W₁) = ⊥ := by
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨hxH, hxEW⟩ := Subgroup.mem_inf.1 hx
  rw [← SetLike.mem_coe, coe_sup_E_W₁ hc] at hxEW
  obtain ⟨e, he, w, hw, rfl⟩ := Set.mem_mul.1 hxEW
  rw [← hHS] at hxH
  have hxM' : e * w ∈ (⁅M, M⁆ : Subgroup G) := hc.hallCore_le_commutator hxH
  have hwM' : w ∈ (⁅M, M⁆ : Subgroup G) := by
    have hrw : w = e⁻¹ * (e * w) := by group
    rw [hrw]
    exact mul_mem (inv_mem (hc.le_commutator_E he)) hxM'
  have hw1 : w = 1 :=
    Subgroup.mem_bot.1 (hc.disjoint_commutator_W₁.le_bot (Subgroup.mem_inf.2 ⟨hwM', hw⟩))
  have heH : e ∈ (hallCore ↥M).map M.subtype := by rw [hw1, mul_one] at hxH; exact hxH
  have he1 : e = 1 :=
    Subgroup.mem_bot.1 (hc.disjoint_hallCore_E.le_bot (Subgroup.mem_inf.2 ⟨heH, he⟩))
  simp [he1, hw1]

theorem isInternalSemidirectProduct_sigmaCore_sup_E_W₁
    (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hHS : (hallCore ↥M).map M.subtype = sigmaCore M) :
    FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (E ⊔ W₁) where
  sup_eq := by rw [← hHS, ← sup_assoc, hc.sup_hallCore_E, hc.sup_commutator_W₁]
  le_normalizer := le_normalizer_sigmaCore M
  disjoint := disjoint_iff.2 (sigmaCore_inf_sup_E_W₁ hc hHS)

theorem mem_sigmaCore_of_isConj [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) {a y : G} (ha : a ∈ sigmaCore M) (hy : y ∈ M) (hconj : IsConj a y) :
    y ∈ sigmaCore M := by
  rw [mem_sigmaCore_iff_primeFactors_orderOf hna hodd hsolv hM hy, ← orderOf_eq_of_isConj hconj]
  exact primeFactors_orderOf_subset_sigmaPrimes ha

theorem mem_of_conj_mem_hallCoreSharp (hTI : IsTIWithNormalizer (fittingRawSharp M) M)
    {a b g : G} (ha : a ∈ hallCoreSharp M) (hb : b ∈ hallCoreSharp M) (hg : g⁻¹ * a * g = b) :
    g ∈ M :=
  mem_of_conj_mem_of_isTIWithNormalizer hTI (hallCoreSharp_subset_fittingRawSharp M ha)
    (hg ▸ hallCoreSharp_subset_fittingRawSharp M hb)

theorem mem_of_conj_mem_conjUnion (hc : IsWitnessedPConfiguration M E W₁ W₂)
    {a b g : G} (ha : a ∈ Prep09.conjUnion M (cyclicTIset W₁ W₂))
    (hb : b ∈ Prep09.conjUnion M (cyclicTIset W₁ W₂)) (hg : g⁻¹ * a * g = b) : g ∈ M := by
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 ha
  obtain ⟨n, hn, w, hw, rfl⟩ := mem_mixedConj.1 hb
  have ht : (m * g * n⁻¹)⁻¹ * v * (m * g * n⁻¹) = w := by
    calc (m * g * n⁻¹)⁻¹ * v * (m * g * n⁻¹)
        = n * (g⁻¹ * (m⁻¹ * v * m) * g) * n⁻¹ := by group
      _ = n * (n⁻¹ * w * n) * n⁻¹ := by rw [hg]
      _ = w := by group
  have htM : m * g * n⁻¹ ∈ M := hc.le_M_sup_W₁_W₂
    (mem_of_conj_mem_of_isTIWithNormalizer hc.isTIWithNormalizer_cyclicTIset hv (ht ▸ hw))
  have hgeq : g = m⁻¹ * (m * g * n⁻¹) * n := by group
  rw [hgeq]
  exact mul_mem (mul_mem (inv_mem hm) htM) hn

omit [Finite G] in
theorem conj_mem_conjUnion {a m : G} (ha : a ∈ Prep09.conjUnion M (cyclicTIset W₁ W₂))
    (hm : m ∈ M) : m⁻¹ * a * m ∈ Prep09.conjUnion M (cyclicTIset W₁ W₂) := by
  obtain ⟨n, hn, v, hv, rfl⟩ := Prep09.mem_conjUnion.1 ha
  exact Prep09.mem_conjUnion.2 ⟨n * m, mul_mem hn hm, v, hv, by group⟩

theorem centIn_hallCoreIn_eq (hHS : (hallCore ↥M).map M.subtype = sigmaCore M) (a : G) :
    Prep09.centIn (Prep09.hallCoreIn M) {a} = sigmaCore M ⊓ centralizer ({a} : Set G) := by
  rw [Prep09.centIn_def, Prep09.hallCoreIn_def, hHS]

theorem conj_mem_coreFixedSet_commutator (hHS : (hallCore ↥M).map M.subtype = sigmaCore M)
    {a m : G} (ha : a ∈ Prep09.coreFixedSet (Prep09.hallCoreIn M) (⁅M, M⁆ : Subgroup G))
    (hm : m ∈ M) :
    m⁻¹ * a * m ∈ Prep09.coreFixedSet (Prep09.hallCoreIn M) (⁅M, M⁆ : Subgroup G) := by
  obtain ⟨haM, ha1, hac⟩ := ha
  rw [centIn_hallCoreIn_eq hHS] at hac
  refine ⟨(Subgroup.mem_normalizer_iff''.1 (Subgroup.normalizer_commutator_ge_left M M hm) a).1
    haM, fun hcon => ha1 ?_, ?_⟩
  · have hback : a = m * (m⁻¹ * a * m) * m⁻¹ := by group
    rw [hback, hcon]; group
  · rw [centIn_hallCoreIn_eq hHS]
    exact inf_centralizer_conj_ne_bot (le_normalizer_sigmaCore M hm) hac

omit [Finite G] in
theorem normalizer_eq_and_ti_of_pointwise_fusion {A : Set G} {N : Subgroup G}
    (hne : A.Nonempty) (hstab : ∀ a ∈ A, ∀ m ∈ N, m⁻¹ * a * m ∈ A)
    (hfus : ∀ a ∈ A, ∀ b ∈ A, ∀ g : G, g⁻¹ * a * g = b → g ∈ N) :
    normalizer A = N ∧ ∀ g : G, g ∉ N → A ∩ Prep09.conjSet g A = ∅ := by
  refine ⟨le_antisymm (fun g hg => ?_) (fun m hm => ?_), fun g hg => ?_⟩
  · obtain ⟨a, ha⟩ := hne
    exact hfus a ha _ ((Subgroup.mem_set_normalizer_iff''.1 hg a).1 ha) g rfl
  · refine Subgroup.mem_set_normalizer_iff''.2 fun x => ⟨fun hx => hstab x hx m hm, fun hx => ?_⟩
    have h := hstab _ hx m⁻¹ (inv_mem hm)
    simpa [mul_assoc] using h
  · refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hg ?_
    obtain ⟨hxA, a, ha, hax⟩ := hx
    exact hfus a ha x (hax ▸ hxA) g hax

theorem FTS_type_II_extended_support_ti
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FBG_local_p_core_centralizer.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_core_centralizing_external_element_dichotomy.{u})
    (h₈ : Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    (h₉ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FTS_type_II_extended_support_ti.{u} := by
  intro G _ _ hG M E W₁ W₂ hM hII hw A₀ hA₀
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hc : IsWitnessedPConfiguration M E W₁ W₂ := hw.1.isWitnessedPConfiguration
  have hTIF : IsTIWithNormalizer (fittingRawSharp M) M := hw.1.isTIWithNormalizer_fittingRawSharp
  have hamb5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    { odd_natCard := hG.odd_natCard, isSimpleGroup := hG.isSimpleGroup,
      not_isMulCommutative := hG.not_isMulCommutative,
      isSolvable_of_ne_top := hG.isSolvable_of_ne_top }
  have hamb4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    { odd_natCard := hG.odd_natCard, isSimpleGroup := hG.isSimpleGroup,
      not_isMulCommutative := hG.not_isMulCommutative,
      isSolvable_of_ne_top := hG.isSolvable_of_ne_top }
  have hamb8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    { odd_natCard := hG.odd_natCard, isSimpleGroup := hG.isSimpleGroup,
      not_isMulCommutative := hG.not_isMulCommutative,
      isSolvable_of_ne_top := hG.isSolvable_of_ne_top }
  have hHS : (hallCore ↥M).map M.subtype = sigmaCore M :=
    ((FPF_non_type_i_sigma_core_identities h₁ h₂ h₃ h₄ h₅ h₆ h₈ h₉ G hamb5 M hM).1 hII).symm
  have hW₁Hall : CFSG.FeitThompson.IsHallPiSubgroup (kappaPrimes M)
      (W₁.subgroupOf M) :=
    (FNI_p_configuration_kappa_factors h₄ h₅ G hamb4 M E W₁ W₂ hM hc).2.1
  have hM'eq : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ E := by rw [← hHS, hc.sup_hallCore_E]
  set A : Set G := Prep09.coreFixedSet (Prep09.hallCoreIn M) (⁅M, M⁆ : Subgroup G) with hAdef
  set V : Set G := Prep09.conjUnion M (cyclicTIset W₁ W₂) with hVdef
  set D : Set G := {y | y ∈ sigmaCore M ⊔ E ∧ y ∉ sigmaCore M ∧
    sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥} with hDdef
  have hresidual := fun (hne : D.Nonempty) =>
    (FTS_residual_exterior_power_ti h₄ h₅ h₇ G hamb8 M W₁ E (sigmaCore M ⊔ E) hM
      ⟨hc.le_M_W₁, hW₁Hall⟩ hc.le_M_E (isInternalSemidirectProduct_sigmaCore_sup_E_W₁ hc hHS)
      (isInternalSemidirectProduct_E_sup_W₁ hc) rfl D hDdef).2 hne
  have hAsplit : ∀ a ∈ A, a ∈ hallCoreSharp M ∨ a ∈ D := by
    intro a ha
    obtain ⟨haM, ha1, hac⟩ := ha
    rw [centIn_hallCoreIn_eq hHS] at hac
    by_cases hS : a ∈ sigmaCore M
    · exact Or.inl (mem_hallCoreSharp.2 ⟨by rw [hHS]; exact hS, ha1⟩)
    · exact Or.inr ⟨hM'eq ▸ haM, hS, hac⟩
  have hfusA : ∀ a ∈ A, ∀ b ∈ A, ∀ g : G, g⁻¹ * a * g = b → g ∈ M := by
    intro a ha b hb g hg
    have haM' : a ∈ (⁅M, M⁆ : Subgroup G) := ha.1
    have hbM' : b ∈ (⁅M, M⁆ : Subgroup G) := hb.1
    have hconj : IsConj a b := isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩
    rcases hAsplit a ha with haH | haD
    · rcases hAsplit b hb with hbH | hbD
      · exact mem_of_conj_mem_hallCoreSharp hTIF haH hbH hg
      · exact absurd (mem_sigmaCore_of_isConj hG.not_isMulCommutative hG.odd_natCard
          hG.isSolvable_of_ne_top hM (by rw [← hHS]; exact (mem_hallCoreSharp.1 haH).1)
          (Subgroup.commutator_le_self M hbM') hconj) hbD.2.1
    · rcases hAsplit b hb with hbH | hbD
      · exact absurd (mem_sigmaCore_of_isConj hG.not_isMulCommutative hG.odd_natCard
          hG.isSolvable_of_ne_top hM (by rw [← hHS]; exact (mem_hallCoreSharp.1 hbH).1)
          (Subgroup.commutator_le_self M haM') hconj.symm) haD.2.1
      · exact (hresidual ⟨a, haD⟩).2.2.1 a haD b hbD g hg
  have hA₀eq : A₀ = A ∪ V := hA₀
  have hfus : ∀ a ∈ A₀, ∀ b ∈ A₀, ∀ g : G, g⁻¹ * a * g = b → g ∈ M := by
    intro a ha b hb g hg
    have hconj : IsConj a b := isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩
    rw [hA₀eq] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact hfusA a ha b hb g hg
      · exact absurd hconj.symm (not_isConj_mixedConj_commutator hc hb ha.1)
    · rcases hb with hb | hb
      · exact absurd hconj (not_isConj_mixedConj_commutator hc ha hb.1)
      · exact mem_of_conj_mem_conjUnion hc ha hb hg
  have hstab : ∀ a ∈ A₀, ∀ m ∈ M, m⁻¹ * a * m ∈ A₀ := by
    intro a ha m hm
    rw [hA₀eq] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (conj_mem_coreFixedSet_commutator hHS ha hm)
    · exact Or.inr (conj_mem_conjUnion ha hm)
  have hne : A₀.Nonempty := by
    obtain ⟨w, hw2⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_W₂
    have hw1 : (w : G) ≠ 1 := by simpa using hw2
    have hwS : (w : G) ∈ sigmaCore M := hHS ▸ hc.le_hallCore_W₂ w.2
    refine ⟨(w : G), ?_⟩
    rw [hA₀eq]
    refine Or.inl ⟨hM'eq ▸ (le_sup_left : sigmaCore M ≤ sigmaCore M ⊔ E) hwS, hw1, ?_⟩
    rw [centIn_hallCoreIn_eq hHS]
    exact (Subgroup.ne_bot_iff_exists_ne_one).2
      ⟨⟨(w : G), Subgroup.mem_inf.2 ⟨hwS, mem_centralizer_singleton_iff.2 rfl⟩⟩,
        by simpa using hw1⟩
  have hsubset : A₀ ⊆ (M : Set G) \ {1} := by
    rw [hA₀eq]
    refine Set.union_subset (fun a ha => ⟨Subgroup.commutator_le_self M ha.1, ha.2.1⟩)
      fun a ha => ⟨mixedConj_subset hc.le_M_sup_W₁_W₂ ha, fun h1 => ?_⟩
    exact one_notMem_mixedConj M W₁ W₂ (by rw [← Set.mem_singleton_iff.1 h1]; exact ha)
  obtain ⟨hnorm, hdisj⟩ := normalizer_eq_and_ti_of_pointwise_fusion hne hstab hfus
  refine ⟨hHS, hne, hsubset, hnorm, hdisj, hfus, fun a ha => ?_⟩
  have hle : centralizer ({a} : Set G) ≤ M := by
    intro g hg
    refine hfus a ha a ha g ?_
    have hcomm := (mem_centralizer_singleton_iff.1 hg).symm
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [hcomm]
      _ = a := by group
  rw [Prep09.centIn_def, inf_eq_right.2 hle]

end

end CFSG.FeitThompson.Proofs
