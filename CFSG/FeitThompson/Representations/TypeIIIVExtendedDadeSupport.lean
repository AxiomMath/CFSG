module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreFusion
import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocks
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import Mathlib
import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality
import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson (IsFTAmbient sigmaSupport mem_sigmaSupport
  sigmaSignalizer mem_sigmaSupportingMaximals sigmaSignalizer_le_centralizer)

universe u

variable {G : Type u} [Group G]

theorem orderOf_dvd_natCard_of_mem [Finite G] {W : Subgroup G} {w : G} (hw : w ∈ W) :
    orderOf w ∣ Nat.card ↥W := by
  have h : orderOf ((⟨w, hw⟩ : ↥W) : G) ∣ Nat.card ↥W := by
    rw [Subgroup.orderOf_coe]; exact orderOf_dvd_natCard _
  exact h

theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have he : ((MulAut.conj c).toMonoidHom) a = b := hc
  rw [← he, orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a]

theorem mem_mixedConj {M W₁ W₂ : Subgroup G} {x : G} :
    x ∈ Prep06.mixedConj M W₁ W₂ ↔ ∃ m ∈ M, ∃ v ∈ cyclicTIset W₁ W₂, m⁻¹ * v * m = x := by
  rw [Prep06.mixedConj_eq]
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]

theorem mem_of_conj_mem_of_isTIWithNormalizer {D : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D L) {v g : G} (hv : v ∈ D) (hvg : g⁻¹ * v * g ∈ D) : g ∈ L := by
  by_contra hg
  exact Set.disjoint_left.1 (h.disjoint_image_conj_inv hg) hvg ⟨v, hv, rfl⟩

theorem centralizer_le_of_isTIWithNormalizer {D : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D L) {v : G} (hv : v ∈ D) : centralizer ({v} : Set G) ≤ L := by
  intro g hg
  refine mem_of_conj_mem_of_isTIWithNormalizer h hv ?_
  have hcomm : v * g = g * v := (Subgroup.mem_centralizer_iff.1 hg) v rfl
  have he : g⁻¹ * v * g = v := by
    calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
      _ = g⁻¹ * (g * v) := by rw [hcomm]
      _ = v := by group
  rw [he]; exact hv

theorem mem_centralizer_conj {m v g : G} (hg : g ∈ centralizer ({m⁻¹ * v * m} : Set G)) :
    m * g * m⁻¹ ∈ centralizer ({v} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcomm : (m⁻¹ * v * m) * g = g * (m⁻¹ * v * m) := (Subgroup.mem_centralizer_iff.1 hg) _ rfl
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  calc v * (m * g * m⁻¹) = m * ((m⁻¹ * v * m) * g) * m⁻¹ := by group
    _ = m * (g * (m⁻¹ * v * m)) * m⁻¹ := by rw [hcomm]
    _ = (m * g * m⁻¹) * v := by group

theorem one_notMem_mixedConj (M W₁ W₂ : Subgroup G) : (1 : G) ∉ Prep06.mixedConj M W₁ W₂ := by
  intro hx
  obtain ⟨m, hm, v, hv, hv1⟩ := mem_mixedConj.1 hx
  have hveq : v = 1 := by
    have he : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
    rw [hv1] at he; simpa using he.symm
  exact (mem_cyclicTIset.1 hv).2.1 (hveq ▸ one_mem W₁)

theorem mixedConj_subset {M W₁ W₂ : Subgroup G} (hW : W₁ ⊔ W₂ ≤ M) :
    Prep06.mixedConj M W₁ W₂ ⊆ (M : Set G) := by
  intro x hx
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 hx
  exact mul_mem (mul_mem (inv_mem hm) (hW (mem_cyclicTIset.1 hv).1)) hm

theorem mixedConj_conj_mem {M W₁ W₂ : Subgroup G} {a : G} (ha : a ∈ Prep06.mixedConj M W₁ W₂)
    {x : G} (hx : x ∈ M) : x * a * x⁻¹ ∈ Prep06.mixedConj M W₁ W₂ := by
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 ha
  refine mem_mixedConj.2 ⟨m * x⁻¹, mul_mem hm (inv_mem hx), v, hv, ?_⟩
  group

theorem exists_mem_conj_eq_of_mem_mixedConj [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {a b : G}
    (ha : a ∈ Prep06.mixedConj M W₁ W₂) (hb : b ∈ Prep06.mixedConj M W₁ W₂) (hab : IsConj a b) :
    ∃ x ∈ M, x * a * x⁻¹ = b := by
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 ha
  obtain ⟨n, hn, w, hw, rfl⟩ := mem_mixedConj.1 hb
  obtain ⟨c, hcv⟩ := isConj_iff.1 hab
  set g : G := m * c⁻¹ * n⁻¹ with hgdef
  have hgvw : g⁻¹ * v * g = w := by
    have h1 : c * (m⁻¹ * v * m) * c⁻¹ = n⁻¹ * w * n := hcv
    have h2 : n * (c * (m⁻¹ * v * m) * c⁻¹) * n⁻¹ = w := by rw [h1]; group
    rw [hgdef]
    calc (m * c⁻¹ * n⁻¹)⁻¹ * v * (m * c⁻¹ * n⁻¹)
        = n * (c * (m⁻¹ * v * m) * c⁻¹) * n⁻¹ := by group
      _ = w := h2
  have hgM : g ∈ M := hc.le_M_sup_W₁_W₂
    (mem_of_conj_mem_of_isTIWithNormalizer hc.isTIWithNormalizer_cyclicTIset hv (hgvw ▸ hw))
  refine ⟨n⁻¹ * g⁻¹ * m, mul_mem (mul_mem (inv_mem hn) (inv_mem hgM)) hm, ?_⟩
  calc (n⁻¹ * g⁻¹ * m) * (m⁻¹ * v * m) * (n⁻¹ * g⁻¹ * m)⁻¹
      = n⁻¹ * (g⁻¹ * v * g) * n := by group
    _ = n⁻¹ * w * n := by rw [hgvw]

theorem exists_mem_conj_eq_of_mem_commutator [Finite G]
    (h₄ : Statements.FTS_canonical_signalizer_structure.{u})
    (hG : Prep06.IsMinimalOddSimple G) {M : Subgroup G} (hM : IsCoatom M)
    (hS : sigmaCore M = ⁅M, M⁆) {a b : G} (ha : a ∈ (⁅M, M⁆ : Subgroup G))
    (hb : b ∈ (⁅M, M⁆ : Subgroup G)) (hab : IsConj a b) : ∃ x ∈ M, x * a * x⁻¹ = b := by
  have hfus := FTS_sigma_core_fusion h₄
  have hamb8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    { isSimpleGroup := hG.simple, not_isMulCommutative := hG.nonabelian,
      odd_natCard := hG.odd, isSolvable_of_ne_top := hG.solvable }
  obtain ⟨c, hc⟩ := isConj_iff.1 hab
  have hb' : (c⁻¹)⁻¹ * a * c⁻¹ = b := by
    have he : (c⁻¹)⁻¹ * a * c⁻¹ = c * a * c⁻¹ := by group
    rw [he, hc]
  obtain ⟨m, hm, hmeq⟩ := hfus G hamb8 M hM a (hS ▸ ha) c⁻¹ (by rw [hS, hb']; exact hb)
  refine ⟨m⁻¹, inv_mem hm, ?_⟩
  rw [← hb', hmeq]
  group

theorem not_coprime_orderOf_of_mem_cyclicTIset [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {v : G} (hv : v ∈ cyclicTIset W₁ W₂) :
    ¬ (orderOf v).Coprime (Nat.card ↥W₁) := by
  obtain ⟨hvW, hvW₁, hvW₂⟩ := mem_cyclicTIset.1 hv
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ : v ∈ (W₁ : Set G) * (W₂ : Set G) := by
    rw [← hc.coe_sup_W₁_W₂]; exact hvW
  have hw₁1 : w₁ ≠ 1 := fun h => hvW₂ (by simpa [h] using hw₂)
  have hd₁ : orderOf w₁ ∣ Nat.card ↥W₁ := orderOf_dvd_natCard_of_mem hw₁
  have hw₂M : w₂ ∈ (⁅M, M⁆ : Subgroup G) := hc.hallCore_le_commutator (hc.le_hallCore_W₂ hw₂)
  have hcop12 : (orderOf w₁).Coprime (orderOf w₂) :=
    Nat.Coprime.coprime_dvd_left hd₁ (Nat.Coprime.coprime_dvd_right
      (orderOf_dvd_natCard_of_mem hw₂M) hc.coprime_natCard_W₁_natCard_commutator)
  have hord : orderOf (w₁ * w₂) = orderOf w₁ * orderOf w₂ :=
    (hc.commute_W₁_W₂ hw₁ hw₂).orderOf_mul_eq_mul_orderOf_of_coprime hcop12
  intro hcop
  have hdvd : orderOf w₁ ∣ orderOf (w₁ * w₂) := hord ▸ Dvd.intro _ rfl
  exact hw₁1 (orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hd₁))

theorem not_isConj_mixedConj_commutator [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {a b : G}
    (ha : a ∈ Prep06.mixedConj M W₁ W₂) (hb : b ∈ (⁅M, M⁆ : Subgroup G)) : ¬ IsConj a b := by
  intro hab
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 ha
  have hva : IsConj v (m⁻¹ * v * m) := isConj_iff.2 ⟨m⁻¹, by group⟩
  refine not_coprime_orderOf_of_mem_cyclicTIset hc hv ?_
  rw [orderOf_eq_of_isConj (hva.trans hab)]
  exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard_of_mem hb)
    hc.coprime_natCard_W₁_natCard_commutator.symm

theorem notMem_sdiff_of_mem_mixedConj [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {a : G} (ha : a ∈ Prep06.mixedConj M W₁ W₂) :
    a ∉ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} :=
  fun h => not_isConj_mixedConj_commutator hc ha h.1 (IsConj.refl a)

theorem dadeT_of_mem_mixedConj [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {a : G} (ha : a ∈ Prep06.mixedConj M W₁ W₂) :
    Prep06.dadeT M a = ⊥ :=
  Prep06.dadeT_of_notMem (notMem_sdiff_of_mem_mixedConj hc ha)

theorem centralizer_le_M_of_mem_mixedConj [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) {a : G} (ha : a ∈ Prep06.mixedConj M W₁ W₂) :
    centralizer ({a} : Set G) ≤ M := by
  obtain ⟨m, hm, v, hv, rfl⟩ := mem_mixedConj.1 ha
  intro g hg
  have hmg : m * g * m⁻¹ ∈ M := hc.le_M_sup_W₁_W₂
    (centralizer_le_of_isTIWithNormalizer hc.isTIWithNormalizer_cyclicTIset hv
      (mem_centralizer_conj hg))
  have he : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [he]
  exact mul_mem (mul_mem (inv_mem hm) hmg) hm

theorem dadeA0_subset [Finite G] {M E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    Prep06.dadeA0 M W₁ W₂ ⊆ (M : Set G) \ {1} := by
  rw [Prep06.dadeA0_eq]
  refine Set.union_subset (fun x hx => ⟨Subgroup.commutator_le_self M hx.1, hx.2⟩) ?_
  intro x hx
  refine ⟨mixedConj_subset hc.le_M_sup_W₁_W₂ hx, fun h => ?_⟩
  exact one_notMem_mixedConj M W₁ W₂ (by rw [← Set.mem_singleton_iff.1 h]; exact hx)

theorem dadeA0_conj_mem {M W₁ W₂ : Subgroup G} {a : G} (ha : a ∈ Prep06.dadeA0 M W₁ W₂)
    {x : G} (hx : x ∈ M) : x * a * x⁻¹ ∈ Prep06.dadeA0 M W₁ W₂ := by
  rw [Prep06.dadeA0_eq] at ha ⊢
  rcases ha with ha | ha
  · refine Or.inl ⟨?_, fun h => ha.2 ?_⟩
    · have hMn := (Subgroup.normalizer_commutator_ge_left M M) hx
      rw [Subgroup.mem_normalizer_iff] at hMn
      exact (hMn a).1 ha.1
    · have he : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [Set.mem_singleton_iff, he, Set.mem_singleton_iff.1 h]
      simp
  · exact Or.inr (mixedConj_conj_mem ha hx)

open scoped Classical in
theorem dadeTau_isometry_clauses [Fintype G] {M W₁ W₂ : Subgroup G}
    (hD : IsDadeData M (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M))
    (f g : ↥M → ℂ) (hf : f ∈ classFun ↥M) (hg : g ∈ classFun ↥M)
    (hf0 : ∀ x : ↥M, (x : G) ∉ Prep06.dadeA0 M W₁ W₂ → f x = 0)
    (hg0 : ∀ x : ↥M, (x : G) ∉ Prep06.dadeA0 M W₁ W₂ → g x = 0) :
    Prep06.dadeTau M W₁ W₂ (f + g)
        = Prep06.dadeTau M W₁ W₂ f + Prep06.dadeTau M W₁ W₂ g ∧
      (∀ c : ℂ, Prep06.dadeTau M W₁ W₂ (c • f) = c • Prep06.dadeTau M W₁ W₂ f) ∧
      cfInner (Prep06.dadeTau M W₁ W₂ f) (Prep06.dadeTau M W₁ W₂ g) = cfInner f g ∧
      (f ∈ virtualChars ↥M → Prep06.dadeTau M W₁ W₂ f ∈ virtualChars G) ∧
      Prep06.dadeTau M W₁ W₂ f ∈ classFun G := by
  have hfd : f ∈ dadeDomain M (Prep06.dadeA0 M W₁ W₂) := mem_dadeDomain.2 ⟨hf, hf0⟩
  have hgd : g ∈ dadeDomain M (Prep06.dadeA0 M W₁ W₂) := mem_dadeDomain.2 ⟨hg, hg0⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Prep06.dadeTau_eq]
    exact dadeMapFun_add M (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M) f g
  · intro c
    simp only [Prep06.dadeTau_eq]
    exact dadeMapFun_smul M (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M) c f
  · simp only [Prep06.dadeTau_eq]
    exact PrimeDadeSubcoherence.cfInner_dadeMapFun hD hfd hgd
  · intro hfv
    simp only [Prep06.dadeTau_eq]
    exact mem_virtualChars_of_mem_span_Irr
      (PrimeDadeSubcoherence.dadeMapFun_mem_span_Irr hD hfd (virtualChars_le_span_Irr hfv))
  · have h := (dadeMap hD ⟨f, hfd⟩).2
    rw [coe_dadeMap hD ⟨f, hfd⟩] at h
    simpa only [Prep06.dadeTau_eq] using h

theorem isDadeData_dadeA0
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₃ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₄ : Statements.FTS_canonical_signalizer_structure.{u})
    [Fintype G] (hG : Prep06.IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsDadeData M (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M) := by
  classical
  have hamb7 : IsFTAmbient G :=
    { isSimpleGroup := hG.simple, not_isMulCommutative := hG.nonabelian,
      odd_natCard := hG.odd, isSolvable := hG.solvable }
  have hamb5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    { odd_natCard := hG.odd, isSimpleGroup := hG.simple,
      not_isMulCommutative := hG.nonabelian, isSolvable_of_ne_top := hG.solvable }
  have hamb4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    { odd_natCard := hG.odd, isSimpleGroup := hG.simple,
      not_isMulCommutative := hG.nonabelian, isSolvable_of_ne_top := hG.solvable }
  have hS : sigmaCore M = ⁅M, M⁆ := (h₂ G hamb5 M hM).2 htype
  have hkappa : (kappaPrimes M).Nonempty := (h₁ G hamb4 M U W₁ W₂ hM hc).1
  have hcoreU : ∀ a ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1}, a ∈ sigmaSupport G := by
    intro a ha
    exact mem_sigmaSupport.2 ⟨M, hM, hS ▸ ha.1, by simpa using ha.2⟩
  refine
    { subset_sdiff := dadeA0_subset hc
      conj_mem := fun {a} ha {x} hx => dadeA0_conj_mem ha hx
      fusion := ?_
      le_centralizer := ?_
      normal_subgroupOf := ?_
      inf_eq_bot := ?_
      mul_eq := ?_
      coprime_card := ?_ }
  ·
    intro a ha b hb hab
    rw [Prep06.dadeA0_eq] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      ·
        exact exists_mem_conj_eq_of_mem_commutator h₄ hG hM hS ha.1 hb.1 hab
      ·
        exact absurd hab.symm (not_isConj_mixedConj_commutator hc hb ha.1)
    · rcases hb with hb | hb
      ·
        exact absurd hab (not_isConj_mixedConj_commutator hc ha hb.1)
      ·
        exact exists_mem_conj_eq_of_mem_mixedConj hc ha hb hab
  ·
    intro a ha
    rw [Prep06.dadeA0_eq] at ha
    rcases ha with ha | ha
    · rw [Prep06.dadeT_of_mem ha]; exact sigmaSignalizer_le_centralizer a
    · rw [dadeT_of_mem_mixedConj hc ha]; exact bot_le
  ·
    intro a ha
    rw [Prep06.dadeA0_eq] at ha
    rcases ha with ha | ha
    · rw [Prep06.dadeT_of_mem ha]; exact (h₄ G hamb7 a (hcoreU a ha)).1
    · rw [dadeT_of_mem_mixedConj hc ha, Subgroup.bot_subgroupOf]; infer_instance
  ·
    intro a ha
    rw [Prep06.dadeA0_eq] at ha
    rcases ha with ha | ha
    · rw [Prep06.dadeT_of_mem ha]
      exact ((h₄ G hamb7 a (hcoreU a ha)).2.2.2.2.1 M
        (mem_sigmaSupportingMaximals.2 ⟨hM, hS ▸ ha.1⟩)).1.inf_eq_bot
    · rw [dadeT_of_mem_mixedConj hc ha]; exact bot_inf_eq _
  ·
    intro a ha
    rw [Prep06.dadeA0_eq] at ha
    rcases ha with ha | ha
    · rw [Prep06.dadeT_of_mem ha]
      exact (((h₄ G hamb7 a (hcoreU a ha)).2.2.2.2.1 M
        (mem_sigmaSupportingMaximals.2 ⟨hM, hS ▸ ha.1⟩)).1.coe_eq_mul).symm
    · rw [dadeT_of_mem_mixedConj hc ha]
      have hle : centralizer ({a} : Set G) ≤ M := centralizer_le_M_of_mem_mixedConj hc ha
      have hinf : M ⊓ centralizer ({a} : Set G) = centralizer ({a} : Set G) :=
        inf_eq_right.2 hle
      rw [hinf]
      simp
  ·
    intro a ha b hb
    rw [Prep06.dadeA0_eq] at ha
    rcases ha with ha | ha
    · rw [Prep06.dadeT_of_mem ha]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left : M ⊓ centralizer ({b} : Set G) ≤ M))
        ((h₃ G hamb7 M hM).2 hkappa a (hS ▸ ha.1) (by simpa using ha.2))
    · rw [dadeT_of_mem_mixedConj hc ha]
      simp [Nat.Coprime]

open scoped Classical in
theorem FPF_type_iii_v_extended_dade_support
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₃ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₄ : Statements.FTS_canonical_signalizer_structure.{u}) :
    Statements.FPF_type_iii_v_extended_dade_support.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  have hD : IsDadeData M (Prep06.dadeA0 M W₁ W₂) (Prep06.dadeT M) :=
    isDadeData_dadeA0 h₁ h₂ h₃ h₄ hG hM htype hc
  refine ⟨hD.subset_sdiff, ?_, ?_, hD, ?_⟩
  ·
    intro a ha m hm
    simpa using hD.conj_mem ha (inv_mem hm)
  ·
    intro a ha b hb hab
    obtain ⟨x, hx, hxab⟩ := hD.fusion ha hb hab
    exact ⟨x⁻¹, inv_mem hx, by simpa using hxab⟩
  ·
    intro f g hf hg hf0 hg0
    exact dadeTau_isometry_clauses hD f g hf hg hf0 hg0

end

end CFSG.FeitThompson.Proofs
