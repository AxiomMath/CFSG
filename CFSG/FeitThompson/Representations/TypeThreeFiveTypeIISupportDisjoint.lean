module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup Prep06
open _root_.CFSG.FeitThompson.Prep05
  (conjClosure leftCosetSet fixedSet centralizerIn signalizer hallCoreOf IsConjugateSubgroup)

universe u

section Aux

variable {G : Type*} [Group G]

theorem mem_conjClosure_iff' {S : Set G} {x : G} :
    x ∈ conjClosure S ↔ ∃ g : G, ∃ y ∈ S, g⁻¹ * y * g = x := by
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, hyx⟩ :=
      _root_.CFSG.FeitThompson.Prep05.mem_conjSet.1 hg
    exact ⟨g, y, hy, hyx⟩
  · rintro ⟨g, y, hy, hyx⟩
    exact Set.mem_iUnion.2 ⟨g,
      _root_.CFSG.FeitThompson.Prep05.mem_conjSet.2 ⟨y, hy, hyx⟩⟩

theorem conjClosure_eq_iUnion (S : Set G) :
    conjClosure S = ⋃ g : G, (fun x => g⁻¹ * x * g) '' S := (rfl)

theorem hallCoreIn_eq_hallCoreOf (N : Subgroup G) : hallCoreIn N = hallCoreOf N := (rfl)

theorem centralizerIn_zpowers_eq (X : Subgroup G) (a : G) :
    centralizerIn X (zpowers a) = X ⊓ centralizer ({a} : Set G) := by
  rw [_root_.CFSG.FeitThompson.Prep05.centralizerIn_eq,
    ← Subgroup.centralizer_closure ({a} : Set G), ← Subgroup.zpowers_eq_closure]

theorem dadeSupport_eq_conjClosure_leftCosetSet (H : G → Subgroup G) (a : G)
    (hR : H a ≤ Subgroup.centralizer ({a} : Set G)) :
    dadeSupport H a = conjClosure (leftCosetSet a (H a)) := by
  have hcoset : dadeCoset H a = leftCosetSet a (H a) := by
    rw [dadeCoset_eq_image]
    ext x
    simp only [Set.mem_image, SetLike.mem_coe,
      _root_.CFSG.FeitThompson.Prep05.mem_leftCosetSet]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (Subgroup.mem_centralizer_singleton_iff.1 (hR hu)).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, Subgroup.mem_centralizer_singleton_iff.1 (hR hr)⟩
  ext x
  rw [mem_dadeSupport_iff, mem_conjClosure_iff', hcoset]
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    exact ⟨c⁻¹, y, hy, by simpa using hc⟩
  · rintro ⟨g, y, hy, rfl⟩
    exact ⟨y, hy, isConj_iff.2 ⟨g⁻¹, by group⟩⟩

theorem dadeDeltaM_eq_biUnion [Finite G] (M : Subgroup G) :
    dadeDeltaM M =
      ⋃ x ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1},
        conjClosure (leftCosetSet x (signalizer x)) := by
  ext x
  rw [dadeDeltaM_eq, mem_totalDadeSupport_iff]
  simp only [Set.mem_iUnion, exists_prop]
  refine exists_congr fun a => and_congr_right fun ha => ?_
  have hT : dadeT M a = sigSignalizer a := dadeT_of_mem ha
  rw [dadeSupport_eq_conjClosure_leftCosetSet _ a (by
    rw [hT]; exact sigSignalizer_le_centralizer a), hT]
  rfl

theorem exists_pconfig_of_typeIII_IV_V [Finite G] {M : Subgroup G}
    (h : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ∃ E W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M E W₁ W₂ := by
  rcases h with h | h | h
  · obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
    exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
    exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨W₁, W₂, hc⟩ := h.exists_isWitnessedPConfiguration_bot
    exact ⟨⊥, W₁, W₂, hc⟩

theorem exists_pconfig_of_typeII [Finite G] {N : Subgroup G} (h : IsTypeII N) :
    ∃ E W₁ W₂ : Subgroup G, IsWitnessedPConfiguration N E W₁ W₂ := by
  obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
  exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩

theorem isTypeIII_IV_V_map_conj [Finite G] {M : Subgroup G}
    (h : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) (g : G) :
    IsTypeIII (M.map (MulAut.conj g).toMonoidHom) ∨
      IsTypeIV (M.map (MulAut.conj g).toMonoidHom) ∨
      IsTypeV (M.map (MulAut.conj g).toMonoidHom) := by
  rcases h with h | h | h
  · exact Or.inl (by simpa using h.conj g⁻¹)
  · exact Or.inr (Or.inl (by simpa using h.conj g⁻¹))
  · exact Or.inr (Or.inr (by simpa using h.conj g⁻¹))

end Aux

open scoped Classical in
theorem FPF_type_iii_v_type_ii_support_disjoint
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_kappa_positive_core_derived_support_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u}) :
    Statements.FPF_type_iii_v_type_ii_support_disjoint.{u} := by
  intro G _ _ hG M N hM hN hMtype hNtype B_N D_N hB hD
  have hFBG : _root_.CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hOSM : IsOddSimpleMinimal G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hMSO : _root_.CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hnotconj : ¬ IsConjugateSubgroup M N := by
    rintro ⟨g, rfl⟩
    have h5 := (h₁ G hFBG).1 _ hN
    have hII : _root_.CFSG.FeitThompson.localTypes
        (M.map (MulAut.conj g).toMonoidHom) 1 := hNtype
    rcases isTypeIII_IV_V_map_conj hMtype g with h | h | h
    · have : (1 : Fin 5) = 2 := h5.unique hII h
      simp at this
    · have : (1 : Fin 5) = 3 := h5.unique hII h
      simp at this
    · have : (1 : Fin 5) = 4 := h5.unique hII h
      simp at this
  obtain ⟨EM, W₁M, W₂M, hcM⟩ := exists_pconfig_of_typeIII_IV_V hMtype
  obtain ⟨EN, W₁N, W₂N, hcN⟩ := exists_pconfig_of_typeII hNtype
  have hkM := (h₂ G hOSM M EM W₁M W₂M hM hcM).1
  have hkN := (h₂ G hOSM N EN W₁N W₂N hN hcN).1
  have hdisj := h₃ G hMSO M N hM hN hnotconj hkM hkN
  rw [(h₄ G hMSO M hM).2 hMtype, (h₄ G hMSO N hN).1 hNtype] at hdisj
  have hBN : B_N = fixedSet (⁅N, N⁆ : Subgroup G) (hallCoreOf N) := by
    rw [hB]
    ext a
    simp only [Set.mem_ofPred_eq,
      _root_.CFSG.FeitThompson.Prep05.mem_fixedSet,
      centralizerIn_zpowers_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    tauto
  have hDN : D_N = conjClosure B_N := by rw [hD]; rfl
  have hmain : Disjoint (dadeDeltaM M) D_N := by
    rw [dadeDeltaM_eq_biUnion M, hDN, hBN]
    exact hdisj
  refine ⟨Set.disjoint_iff_inter_eq_empty.1 hmain, fun f h hf hh => ?_⟩
  refine cfInner_eq_zero_of_disjoint_support (Set.disjoint_of_subset ?_ ?_ hmain)
  · intro x hx
    by_contra hc
    exact hx (hf x hc)
  · intro x hx
    by_contra hc
    exact hx (hh x hc)

end CFSG.FeitThompson.Proofs
