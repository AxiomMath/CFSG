module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRModel
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3Comp
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelAGen)

variable {τ : Tag} {K : Type} [Field K]

section Classes

variable {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem class_eq_of_parent (S : Finset (Fin τ.rank)) {i₀ : Fin τ.rank} (hi₀ : i₀ ∈ S)
    (par : Fin τ.rank → Fin τ.rank) (d : Fin τ.rank → ℕ)
    (hmem : ∀ i ∈ S, (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ)
    (hpar : ∀ i ∈ S, i ≠ i₀ → par i ∈ S ∧ d (par i) < d i ∧
      iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single (par i) 1) ≠ 0) :
    ∀ i (hi : i ∈ S), (⟦⟨_, hmem i hi⟩⟧ : KernelComponent χ) = ⟦⟨_, hmem i₀ hi₀⟩⟧ := by
  intro i
  induction h : d i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    intro hi
    by_cases hii : i = i₀
    · subst hii
      rfl
    · obtain ⟨hpS, hpd, hform⟩ := hpar i hi hii
      rw [← h] at ih
      exact (mk_eq_of_iform_ne_zero (α := ⟨_, hmem i hi⟩) (β := ⟨_, hmem (par i) hpS⟩) hform).trans
        (ih (d (par i)) hpd (par i) rfl hpS)

theorem componentRoots_eq_kernelRoots {i₀ : Fin τ.rank}
    (h₀ : (Pi.single i₀ 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ)
    (hsupp : ∀ β ∈ kernelRoots χ, ∀ i, β i ≠ 0 → (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ)
    (hconn : ∀ i (hi : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ),
      (⟦⟨_, hi⟩⟧ : KernelComponent χ) = ⟦⟨_, h₀⟩⟧) :
    componentRoots χ ⟦⟨_, h₀⟩⟧ = kernelRoots χ := by
  ext β
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro hβ
    refine ⟨hβ, ?_⟩
    have hpos := iform_self_pos_of_isRoot hβ.1
    rw [F4Pilot.iform_eq_sum_mul_iform_single] at hpos
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    have hei := hsupp β hβ i (left_ne_zero_of_mul hi)
    exact (mk_eq_of_iform_ne_zero (α := ⟨β, hβ⟩) (β := ⟨_, hei⟩) (right_ne_zero_of_mul hi)).trans
      (hconn i hei)

theorem rootSpan_kernelRoots_eq {i : KernelComponent χ} (h : componentRoots χ i = kernelRoots χ) :
    rootSpan τ K (kernelRoots χ) = componentRootSpan K χ i := by
  rw [← h]
  rfl

theorem two_lt_ncard_of_roots {S : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ)
    {α δ : Fin τ.rank → ℤ} (hα : α ∈ S) (hα' : -α ∈ S) (hδ : δ ∈ S) (h1 : δ ≠ α) (h2 : δ ≠ -α) :
    2 < S.ncard := by
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset hS
  refine (Set.two_lt_ncard_iff hfin).2 ⟨α, -α, δ, hα, hα', hδ, ?_, h1.symm, h2.symm⟩
  intro h
  have h0 : α = 0 := by
    have : (2 : ℤ) • α = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel α
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  exact (hS α hα).ne_zero h0

end Classes

section Quasisimple

variable
  {M : Type*} [CommGroup M]

theorem open_isQuasisimple_hr {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

@[expose] def leviRootsOff (τ : Tag) (T : Finset (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {β | IsRoot τ β ∧ ∀ i ∈ T, β i = 0}

@[expose] def offChar (τ : Tag) (T : Finset (Fin τ.rank)) :
    Multiplicative (Fin τ.rank → ℤ) →* Multiplicative (T → ℤ) :=
  AddMonoidHom.toMultiplicative
    (Pi.addMonoidHom fun i : T => Pi.evalAddMonoidHom (fun _ => ℤ) (i : Fin τ.rank))

theorem kernelRoots_offChar (T : Finset (Fin τ.rank)) :
    kernelRoots (offChar τ T) = leviRootsOff τ T := by
  ext β
  constructor
  · rintro ⟨hβ, h⟩
    refine ⟨hβ, fun i hi => ?_⟩
    have := congrFun (congrArg Multiplicative.toAdd h) ⟨i, hi⟩
    exact this
  · rintro ⟨hβ, h⟩
    refine ⟨hβ, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    exact h i i.2

theorem perpRoots_eq_leviRootsOff : perpRoots τ = leviRootsOff τ {highNode τ} := by
  ext β
  simp [perpRoots, leviRootsOff]

theorem componentRoots_offChar_eq
    (T : Finset (Fin τ.rank)) {i₀ : Fin τ.rank} (hi₀ : i₀ ∉ T)
    (par : Fin τ.rank → Fin τ.rank) (d : Fin τ.rank → ℕ)
    (hpar : ∀ i, i ∉ T → i ≠ i₀ → par i ∉ T ∧ d (par i) < d i ∧
      iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single (par i) 1) ≠ 0) :
    ∃ h₀ : (Pi.single i₀ 1 : Fin τ.rank → ℤ) ∈ kernelRoots (offChar τ T),
      componentRoots (offChar τ T) ⟦⟨_, h₀⟩⟧ = kernelRoots (offChar τ T) := by
  have hmem : ∀ i, i ∉ T → (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots (offChar τ T) :=
    fun i hi => by
      rw [kernelRoots_offChar]
      exact ⟨IsRoot.basis i, fun j hj => Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi) 1⟩
  have hS : ∀ i ∈ (Finset.univ \ T), (Pi.single i 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (offChar τ T) := fun i hi => hmem i (Finset.mem_sdiff.1 hi).2
  have hi₀S : i₀ ∈ (Finset.univ \ T) := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi₀⟩
  have hconn := class_eq_of_parent (χ := offChar τ T) (Finset.univ \ T) hi₀S par d hS
    fun i hi hii => by
      obtain ⟨h1, h2, h3⟩ := hpar i (Finset.mem_sdiff.1 hi).2 hii
      exact ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h1⟩, h2, h3⟩
  refine ⟨hS i₀ hi₀S, componentRoots_eq_kernelRoots _ ?_ fun i hi => ?_⟩
  · intro β hβ i hβi
    rw [kernelRoots_offChar] at hβ
    exact hmem i fun hiT => hβi (hβ.2 i hiT)
  · have hiT : i ∉ T := fun hiT => by
      rw [kernelRoots_offChar] at hi
      have := hi.2 i hiT
      rw [Pi.single_eq_same] at this
      exact one_ne_zero this
    exact hconn i (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hiT⟩)

theorem isQuasisimple_rootSpan_leviRootsOff_of_odd (hK2 : ringChar K ≠ 2)
    (hsym : ∀ i, τ.symmetrizer i i = 1) (T : Finset (Fin τ.rank)) {i₀ i₁ : Fin τ.rank}
    (hi₀ : i₀ ∉ T) (hi₁ : i₁ ∉ T) (h01 : i₁ ≠ i₀) (par : Fin τ.rank → Fin τ.rank)
    (d : Fin τ.rank → ℕ)
    (hpar : ∀ i, i ∉ T → i ≠ i₀ → par i ∉ T ∧ d (par i) < d i ∧
      iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single (par i) 1) ≠ 0) :
    CFSG.Open.IsQuasisimple ↥(rootSpan τ K (leviRootsOff τ T)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨h₀, hcomp⟩ := componentRoots_offChar_eq T hi₀ par d hpar
  rw [← kernelRoots_offChar, rootSpan_kernelRoots_eq hcomp]
  have hroots : ∀ γ ∈ componentRoots (offChar τ T) ⟦⟨_, h₀⟩⟧, IsRoot τ γ := fun γ hγ => by
    rw [hcomp] at hγ; exact hγ.1
  have hmem : ∀ i, i ∉ T → (Pi.single i 1 : Fin τ.rank → ℤ) ∈
      componentRoots (offChar τ T) ⟦⟨_, h₀⟩⟧ := fun i hi => by
    rw [hcomp, kernelRoots_offChar]
    exact ⟨IsRoot.basis i, fun j hj => Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi) 1⟩
  have hneg : (-Pi.single i₀ 1 : Fin τ.rank → ℤ) ∈ componentRoots (offChar τ T) ⟦⟨_, h₀⟩⟧ := by
    rw [hcomp, kernelRoots_offChar]
    exact ⟨IsRoot.neg (IsRoot.basis i₀), fun j hj => by
      rw [Pi.neg_apply, Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi₀) 1, neg_zero]⟩
  have hncard : 2 < (componentRoots (offChar τ T) ⟦⟨_, h₀⟩⟧).ncard := by
    refine two_lt_ncard_of_roots hroots (hmem i₀ hi₀) hneg (hmem i₁ hi₁) ?_ ?_
    · intro h
      have := congrFun h i₁
      rw [Pi.single_eq_same, Pi.single_eq_of_ne h01] at this
      exact one_ne_zero this
    · intro h
      have := congrFun h i₁
      rw [Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_of_ne h01, neg_zero] at this
      exact one_ne_zero this
  exact open_isQuasisimple_hr
    (CFSG.HardMathSupport.Timmesfeld.LangTorus.isQuasisimple_componentRootSpan_of_perfect _
      (CFSG.HardMathSupport.Timmesfeld.LangTorus.isPerfect_componentRootSpan_of_odd h2 hsym _
        hncard))

theorem isQuasisimple_rootSpan_leviRootsOff_F4 (hK2 : ringChar K ≠ 2)
    (T : Finset (Fin Tag.F4.rank)) {i₀ i₁ : Fin Tag.F4.rank}
    (hi₀ : i₀ ∉ T) (hi₁ : i₁ ∉ T) (h01 : i₁ ≠ i₀) (par : Fin Tag.F4.rank → Fin Tag.F4.rank)
    (d : Fin Tag.F4.rank → ℕ)
    (hpar : ∀ i, i ∉ T → i ≠ i₀ → par i ∉ T ∧ d (par i) < d i ∧
      iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single (par i) 1) ≠ 0) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.F4 K (leviRootsOff Tag.F4 T)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨h₀, hcomp⟩ := componentRoots_offChar_eq T hi₀ par d hpar
  rw [← kernelRoots_offChar, rootSpan_kernelRoots_eq hcomp]
  have hmem : ∀ i, i ∉ T → (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      componentRoots (offChar Tag.F4 T) ⟦⟨_, h₀⟩⟧ := fun i hi => by
    rw [hcomp, kernelRoots_offChar]
    exact ⟨IsRoot.basis i, fun j hj => Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hi) 1⟩
  refine open_isQuasisimple_hr
    (CFSG.HardMathSupport.Timmesfeld.LangTorus.isQuasisimple_componentRootSpan_of_perfect _
      (CFSG.HardMathSupport.Timmesfeld.LangTorus.isPerfect_componentRootSpan_F4_of_two_ne_zero h2 _
        ⟨_, hmem i₀ hi₀, _, hmem i₁ hi₁, ?_, ?_⟩))
  · intro h
    have := congrFun h i₁
    rw [Pi.single_eq_same, Pi.single_eq_of_ne h01] at this
    exact one_ne_zero this
  · intro h
    have := congrFun h i₁
    rw [Pi.single_eq_same, Pi.neg_apply, Pi.single_eq_of_ne h01, neg_zero] at this
    exact one_ne_zero this

end Quasisimple

@[expose] def pairCoeffCheck (τ : Tag) (j k : Fin τ.rank) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m =>
    decide (|τ.rootCertificate.root m j + τ.rootCertificate.root m k| ≤ 4) &&
      (!decide (τ.rootCertificate.root m j + τ.rootCertificate.root m k = 0) ||
        (decide (τ.rootCertificate.root m j = 0) && decide (τ.rootCertificate.root m k = 0)))

theorem pairCoeffCheck_sound {j k : Fin τ.rank}
    (h : pairCoeffCheck τ j k = true) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    |γ j + γ k| ≤ 4 ∧ (γ j + γ k = 0 → γ j = 0 ∧ γ k = 0) := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  simp only [pairCoeffCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨h1, h2⟩ := h m hm
  refine ⟨h1, fun h0 => ?_⟩
  rcases h2 with h2 | h2
  · exact absurd h0 h2
  · exact h2

theorem coeff_eq_zero_of_mem_rootCharKernel_pair {j k : Fin τ.rank}
    (h : pairCoeffCheck τ j k = true) {p : ℕ} (hp5 : 5 ≤ p) {ζ : Kˣ} (hζ : orderOf ζ = p)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ rootCharKernel (Pi.mulSingle j ζ * Pi.mulSingle k ζ)) :
    γ j = 0 ∧ γ k = 0 := by
  obtain ⟨hr, hc⟩ := hγ
  rw [rootChar_mul, rootChar_mulSingle, rootChar_mulSingle, ← zpow_add] at hc
  obtain ⟨h4, h0⟩ := pairCoeffCheck_sound h hr
  apply h0
  have hdvd : (p : ℤ) ∣ γ j + γ k := by
    rw [← hζ]
    exact orderOf_dvd_iff_zpow_eq_one.2 hc
  obtain ⟨m, hm⟩ := hdvd
  rw [hm] at h4 ⊢
  rcases abs_le.1 h4 with ⟨h4a, h4b⟩
  have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  rcases lt_trichotomy m 0 with hneg | rfl | hpos
  · nlinarith
  · rw [mul_zero]
  · nlinarith

theorem rootCharKernel_pair_eq {j k : Fin τ.rank}
    (h : pairCoeffCheck τ j k = true) {p : ℕ} (hp5 : 5 ≤ p) {ζ : Kˣ} (hζ : orderOf ζ = p) :
    rootCharKernel (Pi.mulSingle j ζ * Pi.mulSingle k ζ) = leviRootsOff τ {j, k} := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨h0, h1⟩ := coeff_eq_zero_of_mem_rootCharKernel_pair h hp5 hζ hγ
    refine ⟨hγ.1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h0
    · rw [Finset.mem_singleton.1 hi]
      exact h1
  · rintro ⟨hγ, h0⟩
    refine ⟨hγ, ?_⟩
    rw [rootChar_mul, rootChar_mulSingle, rootChar_mulSingle, h0 j (by simp), h0 k (by simp),
      zpow_zero, mul_one]

structure HRRootData (τ : Tag) : Prop where
  abs_le : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2
  eq_highRoot : ∀ γ, IsRoot τ γ → γ (highNode τ) = 2 → γ = highRoot τ
  highRoot_highNode : highRoot τ (highNode τ) = 2
  iform_eq_zero_iff : ∀ v, iform (highRoot τ) v = 0 ↔ v (highNode τ) = 0
  exists_nbr : ∀ i, i ≠ highNode τ → ∃ i', i' ≠ highNode τ ∧ i' ≠ i ∧
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i' 1) ≠ 0

theorem hrRootData_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    HRRootData τ where
  abs_le _ hγ := abs_coeff_highNode_le_two hτ hγ
  eq_highRoot _ hγ h := eq_highRoot_of_coeff_highNode_eq_two hτ hγ h
  highRoot_highNode := highRoot_highNode hτ
  iform_eq_zero_iff v := by rw [iform_highRoot hτ]
  exists_nbr := by rcases hτ with rfl | rfl | rfl <;> decide

theorem hrRootData_F4 : HRRootData .F4 where
  abs_le _ hγ := F4Pilot.abs_coeff_zero_le_two hγ
  eq_highRoot _ hγ h := F4Pilot.eq_rootR_of_coeff_zero_eq_two hγ h
  highRoot_highNode := rfl
  iform_eq_zero_iff v := by
    change iform F4Pilot.rootR v = 0 ↔ v 0 = 0
    rw [F4Pilot.iform_rootR]
    omega
  exists_nbr := by decide

section Types

instance neZero_rank_F4 : NeZero Tag.F4.rank := ⟨by decide⟩

instance neZero_rank_E6 : NeZero Tag.E6.rank := ⟨by decide⟩

instance neZero_rank_E7 : NeZero Tag.E7.rank := ⟨by decide⟩

instance neZero_rank_E8 : NeZero Tag.E8.rank := ⟨by decide⟩

private def parF4 : Fin Tag.F4.rank → Fin Tag.F4.rank := ![2, 2, 2, 2]
private def depF4 : Fin Tag.F4.rank → ℕ := ![0, 1, 0, 1]
private def parE6 : Fin Tag.E6.rank → Fin Tag.E6.rank := ![2, 1, 3, 3, 3, 4]
private def depE6 : Fin Tag.E6.rank → ℕ := ![2, 0, 1, 0, 1, 2]
private def parE7 : Fin Tag.E7.rank → Fin Tag.E7.rank := ![0, 3, 3, 3, 3, 4, 5]
private def depE7 : Fin Tag.E7.rank → ℕ := ![0, 1, 1, 0, 1, 2, 3]
private def parE8 : Fin Tag.E8.rank → Fin Tag.E8.rank := ![2, 3, 3, 3, 3, 4, 5, 7]
private def depE8 : Fin Tag.E8.rank → ℕ := ![2, 1, 1, 0, 1, 2, 3, 0]

theorem pairCoeffCheck_E6 : pairCoeffCheck .E6 (highNode .E6) (0 : Fin Tag.E6.rank) = true := by decide +kernel

theorem isQuasisimple_perpLevi_F4 (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.F4 K (perpRoots Tag.F4)) := by
  rw [perpRoots_eq_leviRootsOff]
  exact isQuasisimple_rootSpan_leviRootsOff_F4 hK2 {highNode .F4} (i₀ := (2 : Fin Tag.F4.rank))
    (i₁ := (1 : Fin Tag.F4.rank)) (by decide) (by decide) (by decide) parF4 depF4 (by decide)

theorem isQuasisimple_perpLevi_E6 (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.E6 K (perpRoots Tag.E6)) := by
  rw [perpRoots_eq_leviRootsOff]
  exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) {highNode .E6}
    (i₀ := (3 : Fin Tag.E6.rank)) (i₁ := (2 : Fin Tag.E6.rank)) (by decide) (by decide) (by decide)
    parE6 depE6 (by decide)

theorem isQuasisimple_perpLevi_E7 (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.E7 K (perpRoots Tag.E7)) := by
  rw [perpRoots_eq_leviRootsOff]
  exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) {highNode .E7}
    (i₀ := (3 : Fin Tag.E7.rank)) (i₁ := (2 : Fin Tag.E7.rank)) (by decide) (by decide) (by decide)
    parE7 depE7 (by decide)

theorem isQuasisimple_perpLevi_E8 (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan Tag.E8 K (perpRoots Tag.E8)) := by
  rw [perpRoots_eq_leviRootsOff]
  exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) {highNode .E8}
    (i₀ := (3 : Fin Tag.E8.rank)) (i₁ := (2 : Fin Tag.E8.rank)) (by decide) (by decide) (by decide)
    parE8 depE8 (by decide)

theorem modelAGen_E6 [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ζ : Kˣ} (hζ : orderOf ζ = p) : ModelAGen p Tag.E6.rank ↥(adjointGroup .E6 K) := by
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hdet : ¬ (p : ℤ) ∣ Tag.E6.cartan.det := by
    rw [det_cartan_E6]
    intro h
    have h3 : p ∣ 3 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    omega
  refine modelAGen_hr (k' := (0 : Fin Tag.E6.rank)) (i₂ := (3 : Fin Tag.E6.rank)) hK2 hp (by omega) hdet hζ
    (fun γ hγ => abs_coeff_highNode_le_two hτ hγ) (sum_highRoot_mul_cartan hτ)
    (isQuasisimple_perpLevi_E6 hK2) (by decide) (by decide) (by decide)
    (fun γ hγ => coeff_eq_zero_of_mem_rootCharKernel_pair pairCoeffCheck_E6 hp5 hζ hγ) ?_
  rw [rootCharKernel_pair_eq pairCoeffCheck_E6 hp5 hζ]
  exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) _ (i₀ := (3 : Fin Tag.E6.rank))
    (i₁ := (2 : Fin Tag.E6.rank)) (by decide) (by decide) (by decide) parE6 depE6 (by decide)

end Types

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
