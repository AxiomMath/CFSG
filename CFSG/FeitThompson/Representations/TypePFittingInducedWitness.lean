module

import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
public import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence
public import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription
public import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
public import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
public import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
public import CFSG.FeitThompson.Representations.FixedWeightStabilizerIsCentralizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open _root_.CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G]

theorem extendZero_coe {X : Subgroup G} (f : ↥X → ℂ) (x : ↥X) : extendZero f ((x : G)) = f x :=
  X.subtype_injective.extend_apply f 0 x

theorem indBetween_eq_indClassFun_extendZero [Finite G] (X Y : Subgroup G) [Fintype ↥Y]
    (f : ↥X → ℂ) :
    indBetween X Y f = indClassFun (X.subgroupOf Y) (fun z => extendZero f ((z : ↥Y) : G)) := by
  unfold indBetween
  congr 1
  exact Subsingleton.elim _ _

theorem indBetween_apply_one [Finite G] (X Y : Subgroup G) (f : ↥X → ℂ) :
    indBetween X Y f 1 = (X.relIndex Y : ℂ) * f 1 := by
  have : Fintype ↥Y := Fintype.ofFinite _
  rw [indBetween_eq_indClassFun_extendZero, indClassFun_apply_one]
  simp only [OneMemClass.coe_one]
  rw [show extendZero f (1 : G) = f 1 from extendZero_coe f 1]
  rfl

theorem indBetween_eq_indClassFun_coe [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y) [Fintype ↥Y]
    (f : ↥X → ℂ) :
    indBetween X Y f
      = indClassFun (X.subgroupOf Y) (fun z => f ⟨((z : ↥Y) : G), mem_subgroupOf.1 z.2⟩) := by
  rw [indBetween_eq_indClassFun_extendZero]
  congr 1
  funext z
  exact extendZero_coe f ⟨((z : ↥Y) : G), mem_subgroupOf.1 z.2⟩

theorem indBetween_indBetween [Finite G] {X Y Z : Subgroup G} (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    (f : ↥X → ℂ) : indBetween Y Z (indBetween X Y f) = indBetween X Z f := by
  classical
  have : Fintype ↥Y := Fintype.ofFinite _
  have : Fintype ↥Z := Fintype.ofFinite _
  have hXZ : X ≤ Z := hXY.trans hYZ
  have hsub : X.subgroupOf Z ≤ Y.subgroupOf Z := Subgroup.comap_mono hXY
  have key : (indBetween X Y f) ∘ (Subgroup.subgroupOfEquivOfLe hYZ)
      = indClassFun ((X.subgroupOf Z).subgroupOf (Y.subgroupOf Z))
        ((fun w : ↥(X.subgroupOf Z) => f ⟨((w : ↥Z) : G), mem_subgroupOf.1 w.2⟩)
          ∘ (Subgroup.subgroupOfEquivOfLe hsub)) := by
    rw [indBetween_eq_indClassFun_coe hXY]
    refine indClassFun_comp_mulEquiv (Subgroup.subgroupOfEquivOfLe hYZ) ?_ ?_
    · intro z
      exact ⟨fun hz => mem_subgroupOf.2 (mem_subgroupOf.1 (mem_subgroupOf.1 hz)),
        fun hz => mem_subgroupOf.2 (mem_subgroupOf.2 (mem_subgroupOf.1 hz))⟩
    · intro x y hxy
      change f _ = (f ∘ _) _
      simp only [Function.comp_apply]
      refine congrArg f (Subtype.ext ?_)
      show ((y : ↥Y) : G) = (((x : ↥(Y.subgroupOf Z)) : ↥Z) : G)
      rw [hxy]; rfl
  rw [indBetween_eq_indClassFun_coe hYZ, indBetween_eq_indClassFun_coe hXZ]
  have hfun : (fun z : ↥(Y.subgroupOf Z) =>
        indBetween X Y f ⟨((z : ↥Z) : G), mem_subgroupOf.1 z.2⟩)
      = (indBetween X Y f) ∘ (Subgroup.subgroupOfEquivOfLe hYZ) := by
    funext z; rfl
  rw [hfun, key]
  exact AbelianInertiaBlock.indClassFun_indClassFun (Y.subgroupOf Z) hsub _

variable [Finite G]

theorem relIndex_fittingOf_eq {M U W₁ : Subgroup G}
    (hsemi₁ : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁))
    (hsemi₂ : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hFdir : IsInternalDirectProduct (fittingOf M) (hallCoreOf M)
      (centralizerIn U (hallCoreOf M))) :
    (fittingOf M).relIndex M
      = Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U := by
  have hC : centralizerIn U (hallCoreOf M) ≤ U := centralizerIn_le _ _
  have hMcard : Nat.card ↥M = Nat.card ↥(hallCoreOf M) * (Nat.card ↥U * Nat.card ↥W₁) := by
    rw [hsemi₁.natCard_eq_mul, hsemi₂.natCard_eq_mul]
  have hFcard : Nat.card ↥(fittingOf M)
      = Nat.card ↥(hallCoreOf M) * Nat.card ↥(centralizerIn U (hallCoreOf M)) :=
    hFdir.card_eq_mul
  have key : Nat.card ↥(fittingOf M) * (fittingOf M).relIndex M
      = Nat.card ↥(fittingOf M) *
        (Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U) := by
    rw [natCard_mul_relIndex (fittingOf_le M), hMcard, hFcard,
      ← natCard_mul_relIndex hC]
    ring
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key

theorem le_normalizer_fittingOf (M : Subgroup G) :
    M ≤ normalizer ((fittingOf M : Subgroup G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (fittingOf_le M)).1 (by
    rw [subgroupOf_fittingOf M]; infer_instance)

theorem mem_inertiaGroup_subgroupOf_iff' {X Y : Subgroup G} (hXY : X ≤ Y)
    [(X.subgroupOf Y).Normal] {Λ : ↥X →* ℂˣ} {y : ↥Y} :
    (y ∈ inertiaGroup (X.subgroupOf Y)
        (fun z => (Λ ((subgroupOfEquivOfLe hXY) z) : ℂ))) ↔ (y : G) ∈ charInertia X Λ := by
  have hYN : Y ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXY).1 ‹(X.subgroupOf Y).Normal›
  rw [mem_inertiaGroup_iff_forall_conj, mem_charInertia]
  constructor
  · intro h
    refine ⟨hYN y.2, fun m n hmn => ?_⟩
    set z : ↥(X.subgroupOf Y) := ⟨⟨(n : G), hXY n.2⟩, Subgroup.mem_subgroupOf.2 n.2⟩ with hz
    have hval := h z
    have hcoe : (subgroupOfEquivOfLe hXY) ((MulAut.conjNormal y⁻¹) z) = m := by
      refine Subtype.ext ?_
      change ((((MulAut.conjNormal y⁻¹) z : ↥(X.subgroupOf Y)) : ↥Y) : G) = (m : G)
      rw [MulAut.conjNormal_apply]
      push_cast
      rw [hmn]
      simp [hz]
    have hcoe2 : (subgroupOfEquivOfLe hXY) z = n := Subtype.ext rfl
    rw [hcoe, hcoe2] at hval
    exact Units.ext hval
  · rintro ⟨-, h⟩ z
    refine congrArg Units.val (h _ _ ?_)
    change ((((MulAut.conjNormal y⁻¹) z : ↥(X.subgroupOf Y)) : ↥Y) : G)
      = (y : G)⁻¹ * (((z : ↥Y) : G)) * (y : G)
    rw [MulAut.conjNormal_apply]
    push_cast
    simp

theorem mem_charInertia_comp_inclusion {F A : Subgroup G} (hAF : A ≤ F) (Ψ : ↥F →* ℂˣ)
    {m : G} (hmA : m ∈ normalizer (A : Set G)) (hm : m ∈ charInertia F Ψ) :
    m ∈ charInertia A (Ψ.comp (Subgroup.inclusion hAF)) := by
  refine mem_charInertia_of_forall hmA ?_
  intro n hn
  obtain ⟨-, h⟩ := mem_charInertia.1 hm
  exact h ⟨m⁻¹ * (n : G) * m, hAF hn⟩ ⟨(n : G), hAF n.2⟩ rfl

theorem eq_one_of_mem_charInertia_of_fixedPointFree {C W : Subgroup G} [IsMulCommutative ↥C]
    [Finite ↥C] (hWC : W ≤ normalizer (C : Set G))
    (hfpf : ∀ w ∈ W, w ≠ 1 → centralizerIn C (zpowers w) = ⊥)
    {ν : ↥C →* ℂˣ} (hν : ν ≠ 1) {w : G} (hw : w ∈ W) (hmem : w ∈ charInertia C ν) : w = 1 := by
  by_contra hw1
  refine hν ?_
  have hwC := hWC hw
  have hcoe : ∀ c : ↥C, ((FreeCore.conjAut C hwC c : ↥C) : G) = w * (c : G) * w⁻¹ :=
    fun c => FreeCore.coe_conjAut_apply hwC c
  have hefpf : MonoidHom.FixedPointFree (FreeCore.conjAut C hwC : ↥C → ↥C) := by
    intro c hc
    have h1 : w * (c : G) * w⁻¹ = (c : G) := by rw [← hcoe c]; exact congrArg _ hc
    have hcomm : Commute w (c : G) := by
      unfold Commute SemiconjBy
      calc w * (c : G) = (w * (c : G) * w⁻¹) * w := by group
      _ = (c : G) * w := by rw [h1]
    have hmemc : (c : G) ∈ centralizerIn C (zpowers w) := by
      refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (hcomm.zpow_left n).eq
    rw [hfpf w hw hw1] at hmemc
    exact Subtype.ext (by simpa using hmemc)
  refine eq_one_of_comp_aut_eq_of_fixedPointFree hefpf (MonoidHom.ext fun c => ?_)
  obtain ⟨-, h⟩ := mem_charInertia.1 hmem
  exact (h c (FreeCore.conjAut C hwC c) (by rw [hcoe]; group)).symm

theorem le_normalizer_of_isMulCommutative {A K : Subgroup G} [IsMulCommutative ↥A] (hKA : K ≤ A) :
    A ≤ normalizer (K : Set G) :=
  ((le_centralizer_iff_isMulCommutative.2 ‹IsMulCommutative ↥A›).trans
    (Subgroup.centralizer_le (show (K : Set G) ⊆ (A : Set G) from hKA))).trans
    (Subgroup.centralizer_le_normalizer _)

theorem charInertia_inf_le {M U W₁ : Subgroup G} [IsMulCommutative ↥U]
    [IsMulCommutative ↥(hallCoreOf M)] [IsMulCommutative ↥(fittingOf M)]
    (hsemi₁ : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁))
    (hsemi₂ : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hFdir : IsInternalDirectProduct (fittingOf M) (hallCoreOf M)
      (centralizerIn U (hallCoreOf M)))
    (hfpf : IsFixedPointFreeOn U W₁)
    (hmin : ∀ N : Subgroup G, N ≤ hallCoreOf M → M ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = hallCoreOf M)
    (hnormC : M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G))
    (Ψ : ↥(fittingOf M) →* ℂˣ)
    (hμ : (Ψ.comp (Subgroup.inclusion hFdir.left_le)) ≠ 1)
    (hμinv : ∀ w ∈ W₁, ∀ (n : ↥(hallCoreOf M)) (hn : w⁻¹ * (n : G) * w ∈ hallCoreOf M),
      (Ψ.comp (Subgroup.inclusion hFdir.left_le)) ⟨w⁻¹ * (n : G) * w, hn⟩
        = (Ψ.comp (Subgroup.inclusion hFdir.left_le)) n)
    (hν : (Ψ.comp (Subgroup.inclusion hFdir.right_le)) ≠ 1) :
    charInertia (fittingOf M) Ψ ⊓ M ≤ fittingOf M := by
  set H := hallCoreOf M with hH
  set C := centralizerIn U (hallCoreOf M) with hC
  have hCU : C ≤ U := centralizerIn_le _ _
  have hCcomm : IsMulCommutative ↥C := isMulCommutative_of_le hCU
  have hUM : U ⊔ W₁ ≤ M := hsemi₁.right_le
  have hW₁M : W₁ ≤ M := (le_sup_right : W₁ ≤ U ⊔ W₁).trans hUM
  have hUM' : U ≤ M := (le_sup_left : U ≤ U ⊔ W₁).trans hUM
  have hHnorm : M ≤ normalizer (H : Set G) := hsemi₁.le_normalizer
  intro m hm
  obtain ⟨hmI, hmM⟩ := Subgroup.mem_inf.1 hm
  obtain ⟨h, hh, y, hy, rfl⟩ := hsemi₁.exists_mul hmM
  obtain ⟨uu, huu, w, hw, rfl⟩ := hsemi₂.exists_mul hy
  have hhI : h ∈ charInertia (fittingOf M) Ψ :=
    (le_centralizer_iff_isMulCommutative.2 ‹IsMulCommutative ↥(fittingOf M)›).trans
      centralizer_le_charInertia (hFdir.left_le hh)
  have hyI : uu * w ∈ charInertia (fittingOf M) Ψ := by
    have heq : uu * w = h⁻¹ * (h * (uu * w)) := by group
    rw [heq]
    exact mul_mem (inv_mem hhI) hmI
  have hyM : uu * w ∈ M := hUM (Subgroup.mul_mem_sup huu hw)
  have hyC : uu * w ∈ charInertia C (Ψ.comp (Subgroup.inclusion hFdir.right_le)) :=
    mem_charInertia_comp_inclusion _ Ψ (hnormC hyM) hyI
  have huC : uu ∈ charInertia C (Ψ.comp (Subgroup.inclusion hFdir.right_le)) :=
    centralizer_le_charInertia
      (Subgroup.centralizer_le (show (C : Set G) ⊆ (U : Set G) from hCU)
        ((le_centralizer_iff_isMulCommutative.2 ‹IsMulCommutative ↥U›) huu))
  have hwC : w ∈ charInertia C (Ψ.comp (Subgroup.inclusion hFdir.right_le)) := by
    have heq : w = uu⁻¹ * (uu * w) := by group
    rw [heq]
    exact mul_mem (inv_mem huC) hyC
  have hw1 : w = 1 := by
    refine eq_one_of_mem_charInertia_of_fixedPointFree (C := C) (W := W₁)
      (fun x hx => hnormC (hW₁M hx)) (fun x hx hx1 => ?_) hν hw hwC
    have hbot := hfpf x hx hx1
    have hle : centralizerIn C (zpowers x) ≤ centralizerIn U (zpowers x) :=
      inf_le_inf_right _ hCU
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  subst hw1
  rw [mul_one] at hyI
  have huH : uu ∈ charInertia H (Ψ.comp (Subgroup.inclusion hFdir.left_le)) :=
    mem_charInertia_comp_inclusion _ Ψ (hHnorm (hUM' huu)) hyI
  have hstab : U ⊓ charInertia H (Ψ.comp (Subgroup.inclusion hFdir.left_le))
      = U ⊓ centralizer (H : Set G) := by
    refine inf_charInertia_eq_inf_centralizer (A := U ⊔ W₁) (Q := W₁) hμ
      (hUM.trans hHnorm) hsemi₂.coe_eq_mul hsemi₂.normal_subgroupOf ?_ hμinv
    intro K hKH hnormK
    refine hmin K hKH ?_
    rw [← hsemi₁.sup_eq]
    exact sup_le (le_normalizer_of_isMulCommutative hKH) hnormK
  have huCmem : uu ∈ C := by
    rw [hC, centralizerIn_eq, ← hstab]
    exact Subgroup.mem_inf.2 ⟨huu, huH⟩
  have h1 : h ∈ fittingOf M := hFdir.left_le hh
  have h2 : uu ∈ fittingOf M := hFdir.right_le huCmem
  simpa [mul_one] using Subgroup.mul_mem _ h1 h2

theorem indBetween_mem_Irr_of_charInertia_le {M F X : Subgroup G} (hFX : F ≤ X) (hXM : X ≤ M)
    (hFM : M ≤ normalizer (F : Set G)) (Λ : ↥F →* ℂˣ)
    (hI : charInertia F Λ ⊓ M ≤ F) :
    indBetween F X (fun x => (Λ x : ℂ)) ∈ Irr ↥X := by
  classical
  have : Fintype ↥X := Fintype.ofFinite _
  have hFXnorm : (F.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hFX).2 (hXM.trans hFM)
  set θ : ↥(F.subgroupOf X) → ℂ := fun z => (Λ ((subgroupOfEquivOfLe hFX) z) : ℂ) with hθ
  have hθIrr : θ ∈ Irr ↥(F.subgroupOf X) :=
    SolvableNormalLayer.coe_monoidHom_units_mem_Irr
      (Λ.comp (subgroupOfEquivOfLe hFX).toMonoidHom)
  have hind : indBetween F X (fun x => (Λ x : ℂ)) = indClassFun (F.subgroupOf X) θ := by
    rw [indBetween_eq_indClassFun_extendZero]
    congr 1
    funext z
    have hmem : ((z : ↥X) : G) ∈ F := mem_subgroupOf.1 z.2
    rw [extendZero_coe (fun x : ↥F => (Λ x : ℂ)) ⟨((z : ↥X) : G), hmem⟩]
    rfl
  rw [hind]
  refine (FreeCore.mem_Irr_indClassFun_iff _ hθIrr).2 ?_
  refine le_antisymm ?_ (le_inertiaGroup _ (Irr_subset_classFun hθIrr))
  intro y hy
  rw [hθ, mem_inertiaGroup_subgroupOf_iff' hFX] at hy
  exact mem_subgroupOf.2 (hI (Subgroup.mem_inf.2 ⟨hy, hXM y.2⟩))

theorem not_kerContains_of_restrict_ne_one {M F H X : Subgroup G} (hFX : F ≤ X) (hXM : X ≤ M)
    (hHF : H ≤ F) (hFM : M ≤ normalizer (F : Set G)) (hHM : M ≤ normalizer (H : Set G))
    (Λ : ↥F →* ℂˣ) (hres : Λ.comp (Subgroup.inclusion hHF) ≠ 1) :
    ¬ kerContains H X (indBetween F X (fun x => (Λ x : ℂ))) := by
  classical
  have : Fintype ↥X := Fintype.ofFinite _
  have hFXnorm : (F.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hFX).2 (hXM.trans hFM)
  have hHXnorm : (H.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hHF.trans hFX)).2 (hXM.trans hHM)
  set θ : ↥(F.subgroupOf X) → ℂ := fun z => (Λ ((subgroupOfEquivOfLe hFX) z) : ℂ) with hθ
  have hθIrr : θ ∈ Irr ↥(F.subgroupOf X) :=
    SolvableNormalLayer.coe_monoidHom_units_mem_Irr
      (Λ.comp (subgroupOfEquivOfLe hFX).toMonoidHom)
  have hind : indBetween F X (fun x => (Λ x : ℂ)) = indClassFun (F.subgroupOf X) θ := by
    rw [indBetween_eq_indClassFun_extendZero]
    congr 1
    funext z
    have hmem : ((z : ↥X) : G) ∈ F := mem_subgroupOf.1 z.2
    rw [extendZero_coe (fun x : ↥F => (Λ x : ℂ)) ⟨((z : ↥X) : G), hmem⟩]
    rfl
  intro hker
  have hsub : ((H.subgroupOf X : Subgroup ↥X) : Set ↥X)
      ⊆ charValueKernel (indClassFun (F.subgroupOf X) θ) := by
    intro x hx
    rw [mem_charValueKernel, ← hind]
    exact hker x (mem_subgroupOf.1 hx)
  have hsubF : (H.subgroupOf X) ≤ (F.subgroupOf X) := Subgroup.comap_mono hHF
  rw [subset_charValueKernel_indClassFun_iff hsubF hθIrr] at hsub
  refine hres (MonoidHom.ext fun n => Units.ext ?_)
  have hmemX : ((n : G)) ∈ X := hFX (hHF n.2)
  set z : ↥((H.subgroupOf X).subgroupOf (F.subgroupOf X)) :=
    ⟨⟨⟨(n : G), hmemX⟩, mem_subgroupOf.2 (hHF n.2)⟩, mem_subgroupOf.2 (mem_subgroupOf.2 n.2)⟩
    with hz
  have hval := hsub z.2
  rw [mem_charValueKernel] at hval
  have h1 : θ (z : ↥(F.subgroupOf X)) = (Λ ((Subgroup.inclusion hHF) n) : ℂ) := by
    rw [hθ]
    exact congrArg (fun y => ((Λ y : ℂˣ) : ℂ)) (Subtype.ext rfl)
  have h2 : θ 1 = 1 := by rw [hθ]; simp
  rw [h1, h2] at hval
  simpa using hval

theorem exists_monoidHom_restrict_eq {X A B : Subgroup G} (h : IsInternalDirectProduct X A B)
    (μ : ↥A →* ℂˣ) (ν : ↥B →* ℂˣ) :
    ∃ Ψ : ↥X →* ℂˣ, Ψ.comp (Subgroup.inclusion h.left_le) = μ ∧
      Ψ.comp (Subgroup.inclusion h.right_le) = ν := by
  refine ⟨((μ.comp (MonoidHom.fst ↥A ↥B)) * (ν.comp (MonoidHom.snd ↥A ↥B))).comp
    h.mulEquivProd.symm.toMonoidHom, MonoidHom.ext fun a => ?_, MonoidHom.ext fun b => ?_⟩
  · have hx : h.mulEquivProd.symm (Subgroup.inclusion h.left_le a) = (a, 1) := by
      rw [MulEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [h.coe_mulEquivProd_apply]
      simp [Subgroup.coe_inclusion]
    simp [hx]
  · have hx : h.mulEquivProd.symm (Subgroup.inclusion h.right_le b) = (1, b) := by
      rw [MulEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [h.coe_mulEquivProd_apply]
      simp [Subgroup.coe_inclusion]
    simp [hx]

theorem exists_monoidHom_hallCoreOf {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hq : Nat.Prime (Nat.card ↥W₁))
    (hab : IsMulCommutative ↥(hallCoreOf M)) :
    ∃ μ : ↥(hallCoreOf M) →* ℂˣ, μ ≠ 1 ∧
      ∀ w ∈ W₁, ∀ (n : ↥(hallCoreOf M)) (hn : w⁻¹ * (n : G) * w ∈ hallCoreOf M),
        μ ⟨w⁻¹ * (n : G) * w, hn⟩ = μ n := by
  have hab' : IsMulCommutative ↥(Subgroup.map M.subtype (hallCore ↥M)) := by
    rw [← hallCoreOf_eq]; exact hab
  obtain ⟨lam, hlamIrr, hlam1, hlaminv⟩ := exists_invariant_mem_Irr_hallCore_ne_one hc hq
  have hlamdeg : lam 1 = 1 := Irr.apply_one_eq_one_of_isMulCommutative hlamIrr
  obtain ⟨μ, hμ⟩ := exists_monoidHom_units_eq_of_mem_Irr_of_apply_one_eq_one hlamIrr hlamdeg
  refine ⟨μ, ?_, ?_⟩
  · intro h
    refine hlam1 (funext fun x => ?_)
    have hx : ((μ x : ℂˣ) : ℂ) = lam x := congrFun hμ x
    rw [show μ = 1 from h] at hx
    simpa using hx.symm
  · intro w hw n hn
    refine Units.ext ?_
    have h := congrFun (hlaminv ⟨w, hw⟩) n
    rw [charConj_apply _ ⟨w, hw⟩ lam (x := n) (y := ⟨w⁻¹ * (n : G) * w, hn⟩) (by simp)] at h
    calc ((μ ⟨w⁻¹ * (n : G) * w, hn⟩ : ℂˣ) : ℂ) = lam ⟨w⁻¹ * (n : G) * w, hn⟩ := congrFun hμ _
    _ = lam n := h
    _ = ((μ n : ℂˣ) : ℂ) := (congrFun hμ n).symm

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open _root_.CFSG.FeitThompson.Prep05

universe u

theorem relIndex_fittingOf_eq_of_elementary_core_structure
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (fittingOf M).relIndex M
      = Nat.card ↥W₁ * (centralizerIn U (hallCoreOf M)).relIndex U := by
  obtain ⟨-, -, -, -, -, -, -, -, hsemi₁, hsemi₂, -, -, -, -, -, -, -, -, -, -, hFdir, -, -, -⟩ :=
    h₁ G hG M U W₁ W₂ hM hc (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  exact relIndex_fittingOf_eq hsemi₁ hsemi₂ hFdir

private theorem FNI_type_p_fitting_induced_witness_aux
    (_h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_fitting_induced_witness.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc q uu hqdef huudef hCne
  obtain ⟨-, -, hqp, -, -, -, -, hUab, hsemi₁, hsemi₂, -, hfpf,
    -, -, -, -, -, hmin, -, hnormC, hFdir, hFab, -, -⟩ :=
    _h₁ G hG M U W₁ W₂ hM hc (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  subst hqdef huudef
  have hHab : IsMulCommutative ↥(hallCoreOf M) := isMulCommutative_of_le hFdir.left_le
  have hFK : fittingOf M ≤ (⁅M, M⁆ : Subgroup G) := by
    rw [fittingOf_eq]; exact hc.fittingRaw_le_commutator
  have hKM : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  have hFM : M ≤ normalizer ((fittingOf M : Subgroup G) : Set G) := le_normalizer_fittingOf M
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) := hsemi₁.le_normalizer
  have hHF : hallCoreOf M ≤ fittingOf M := hFdir.left_le
  obtain ⟨μ, hμ1, hμinv⟩ := exists_monoidHom_hallCoreOf hc hqp hHab
  have hCnt : Nontrivial ↥(centralizerIn U (hallCoreOf M)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hCne
  have hCab : IsMulCommutative ↥(centralizerIn U (hallCoreOf M)) :=
    isMulCommutative_of_le hFdir.right_le
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(centralizerIn U (hallCoreOf M)))
  obtain ⟨ν, hνne⟩ := exists_monoidHom_apply_ne_one_of_isMulCommutative hc1
  have hν1 : ν ≠ 1 := fun h => hνne (by rw [h]; simp)
  obtain ⟨Ψ, hΨμ, hΨν⟩ := exists_monoidHom_restrict_eq hFdir μ ν
  set ψ : ↥(fittingOf M) → ℂ := fun x => (Ψ x : ℂ) with hψdef
  have hψIrr : ψ ∈ Irr ↥(fittingOf M) := SolvableNormalLayer.coe_monoidHom_units_mem_Irr Ψ
  have hψ1 : ψ 1 = 1 := by rw [hψdef]; simp
  have hI : charInertia (fittingOf M) Ψ ⊓ M ≤ fittingOf M := by
    refine charInertia_inf_le hsemi₁ hsemi₂ hFdir hfpf hmin hnormC Ψ ?_ ?_ ?_
    · rw [hΨμ]; exact hμ1
    · rw [hΨμ]; exact hμinv
    · rw [hΨν]; exact hν1
  have hlam :
      indBetween (⁅M, M⁆ : Subgroup G) M (indBetween (fittingOf M) (⁅M, M⁆ : Subgroup G) ψ)
        = indBetween (fittingOf M) M ψ := indBetween_indBetween hFK hKM ψ
  refine ⟨ψ, hψIrr, hψ1, indBetween (fittingOf M) (⁅M, M⁆ : Subgroup G) ψ,
    indBetween_mem_Irr_of_charInertia_le hFK hKM hFM Ψ hI, rfl,
    indBetween (⁅M, M⁆ : Subgroup G) M (indBetween (fittingOf M) (⁅M, M⁆ : Subgroup G) ψ),
    rfl, hlam, ?_, ?_, ?_, ?_⟩
  · rw [hlam]
    exact indBetween_mem_Irr_of_charInertia_le (fittingOf_le M) (le_refl M) hFM Ψ hI
  · rw [hlam, indBetween_apply_one, hψ1, mul_one,
      relIndex_fittingOf_eq_of_elementary_core_structure _h₁ hG hM hc]
  · exact not_kerContains_of_restrict_ne_one hFK hKM hHF hFM hHM Ψ (by rw [hΨμ]; exact hμ1)
  · rw [hlam]
    exact not_kerContains_of_restrict_ne_one (fittingOf_le M) (le_refl M) hHF hFM hHM Ψ
      (by rw [hΨμ]; exact hμ1)

theorem FNI_type_p_fitting_induced_witness
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_fitting_induced_witness.{u} :=
  FNI_type_p_fitting_induced_witness_aux h₁

end CFSG.FeitThompson.Proofs

end
