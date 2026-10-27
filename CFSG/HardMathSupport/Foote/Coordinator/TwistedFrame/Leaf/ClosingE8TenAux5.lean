module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [Field L] [Algebra K L]


theorem Fv_smul (Fr : L →+* L) (a : L) (c : Fn L) : Fv Fr (a • c) = Fr a • Fv Fr c := by
  funext ν
  simp [Fv]

@[expose] def Qrat (h : ModGL Tag.E8 L) : Subgroup (ModGL Tag.E8 K) where
  carrier := {q | h⁻¹ * baseChangeGL (algebraMap K L) q * h ∈ Qθ Tag.E8 L}
  mul_mem' := by
    intro q q' hq hq'
    simp only [Set.mem_setOf_eq] at hq hq' ⊢
    have e : h⁻¹ * baseChangeGL (algebraMap K L) (q * q') * h =
        (h⁻¹ * baseChangeGL (algebraMap K L) q * h) *
          (h⁻¹ * baseChangeGL (algebraMap K L) q' * h) := by
      rw [map_mul]
      group
    rw [e]
    exact mul_mem hq hq'
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one]
    rw [mul_one, inv_mul_cancel]
    exact one_mem _
  inv_mem' := by
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    have e : h⁻¹ * baseChangeGL (algebraMap K L) q⁻¹ * h =
        (h⁻¹ * baseChangeGL (algebraMap K L) q * h)⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    exact inv_mem hq

theorem mem_Qrat {h : ModGL Tag.E8 L} {q : ModGL Tag.E8 K} :
    q ∈ Qrat h ↔ h⁻¹ * baseChangeGL (algebraMap K L) q * h ∈ Qθ Tag.E8 L := Iff.rfl

@[expose] def Cc (h : ModGL Tag.E8 L) (q : ModGL Tag.E8 K) : Fn L :=
  heisCoord Tag.E8 L (h⁻¹ * baseChangeGL (algebraMap K L) q * h)

theorem Cc_mul {h : ModGL Tag.E8 L} {q q' : ModGL Tag.E8 K} (hq : q ∈ Qrat h) (hq' : q' ∈ Qrat h) :
    Cc h (q * q') = Cc h q + Cc h q' := by
  have e : h⁻¹ * baseChangeGL (algebraMap K L) (q * q') * h =
      (h⁻¹ * baseChangeGL (algebraMap K L) q * h) *
        (h⁻¹ * baseChangeGL (algebraMap K L) q' * h) := by
    rw [map_mul]
    group
  unfold Cc
  rw [e]
  exact (heisCoord_spec Tag.E8 L).mul _ hq _ hq'

@[expose] def Uspace (h : ModGL Tag.E8 L) (H : Subgroup (ModGL Tag.E8 K)) : Submodule L (Fn L) :=
  Submodule.span L (Cc h '' ((H ⊓ Qrat h : Subgroup (ModGL Tag.E8 K)) : Set (ModGL Tag.E8 K)))

theorem Cc_mem_Uspace {h : ModGL Tag.E8 L} {H : Subgroup (ModGL Tag.E8 K)} {q : ModGL Tag.E8 K}
    (hq : q ∈ H) (hr : q ∈ Qrat h) : Cc h q ∈ Uspace h H :=
  Submodule.subset_span ⟨q, ⟨hq, hr⟩, rfl⟩

theorem Uspace_supp (h : ModGL Tag.E8 L) (H : Subgroup (ModGL Tag.E8 K)) {u : Fn L}
    (hu : u ∈ Uspace h H) : ∀ β, β ∉ Deg1 Tag.E8 → u β = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, hq, rfl⟩ := hx
    exact fun β hβ => (heisCoord_spec Tag.E8 L).support _ hq.2 β hβ
  | zero => exact fun β _ => rfl
  | add x y _ _ hx hy => exact fun β hβ => by simp [hx β hβ, hy β hβ]
  | smul a x _ hx => exact fun β hβ => by simp [hx β hβ]

theorem Uspace_inv (h : ModGL Tag.E8 L) (H : Subgroup (ModGL Tag.E8 K)) {x : ModGL Tag.E8 L}
    {M : Fn L →ₗ[L] Fn L} (hx : ActsBy x M) {l₀ : ModGL Tag.E8 K} (hl₀ : l₀ ∈ H)
    (hl : baseChangeGL (algebraMap K L) l₀ = h * x * h⁻¹) :
    ∀ u ∈ Uspace h H, M u ∈ Uspace h H := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q, hq, rfl⟩ := hv
    have hqH : q ∈ H := hq.1
    have hqQ : h⁻¹ * baseChangeGL (algebraMap K L) q * h ∈ Qθ Tag.E8 L := hq.2
    obtain ⟨hy, hyc⟩ := hx _ hqQ
    have e : h⁻¹ * baseChangeGL (algebraMap K L) (l₀ * q * l₀⁻¹) * h =
        x * (h⁻¹ * baseChangeGL (algebraMap K L) q * h) * x⁻¹ := by
      rw [map_mul, map_mul, map_inv, hl]
      group
    have hmemQ : l₀ * q * l₀⁻¹ ∈ Qrat h := by
      rw [mem_Qrat, e]
      exact hy
    have := Cc_mem_Uspace (h := h) (H := H) (H.mul_mem (H.mul_mem hl₀ hqH) (H.inv_mem hl₀)) hmemQ
    have hc : Cc h (l₀ * q * l₀⁻¹) = M (Cc h q) := by
      unfold Cc
      rw [e, hyc]
    rwa [hc] at this
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem Uspace_sigma (h : ModGL Tag.E8 L) (H : Subgroup (ModGL Tag.E8 K)) (Fr : L →+* L)
    (hfix : ∀ a : K, Fr (algebraMap K L a) = algebraMap K L a) {n : ModGL Tag.E8 L}
    (hlang : Frob Fr h = h * n) {M : Fn L →ₗ[L] Fn L} (hn : ActsBy n M) :
    ∀ u ∈ Uspace h H, M (Fv Fr u) ∈ Uspace h H := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q, hq, rfl⟩ := hv
    have := sigma_fixed_coords (algebraMap K L) Fr hfix hlang hn q hq.2
    change M (Fv Fr (Cc h q)) ∈ _
    unfold Cc
    rw [this]
    exact Cc_mem_Uspace hq.1 hq.2
  | zero => simpa [Fv_zero] using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Fv_add, map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Fv_smul, map_smul]; exact Submodule.smul_mem _ _ hx

theorem block_of_coord (h : ModGL Tag.E8 L) (H : Subgroup (ModGL Tag.E8 K)) (Fr : L →+* L)
    (hfix : ∀ a : K, Fr (algebraMap K L a) = algebraMap K L a) {n : ModGL Tag.E8 L}
    (hlang : Frob Fr h = h * n) {M : Fn L →ₗ[L] Fn L} (hn : ActsBy n M) {w : WeylGroup Tag.E8}
    (hM : ∀ μ ∈ mRoots, ∃ ε : L, ε ≠ 0 ∧ M (Pi.single μ (1 : L)) = Pi.single (w • μ) ε)
    (hw : ∀ μ ∈ mRoots, w • μ ∈ mRoots ∧ cls (w • μ) = 5 - cls μ)
    (hU : InvE (Uspace h H)) {u : Fn L} (hu : u ∈ Uspace h H) {μ : Fin Tag.E8.rank → ℤ}
    (hμ : μ ∈ mRoots) (h0 : u μ ≠ 0) :
    ∀ ν ∈ mRoots, (cls ν = cls μ ∨ cls ν = 5 - cls μ) →
      (Pi.single ν (1 : L) : Fn L) ∈ Uspace h H := by
  have hd : μ ∈ deg1Roots := by
    rw [mem_deg1Roots]
    obtain ⟨a, b, -⟩ := mem_mRoots.1 hμ
    exact ⟨a, b⟩
  have h1 := single_mem_of_coord_ne hU hu hd h0
  intro ν hν hc
  rcases hc with hc | hc
  · exact single_mem_of_cls hU hμ hν hc.symm h1
  · obtain ⟨hwm, hwc⟩ := hw μ hμ
    obtain ⟨ε, hε, hMs⟩ := hM μ hμ
    have hσ := Uspace_sigma h H Fr hfix hlang hn _ h1
    rw [Fv_single, map_one, hMs] at hσ
    have h2 : (Pi.single (w • μ) (1 : L) : Fn L) ∈ Uspace h H := by
      have : (Pi.single (w • μ) (1 : L) : Fn L) = ε⁻¹ • (Pi.single (w • μ) ε : Fn L) := by
        funext ν'
        by_cases he : ν' = w • μ
        · subst he; simp [hε]
        · simp [Pi.single_eq_of_ne he]
      rw [this]
      exact Submodule.smul_mem _ _ hσ
    exact single_mem_of_cls hU hwm hν (by rw [hwc, hc]) h2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
