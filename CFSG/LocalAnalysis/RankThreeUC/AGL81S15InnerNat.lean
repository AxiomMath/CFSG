module

public import CFSG.RankThree.FFModules.ClassificationSL3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerCliff

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules
open scoped MatrixGroups

section Restrict

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] {L B : Subgroup K}

@[expose] noncomputable def stabRep (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) : Representation (ZMod 2) ↥(stabIn h κ Y) ↥Y :=
  (⟨Y, fun g _ hv => g.2.2 _ hv⟩ :
    Subrepresentation (κ.comp (stabIn h κ Y).subtype)).toRepresentation

theorem stabRep_coe (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (b : ↥(stabIn h κ Y)) (y : ↥Y) :
    ((stabRep h κ Y b y : ↥Y) : Z) = κ (b : K) y := rfl

@[expose] noncomputable def stabImage (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) : Subgroup (↥Y ≃ₗ[ZMod 2] ↥Y) :=
  (repGL (stabRep h κ Y)).range

theorem mem_stabImage (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) {a : ↥Y ≃ₗ[ZMod 2] ↥Y} :
    a ∈ stabImage h κ Y ↔ ∃ b ∈ stabIn h κ Y, ∀ y : ↥Y, ((a y : ↥Y) : Z) = κ b y := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, fun y => rfl⟩
  · rintro ⟨b, hb, hy⟩
    refine ⟨⟨b, hb⟩, LinearEquiv.ext fun y => Subtype.ext ?_⟩
    exact (hy y).symm

theorem stabImage_sq (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) : ∀ a ∈ stabImage h κ Y, a * a = 1 := by
  rintro _ ⟨b, rfl⟩
  rw [← map_mul]
  have hbb : b * b = 1 := Subtype.ext (h.sq b b.2.1)
  rw [hbb, map_one]

theorem stabImage_comm (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) :
    ∀ a ∈ stabImage h κ Y, ∀ a' ∈ stabImage h κ Y, a * a' = a' * a := by
  rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
  rw [← map_mul, ← map_mul]
  have : b * b' = b' * b := Subtype.ext (h.comm b b.2.1 b' b'.2.1)
  rw [this]

theorem stabImage_quad (h : InnerCtx L B) {κ : Representation (ZMod 2) K Z}
    (hd : ChiefData L B κ) (Y : Submodule (ZMod 2) Z) :
    ∀ a ∈ stabImage h κ Y, ∀ a' ∈ stabImage h κ Y, ∀ w : ↥Y, a' (a w - w) = a w - w := by
  rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ w
  apply Subtype.ext
  exact hd.quad b b.2.1 b' b'.2.1 (w : Z)

theorem card_stabIn (h : InnerCtx L B) {κ : Representation (ZMod 2) K Z}
    (hd : ChiefData L B κ) {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) :
    Nat.card ↥(stabIn h κ Y) =
      Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y) := by
  haveI := hd.nontrivial
  have hle : B ⊓ MonoidHom.ker κ ≤ stabIn h κ Y := fun b hb =>
    ⟨hb.1, fun y hy => by
      have : κ b y = y := LinearMap.congr_fun (MonoidHom.mem_ker.mp hb.2) y
      rw [this]
      exact hy⟩
  have hker : (repGL (stabRep h κ Y)).ker = (B ⊓ MonoidHom.ker κ).subgroupOf (stabIn h κ Y) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · intro hb
      have hbY : ∀ y ∈ Y, κ (b : K) y = y := fun y hy =>
        congrArg Subtype.val (LinearEquiv.congr_fun hb ⟨y, hy⟩)
      refine ⟨b.2.1, LinearMap.ext fun z => ?_⟩
      exact h.kappa_eq_one_of_fix κ hd.irr Y hY.inv hnt b.2.1 hbY z
    · rintro ⟨-, hb⟩
      refine LinearEquiv.ext fun y => Subtype.ext ?_
      have : κ (b : K) y = y := LinearMap.congr_fun hb (y : Z)
      exact this
  have h1 := Subgroup.card_mul_index (repGL (stabRep h κ Y)).ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  rw [← h1]
  rfl

theorem card_fix_stabImage (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) :
    Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} =
      Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨(y.1 : Z), mem_fixSub.mpr fun b hb => ?_, y.1.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.2⟩, fun a ha => ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have hmem : repGL (stabRep h κ Y) ⟨b, hb⟩ ∈ stabImage h κ Y := ⟨⟨b, hb⟩, rfl⟩
    have := congrArg Subtype.val (y.2 _ hmem)
    exact this
  · obtain ⟨b, hb, hab⟩ := (mem_stabImage h κ Y).mp ha
    apply Subtype.ext
    rw [hab]
    exact mem_fixSub.mp w.2.1 b hb

end Restrict

section Rho

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] {L B : Subgroup K}
  {F : Type} [Field F]

@[expose] noncomputable def rhoY (e : ↥L ≃* SL(3, F)) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) :
    Representation (ZMod 2) SL(3, F) ↥Y :=
  ((⟨Y, fun g _ hv => hY g g.2 _ hv⟩ :
    Subrepresentation (κ.comp L.subtype)).toRepresentation).comp e.symm.toMonoidHom

theorem rhoY_coe (e : ↥L ≃* SL(3, F)) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) (g : SL(3, F)) (y : ↥Y) :
    ((rhoY e κ Y hY g y : ↥Y) : Z) = κ ((e.symm g : ↥L) : K) y := rfl

theorem rhoY_irreducible (e : ↥L ≃* SL(3, F)) {κ : Representation (ZMod 2) K Z}
    {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) : (rhoY e κ Y hY.inv).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hY.ne_bot, fun W hW => ?_⟩
  have hinv : ∀ l ∈ L, ∀ w ∈ W.map Y.subtype, κ l w ∈ W.map Y.subtype := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨rhoY e κ Y hY.inv (e ⟨l, hl⟩) w, hW _ w hw, ?_⟩
    rw [Submodule.subtype_apply, rhoY_coe, MulEquiv.symm_apply_apply]
    rfl
  rcases hY.min _ (Submodule.map_subtype_le Y W) hinv with hbot | htop
  · left
    have h1 : W.map Y.subtype = (⊥ : Submodule (ZMod 2) ↥Y).map Y.subtype := by
      rw [hbot, Submodule.map_bot]
    exact Submodule.map_injective_of_injective Y.injective_subtype h1
  · right
    have h1 : W.map Y.subtype = (⊤ : Submodule (ZMod 2) ↥Y).map Y.subtype := by
      rw [htop, Submodule.map_subtype_top]
    exact Submodule.map_injective_of_injective Y.injective_subtype h1

theorem rhoY_nontrivial (e : ↥L ≃* SL(3, F)) {κ : Representation (ZMod 2) K Z}
    {Y : Submodule (ZMod 2) Z} (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) : ∃ g, rhoY e κ Y hY g ≠ 1 := by
  obtain ⟨l, hl, y, hy, hne⟩ := hnt
  refine ⟨e ⟨l, hl⟩, fun hg => hne ?_⟩
  have := congrArg (fun f : ↥Y →ₗ[ZMod 2] ↥Y => ((f ⟨y, hy⟩ : ↥Y) : Z)) hg
  simpa [rhoY_coe] using this

theorem rhoY_ker [Finite F] (e : ↥L ≃* SL(3, F)) {κ : Representation (ZMod 2) K Z}
    {Y : Submodule (ZMod 2) Z} (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) :
    ∀ x : SL(3, F), rhoY e κ Y hY x = 1 →
      x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F :=
  ker_le_scalars (rhoY e κ Y hY) (rhoY_nontrivial e hY hnt)

theorem stabImage_intertwines (h : InnerCtx L B) (e : ↥L ≃* SL(3, F))
    (κ : Representation (ZMod 2) K Z) (Y : Submodule (ZMod 2) Z)
    (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) :
    ∀ a ∈ stabImage h κ Y, ∀ x : SL(3, F), ∃ y,
      CFSG.QuasithinUnique.Setup.X7a.Intertwines (rhoY e κ Y hY) a x y := by
  intro a ha x
  obtain ⟨b, hb, hab⟩ := (mem_stabImage h κ Y).mp ha
  set l : ↥L := e.symm x with hl
  have hconj : b * (l : K) * b⁻¹ ∈ L := h.normalizes b hb.1 l l.2
  refine ⟨e ⟨b * (l : K) * b⁻¹, hconj⟩, fun u => ?_⟩
  apply Subtype.ext
  rw [hab, rhoY_coe, rhoY_coe, MulEquiv.symm_apply_apply, hab]
  show κ b (κ (l : K) u) = κ (b * (l : K) * b⁻¹) (κ b u)
  rw [← repMulApply, ← repMulApply, show b * (l : K) * b⁻¹ * b = b * (l : K) by group]

end Rho

end CFSG.LocalAnalysis.RankThreeUC.S15
