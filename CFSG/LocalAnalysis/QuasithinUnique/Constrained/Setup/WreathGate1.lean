module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Model

variable {H : Type*} [Group H] {V : Subgroup H} {Wm : Type*} [AddCommGroup Wm]
  [Module (ZMod 2) Wm]

@[expose] def modelIso : Submodule (ZMod 2) Wm ≃o Subgroup (Multiplicative Wm) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup

@[expose] def modelSub (θ : ↥V ≃* Multiplicative Wm) (U : Submodule (ZMod 2) Wm) : Subgroup H :=
  ((modelIso U).map θ.symm.toMonoidHom).map V.subtype

theorem mem_modelSub {θ : ↥V ≃* Multiplicative Wm} {U : Submodule (ZMod 2) Wm} {x : H} :
    x ∈ modelSub θ U ↔ ∃ hx : x ∈ V, Multiplicative.toAdd (θ ⟨x, hx⟩) ∈ U := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(θ.symm z).2, ?_⟩
    have h1 : θ ⟨V.subtype (θ.symm.toMonoidHom z), (θ.symm z).2⟩ = z := θ.apply_symm_apply z
    rw [h1]
    exact hz
  · rintro ⟨hx, hU⟩
    exact ⟨⟨x, hx⟩, ⟨θ ⟨x, hx⟩, hU, by simp⟩, rfl⟩

theorem modelSub_le (θ : ↥V ≃* Multiplicative Wm) (U : Submodule (ZMod 2) Wm) :
    modelSub θ U ≤ V := fun _ hx => (mem_modelSub.mp hx).1

theorem modelSub_le_iff (θ : ↥V ≃* Multiplicative Wm) {U U' : Submodule (ZMod 2) Wm} :
    modelSub θ U ≤ modelSub θ U' ↔ U ≤ U' := by
  unfold modelSub
  rw [Subgroup.map_le_map_iff_of_injective V.subtype_injective,
    Subgroup.map_le_map_iff_of_injective θ.symm.injective, OrderIso.le_iff_le]

theorem modelSub_sup (θ : ↥V ≃* Multiplicative Wm) (U U' : Submodule (ZMod 2) Wm) :
    modelSub (H := H) θ (U ⊔ U') = modelSub θ U ⊔ modelSub θ U' := by
  unfold modelSub
  rw [OrderIso.map_sup, Subgroup.map_sup]
  exact Subgroup.map_sup _ _ _

theorem modelSub_iSup (θ : ↥V ≃* Multiplicative Wm) {ι : Sort*} (U : ι → Submodule (ZMod 2) Wm) :
    modelSub (H := H) θ (⨆ i, U i) = ⨆ i, modelSub θ (U i) := by
  unfold modelSub
  rw [OrderIso.map_iSup, Subgroup.map_iSup, Subgroup.map_iSup]

theorem modelSub_inf (θ : ↥V ≃* Multiplicative Wm) (U U' : Submodule (ZMod 2) Wm) :
    modelSub (H := H) θ (U ⊓ U') = modelSub θ U ⊓ modelSub θ U' := by
  unfold modelSub
  rw [OrderIso.map_inf, Subgroup.map_inf _ _ _ θ.symm.injective,
    Subgroup.map_inf _ _ _ V.subtype_injective]

theorem modelSub_bot (θ : ↥V ≃* Multiplicative Wm) :
    modelSub (H := H) θ ⊥ = ⊥ := by
  unfold modelSub
  rw [OrderIso.map_bot, Subgroup.map_bot, Subgroup.map_bot]

theorem modelSub_top (θ : ↥V ≃* Multiplicative Wm) :
    modelSub (H := H) θ ⊤ = V := by
  ext x
  rw [mem_modelSub]
  exact ⟨fun h => h.1, fun hx => ⟨hx, Submodule.mem_top⟩⟩

theorem card_modelSub (θ : ↥V ≃* Multiplicative Wm) (U : Submodule (ZMod 2) Wm) :
    Nat.card ↥(modelSub (H := H) θ U) = Nat.card ↥U := by
  unfold modelSub
  rw [Subgroup.card_map_of_injective V.subtype_injective,
    Subgroup.card_map_of_injective θ.symm.injective]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun z => Iff.rfl)

theorem iSupIndep_modelSub (θ : ↥V ≃* Multiplicative Wm) {ι : Type*} {U : ι → Submodule (ZMod 2) Wm}
    (hU : iSupIndep U) : iSupIndep fun i => modelSub (H := H) θ (U i) := by
  have h1 : iSupIndep fun i => modelIso (U i) := (iSupIndep_map_orderIso_iff modelIso).2 hU
  have h2 := CFSG.LocalCores.iSupIndep_map_of_injective (f := θ.symm.toMonoidHom)
    θ.symm.injective h1
  exact CFSG.LocalCores.iSupIndep_map_of_injective (f := V.subtype) V.subtype_injective h2

end Model

section Action

variable {H : Type*} [Group H] {V : Subgroup H} {Wm : Type*} [AddCommGroup Wm]
  [Module (ZMod 2) Wm] [V.Normal]

@[expose] noncomputable def modelRho (θ : ↥V ≃* Multiplicative Wm) : H →* (Wm ≃ₗ[ZMod 2] Wm) :=
  (Layer.binPsi θ).toMonoidHom.comp MulAut.conjNormal

theorem modelRho_apply (θ : ↥V ≃* Multiplicative Wm) (x : H) (v : ↥V) :
    modelRho θ x (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (MulAut.conjNormal x v)) := by
  show Layer.binPsi θ (MulAut.conjNormal x) (Multiplicative.toAdd (θ v)) = _
  rw [Layer.binPsi_apply]
  simp

theorem autOn_eq_map (X : Subgroup H) :
    autOn X V = X.map (MulAut.conjNormal : H →* MulAut ↥V) := by
  ext φ
  rw [mem_autOn_iff, Subgroup.mem_map]
  have hn : ∀ x : H, x ∈ Subgroup.normalizer (V : Set H) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr ‹V.Normal›]
    exact Subgroup.mem_top x
  have key : ∀ x : H, conjAct V ⟨x, hn x⟩ = MulAut.conjNormal x := by
    intro x
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [coe_conjAct_apply, MulAut.conjNormal_apply]
  constructor
  · rintro ⟨g, hgX, rfl⟩
    exact ⟨g.1, hgX, (key g.1).symm⟩
  · rintro ⟨x, hxX, rfl⟩
    exact ⟨⟨x, hn x⟩, hxX, key x⟩

theorem ker_conjNormal : (MulAut.conjNormal : H →* MulAut ↥V).ker =
    Subgroup.centralizer (V : Set H) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx v hv
    have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : H)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    have h2 : x * v = v * x := by
      calc x * v = (x * v * x⁻¹) * x := by group
        _ = v * x := by rw [h1]
    exact h2.symm
  · intro hx
    refine MulEquiv.ext fun v => Subtype.ext ?_
    show ((MulAut.conjNormal x v : ↥V) : H) = (v : H)
    rw [MulAut.conjNormal_apply]
    have := hx v v.2
    calc x * (v : H) * x⁻¹ = (v : H) * x * x⁻¹ := by rw [this]
      _ = (v : H) := by group

theorem ker_modelRho (θ : ↥V ≃* Multiplicative Wm) :
    (modelRho θ).ker = Subgroup.centralizer (V : Set H) := by
  rw [← ker_conjNormal (V := V)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Layer.binPsi θ (MulAut.conjNormal x) = 1 := h
    exact (Layer.binPsi θ).injective (h1.trans (map_one (Layer.binPsi θ)).symm)
  · show Layer.binPsi θ (MulAut.conjNormal x) = 1
    rw [h, map_one]

theorem map_modelRho (θ : ↥V ≃* Multiplicative Wm) (X : Subgroup H) :
    X.map (modelRho θ) = (autOn X V).map (Layer.binPsi θ).toMonoidHom := by
  rw [autOn_eq_map, Subgroup.map_map]
  rfl

end Action

end CFSG.QuasithinUnique.Setup.Wreath
