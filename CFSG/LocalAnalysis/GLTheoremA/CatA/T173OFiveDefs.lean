module

public import CFSG.Blueprint.ChevalleyWeyl
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley

structure S172DModel {Ω : Type} [Group Ω] (S B : Subgroup Ω) {Γ : Type} [Group Γ]
    (G₀ Ghat : Subgroup Γ) where
  π : ↥S →* ↥G₀
  β : ↥B →* ↥Ghat
  surj : Function.Surjective π
  ker_π : π.ker = Subgroup.center ↥S
  conj : ∀ (b : ↥B) (s t : ↥S), (t : Ω) = (b : Ω)⁻¹ * s * b →
    ((π t : ↥G₀) : Γ) = ((β b : ↥Ghat) : Γ)⁻¹ * ((π s : ↥G₀) : Γ) * ((β b : ↥Ghat) : Γ)
  le : G₀ ≤ Ghat
  faithful : ∀ g ∈ Ghat, (∀ h ∈ G₀, g * h = h * g) → g = 1

@[expose] def stdLayerD {Γ : Type} [Group Γ] (G₀ : Subgroup Γ) (d : Γ) : Subgroup Γ :=
  GLALayer (G₀ ⊓ Subgroup.centralizer ({d} : Set Γ))

namespace S172DModel

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

@[expose] def piImg (M : S172DModel S B G₀ Ghat) (X : Subgroup Ω) : Subgroup Γ :=
  ((X.subgroupOf S).map M.π).map G₀.subtype

@[expose] def img (M : S172DModel S B G₀ Ghat) (X : Subgroup Ω) : Subgroup Γ :=
  ((X.subgroupOf B).map M.β).map Ghat.subtype

@[expose] def barB (M : S172DModel S B G₀ Ghat) : Subgroup Γ := M.β.range.map Ghat.subtype

variable (M : S172DModel S B G₀ Ghat)

theorem mem_piImg {X : Subgroup Ω} {x : Γ} :
    x ∈ M.piImg X ↔ ∃ s : ↥S, (s : Ω) ∈ X ∧ ((M.π s : ↥G₀) : Γ) = x := by
  simp only [S172DModel.piImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨M.π s, ⟨s, hs, rfl⟩, rfl⟩

theorem mem_barB {y : Γ} :
    y ∈ M.barB ↔ ∃ b : ↥B, ((M.β b : ↥Ghat) : Γ) = y := by
  rw [S172DModel.barB, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hya⟩
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 ha
    exact ⟨b, hya⟩
  · rintro ⟨b, rfl⟩
    exact ⟨M.β b, ⟨b, rfl⟩, rfl⟩

end S172DModel

@[expose] noncomputable def e6TorusThree
    (F : Type) [Field F] (ζ : Fˣ) :
    Subgroup (ModGL Tag.E6 F) :=
  Subgroup.closure (Set.range fun i : Fin Tag.E6.rank => torusElt Tag.E6 F i ζ)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
