module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (aeBar8 E8Pkg)

section Pre

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem phi_conj {g h : Y} (hg : g ∈ I) (hh : h ∈ I) (hc : g * h * g⁻¹ ∈ I) :
    P.φ ⟨g * h * g⁻¹, hc⟩ = P.φ ⟨g, hg⟩ * P.φ ⟨h, hh⟩ * (P.φ ⟨g, hg⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem preim_conj {X E : Subgroup (AEQ 8)} (hEX : ∀ g ∈ X, ∀ a ∈ E, g * a * g⁻¹ ∈ E) {g h : Y}
    (hg : g ∈ preim P X) (hh : h ∈ preim P E) : g * h * g⁻¹ ∈ preim P E := by
  obtain ⟨hgI, hgX⟩ := (mem_preim P).mp hg
  obtain ⟨hhI, hhE⟩ := (mem_preim P).mp hh
  have hI' : g * h * g⁻¹ ∈ I := I.mul_mem (I.mul_mem hgI hhI) (I.inv_mem hgI)
  refine mem_preim_of_mem P hI' ?_
  rw [phi_conj P hgI hhI hI']
  exact hEX _ hgX _ hhE

theorem preim_le_normalizer {X E : Subgroup (AEQ 8)} (hEX : ∀ g ∈ X, ∀ a ∈ E, g * a * g⁻¹ ∈ E) :
    preim P X ≤ Subgroup.normalizer (preim P E : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact preim_conj P hEX hg hh
  · intro hh
    have hg' : g⁻¹ ∈ preim P X := (preim P X).inv_mem hg
    have := preim_conj P hEX hg' hh
    simpa [mul_assoc] using this

theorem mem_preim_of_normalizes {X E : Subgroup (AEQ 8)} (hX : X ≤ aeBar8) (hEX : E ≤ X)
    (hn : ∀ g ∈ aeBar8, (∀ a, a ∈ E ↔ g * a * g⁻¹ ∈ E) → g ∈ X) {g : Y} (hgI : g ∈ I)
    (hg : g ∈ Subgroup.normalizer (preim P E : Set Y)) : g ∈ preim P X := by
  have hmem := Subgroup.mem_normalizer_iff.mp hg
  refine mem_preim_of_mem P hgI (hn _ (P.range_eq ▸ ⟨⟨g, hgI⟩, rfl⟩) fun a => ?_)
  constructor
  · intro haE
    have : a ∈ P.φ.range := P.range_eq ▸ hX (hEX haE)
    obtain ⟨⟨h, hhI⟩, rfl⟩ := this
    have hhA : h ∈ preim P E := mem_preim_of_mem P hhI haE
    have h1 := (hmem h).mp hhA
    obtain ⟨hI', hE'⟩ := (mem_preim P).mp h1
    rwa [phi_conj P hgI hhI hI'] at hE'
  · intro hconj
    have ha' : P.φ ⟨g, hgI⟩ * a * (P.φ ⟨g, hgI⟩)⁻¹ ∈ P.φ.range := P.range_eq ▸ hX (hEX hconj)
    have ha : a ∈ P.φ.range := by
      have e : a = (P.φ ⟨g, hgI⟩)⁻¹ * (P.φ ⟨g, hgI⟩ * a * (P.φ ⟨g, hgI⟩)⁻¹) * P.φ ⟨g, hgI⟩ := by
        group
      rw [e]
      exact P.φ.range.mul_mem (P.φ.range.mul_mem (P.φ.range.inv_mem ⟨_, rfl⟩) ha') ⟨_, rfl⟩
    obtain ⟨⟨h, hhI⟩, rfl⟩ := ha
    have hI' : g * h * g⁻¹ ∈ I := I.mul_mem (I.mul_mem hgI hhI) (I.inv_mem hgI)
    have hgh : g * h * g⁻¹ ∈ preim P E := mem_preim_of_mem P hI' (by rw [phi_conj P hgI hhI hI']; exact hconj)
    exact ((mem_preim P).mp ((hmem h).mpr hgh)).2

theorem isElemAbelian2_preim {E : Subgroup (AEQ 8)} (hE : E ≤ aeBar8) (hsq : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 64) : IsElemAbelian2 (preim P E) 6 := by
  refine ⟨by rw [card_preim P hE, hcard]; norm_num, ?_⟩
  intro g hg
  obtain ⟨hgI, hgE⟩ := (mem_preim P).mp hg
  have : (⟨g, hgI⟩ : ↥I) * ⟨g, hgI⟩ = 1 := by
    apply P.inj
    rw [map_mul, map_one]
    exact hsq _ hgE
  exact congrArg Subtype.val this

theorem isPGroup_preim {E : Subgroup (AEQ 8)} (hE : E ≤ aeBar8) (hsq : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 64) : IsPGroup 2 (preim P E) :=
  IsPGroup.of_card (n := 6) (by rw [card_preim P hE, hcard]; norm_num)

end Pre

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
