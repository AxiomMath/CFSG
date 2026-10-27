module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Pi2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

structure MainCtx (G : Type) [Group G] (L : Subgroup G) (t : G) (Y : Type) [Group Y]
    (S J : Subgroup (MulAut Y)) where
  π : ↥(centralizer ({t} : Set G)) →* MulAut Y
  hπ : PiData π ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  A : AutHyp Y S J
  hL : ∀ x : ↥(centralizer ({t} : Set G)), π x ∈ innerImage Y ⊤ ↔ (x : G) ∈ L
  t_mem : t ∈ L
  hinv : ∀ x : ↥(centralizer ({t} : Set G)), π x ∈ innerImage Y ⊤ → π x ≠ 1 → π x * π x = 1 →
    ∀ u ∈ L, u * u = 1 → u ≠ 1 → u ≠ t → ∃ c ∈ L, c * u * c⁻¹ = (x : G) ∨ c * u * c⁻¹ = x * t

namespace MainCtx

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {Y : Type} [Group Y]
  {S J : Subgroup (MulAut Y)} (C : MainCtx G L t Y S J)

@[expose] def tH : ↥(centralizer ({t} : Set G)) := ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def pre (B : Subgroup (MulAut Y)) : Subgroup G :=
  (B.comap C.π).map (centralizer ({t} : Set G)).subtype

theorem mem_pre {B : Subgroup (MulAut Y)} {x : G} :
    x ∈ C.pre B ↔ ∃ h : ↥(centralizer ({t} : Set G)), C.π h ∈ B ∧ (h : G) = x := by
  simp only [pre, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]

theorem pre_le_H (B : Subgroup (MulAut Y)) : C.pre B ≤ centralizer ({t} : Set G) := by
  intro x hx
  obtain ⟨h, -, rfl⟩ := (C.mem_pre).1 hx
  exact h.2

@[expose] noncomputable def pset [Fintype G] (B : Set (MulAut Y)) : Finset G :=
  Finset.univ.filter fun x => ∃ h : ↥(centralizer ({t} : Set G)), (h : G) = x ∧ C.π h ∈ B

theorem mem_pset [Fintype G] {B : Set (MulAut Y)} {x : G} :
    x ∈ C.pset B ↔ ∃ h : ↥(centralizer ({t} : Set G)), (h : G) = x ∧ C.π h ∈ B := by
  simp [pset]

theorem card_pset [Finite G] [Fintype G] (B : Set (MulAut Y)) :
    (C.pset B).card = 2 * B.ncard := by
  have : Finite ↥(centralizer ({t} : Set G)) := inferInstance
  have h1 : (C.pset B : Set G) = Subtype.val '' (C.π ⁻¹' B) := by
    ext x
    simp only [Finset.mem_coe, mem_pset, Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨h, hx, hB⟩ => ⟨h, hB, hx⟩, fun ⟨h, hB, hx⟩ => ⟨h, hx, hB⟩⟩
  rw [← Set.ncard_coe_finset, h1, Set.ncard_image_of_injective _ Subtype.val_injective,
    C.hπ.ncard_preimage]

end MainCtx

end CFSG.EvenSporadicStandard.M22Std
