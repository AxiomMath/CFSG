module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecConj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open scoped commutatorElement

section Datum

variable {G : Type} [Group G] [Finite G]

theorem conjClass_eq_of_mem {K₀ K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) :
    CoreAssembly.conjClass K = CoreAssembly.conjClass K₀ := by
  obtain ⟨g, rfl⟩ := hK
  exact conjClass_conjSub g K₀

theorem tightCore_eq_of_mem {R : Subgroup G} (hRc : tightCore R = R) {M : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) : tightCore M = M := by
  obtain ⟨g, rfl⟩ := hM
  rw [hRc, ← conjSub_tightCore, hRc]

variable {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}

theorem exists_datum_at (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) {M : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) {z : G} (hz : IsUniqueInvolution M z) :
    ∃ S' : Sylow 2 ↥M, TwinCoreHyp n G M S' z := by
  obtain ⟨g, rfl⟩ := hM
  have hz' : g * t₀ * g⁻¹ = z :=
    ((Q8Datum.isUniqueInvolution_core h.datum).conj g).eq hz
  rw [hRc]
  rw [hRc] at hz
  obtain ⟨S', hh⟩ := twinCoreHyp_conj h g
  rw [hz'] at hh
  exact ⟨S', hh⟩

end Datum

section Targets

variable {G : Type} [Group G] [Finite G]

@[expose] def TwinFrameUActs (Ω : Set (Subgroup G)) : Prop :=
  ∀ (K K' J : Subgroup G) (z u t : G), TwinFrameData Ω K K' z u J t →
    u ∈ centralizerModOdd ⊤ J

end Targets

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
