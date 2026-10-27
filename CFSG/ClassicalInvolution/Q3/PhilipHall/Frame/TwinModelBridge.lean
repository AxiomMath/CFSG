module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel

open CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance

@[expose] def FullOddCoreStmt (Y : Type*) [Group Y] : Prop :=
  ∀ H : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ H → ∀ α ∈ H,
    orderOf α = 2 → CFSG.Assembly.oddCore ↥(H ⊓ Subgroup.centralizer ({α} : Set (MulAut Y))) = ⊥

theorem autOddFree_of_fullOddCoreStmt {Y : Type} [Group Y] [Finite Y] (h : FullOddCoreStmt Y) :
    AutOddFree Y := by
  intro 𝒳 hinn f hf
  have hα2 : orderOf (f : MulAut Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hf
  have hfull := h 𝒳 hinn (f : MulAut Y) f.2 hα2
  set C : Subgroup 𝒳 := Subgroup.centralizer ({f} : Set 𝒳) with hC
  have hmap : C.map 𝒳.subtype = 𝒳 ⊓ Subgroup.centralizer ({(f : MulAut Y)} : Set (MulAut Y)) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, hC]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxc, rfl⟩
  have e : C ≃* ↥(𝒳 ⊓ Subgroup.centralizer ({(f : MulAut Y)} : Set (MulAut Y))) :=
    (C.equivMapOfInjective 𝒳.subtype 𝒳.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have hbot : CFSG.Assembly.oddCore ↥C = ⊥ := by
    have h1 := CFSG.EvenSmallLie.oddCore_map_mulEquiv e
    rw [hfull] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  show (CFSG.Open.componentClassificationOddCore ↥C).map C.subtype = ⊥
  have : CFSG.Open.componentClassificationOddCore ↥C = CFSG.Assembly.oddCore ↥C := rfl
  rw [this, hbot, Subgroup.map_bot]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel
