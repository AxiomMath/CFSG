
module

public import CFSG.Fischer.Polar.LinesBase
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

@[expose] public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab

local notation "PT" => perpTab ()
local notation "PL" => perpLists (perpTab ())

theorem mem_perpPerpList {q : Fin 693} {w : ℕ} :
    w ∈ (PL[0]!).filter (fun w => (PT[w]!)[q.val]!) ↔
      ∃ h : w < 693, perp ⟨w, h⟩ 0 ∧ perp ⟨w, h⟩ q := by
  rw [Array.mem_filter, mem_perpLists_zero]
  constructor
  · rintro ⟨⟨hw, h0⟩, hq⟩
    exact ⟨hw, perp_comm.1 h0, (perpTab_spec ⟨w, hw⟩ q).1 hq⟩
  · rintro ⟨hw, h0, hq⟩
    exact ⟨⟨hw, perp_comm.1 h0⟩, (perpTab_spec ⟨w, hw⟩ q).2 hq⟩

theorem perpPerp_image {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) (p q : Fin 693) :
    {w | perp w (g p) ∧ perp w (g q)} = ⇑g '' {w | perp w p ∧ perp w q} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ w, ?_, perm_apply_inv_self g w⟩
    have h1 := (hg.inv.map_perp w (g p)).2 h.1
    have h2 := (hg.inv.map_perp w (g q)).2 h.2
    rw [perm_inv_apply_self] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨w, h, rfl⟩
    exact ⟨(hg.map_perp w p).2 h.1, (hg.map_perp w q).2 h.2⟩

end CFSG.Fischer
