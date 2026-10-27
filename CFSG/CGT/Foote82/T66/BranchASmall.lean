module

public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.CitedBAS
import CFSG.CGT.Foote82.T66.BranchASmallMcLMain
import CFSG.CGT.Foote82.T66.BranchASmallTypes

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

private theorem false_of_type {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {G L : Subgroup (GLV V)} {z : GLV V} (hc : BAS.Hyp G L z) (h19 : BASMaximal)
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3)
    (hbig : ∀ g ∈ G, g * z * g⁻¹ ≠ z → (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      Module.finrank (ZMod 2) ↥(BAS.tvComm L (g * z * g⁻¹)) ≤
        Module.finrank (ZMod 2) ↥(tildeVBot L) + 1) : False := by
  have hle := hc.finrank_commSpace_z_le_one
    (fun d hd hd2 hrank => h19 V L htype hc.faithful hc.irrTilde d hd hd2 hrank) hbig
  have hpos : 0 < Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) := by
    haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.commSpace_z_ne_bot
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  exact hc.false_of_transvection htype (by omega)

theorem branchASmall (h7 : BASThreeA6) (h6 : BASA6NoSix) (h15 : BASOmegaEight)
    (h18 : BASTIFails) (h19 : BASMaximal) : BranchASmall := by
  intro V _ _ _ G L z hconf htype
  have hc : BAS.Hyp G L z := ⟨hconf⟩
  rcases htype with hA | hU | hO | hZ
  · exact false_of_type hc h19 (Or.inl hA) fun g hg hne hcomm =>
      hc.finrank_tvComm_le_of_TI h18 (Or.inl hA) hg hne hcomm
  · exact false_of_type hc h19 (Or.inr (Or.inl hU)) fun g hg hne hcomm =>
      hc.finrank_tvComm_le_of_TI h18 (Or.inr hU) hg hne hcomm
  · exact false_of_type hc h19 (Or.inr (Or.inr hO)) fun g hg hne hcomm =>
      hc.finrank_tvComm_le_of_eight h15 hO hg hne hcomm
  ·
    exact hc.false_of_A6Z3 h7 h6 hZ

end CFSG.CGT.Foote82
