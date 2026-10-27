module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.Uniqueness.SU.SU10Prod

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem isInternalDirect_sylow {K X Y P : Subgroup G} (hK : IsInternalDirect K X Y)
    (hP : IsSylowIn 2 K P) : IsInternalDirect P (X ⊓ P) (Y ⊓ P) := by
  obtain ⟨hsup, hinf, hcomm⟩ := hK
  have hP' : CFSG.GH74.Uniqueness.SU.SU4.IsSylowIn (X ⊔ Y) P := by
    rw [hsup]
    exact ⟨hP.1, hP.2.1, Nat.not_even_iff_odd.mp fun hev => hP.2.2 (even_iff_two_dvd.mp hev)⟩
  refine ⟨?_, ?_, fun u hu v hv => hcomm u hu.1 v hv.1⟩
  · rw [inf_comm X P, inf_comm Y P]
    exact CFSG.GH74.Uniqueness.SU.SU10.inf_sup_eq_of_isSylowIn hcomm hP'
  · rw [eq_bot_iff, ← hinf]
    exact inf_le_inf inf_le_left inf_le_left

end CFSG.OddStandard.HigherRank.YamadaG23
