module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf13Sup23
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs

public section

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q8P.Asc77
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE CFSG.ClassicalInvolution.Q3.PhilipHall.Frame



section Sup23W

theorem sup23_2P_of_thmEQ8W (hE : TwinThmEW.ThmEQ8) : Sup23_2P := by
  intro G _ _ _ Ω K K' W S R R' z u hyp
  have hst := hyp.std.setting.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hRK : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have h8 : Nat.card ↥R = 8 := hst.card8 K hK R hRK
  obtain ⟨C⟩ := Asc77.S24B.Ctx8F.nonempty hyp h8
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)
    with hH
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ H := le_sup_left
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := le_sup_right
  have hCv : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ v ∈ W₁, v * v = 1 → v ≠ 1 → v ≠ z →
      Subgroup.centralizer ({v} : Set G) ≤ H := fun W₁ hW₁ hzW₁ v hv hv2 hv1 hvz =>
    centralizer_le_of_mem_W1 C hCz hCu hW₁ hzW₁ hv hv2 hv1 hvz
  have htrans := Q3.PhilipHall.Frame.TwinPerp23.trans_of_cent hyp.std.setting hCz hCv
  have hEA : TwinThmEW.EHypAll Ω K (S : Subgroup G) W H :=
    TwinThmEW.EHypAll.of_involutions_W htrans (fun a haW ha1 ha2 => by
      by_cases haz : a = z
      · rw [haz]; exact hCz
      · exact centralizer_le_of_mem_W1 C hCz hCu hyp.hW hyp.hzW haW ha2 ha1 haz)
  exact hE G Ω K S R W H (estandQ8_of_hyp24 hyp C) hEA

end Sup23W

end CFSG.ClassicalInvolution.Q8P.P24
