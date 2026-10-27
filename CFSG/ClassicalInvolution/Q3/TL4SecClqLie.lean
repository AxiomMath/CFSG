module

public import CFSG.ClassicalInvolution.Q3.TL4SecClique
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLie
public import CFSG.ClassicalInvolution.Q3.Q3T8NTri
public import CFSG.ClassicalInvolution.Q3.Q3DInputs7

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform

section Cit3


theorem secIdLieClique5_proved : SecIdLieClique5 := by
  intro n hA hP Y _ _ hn R S t hd hc hl B hB hinj hadj
  have hΩ := hd.hypOmegaGen
  have h2 := hl.isPGroup_members hc.2.2
  have hlifts := hl.hasLifts hd
  have hex := hl.exactSylow hc.2.2
  obtain ⟨hΦ, hgen, hAE⟩ := hl.liftFam_hyp hd hc
  obtain ⟨M, hM, -, hMinj, hMadj⟩ := exists_lift_clique hΩ h2 hlifts hex B hB hinj hadj
  have hcit : CITBelowT (.sl2 3 1) n := (citBelowT_three_iff (by norm_num) n).mpr hA
  exact dConnected_of_liftFam hΩ h2 hlifts hex
    (Q3T8.Asc77.dConnected_of_five_clique3 (Disc3.ih8T_three_proved n hcit) hcit hn hΦ hc.2.2
      hgen hAE M hM hMinj hMadj)

theorem secIdLieTriangle_proved : SecIdLieTriangle := by
  intro n hA hP Y _ _ hn R S t hd hc hl B hB hinj hadj
  have hΩ := hd.hypOmegaGen
  have h2 := hl.isPGroup_members hc.2.2
  have hlifts := hl.hasLifts hd
  have hex := hl.exactSylow hc.2.2
  obtain ⟨hΦ, hgen, hAE⟩ := hl.liftFam_hyp hd hc
  obtain ⟨M, hM, -, hMinj, hMadj⟩ := exists_lift_clique hΩ h2 hlifts hex B hB hinj hadj
  have hcit : CITBelowT (.sl2 3 1) n := (citBelowT_three_iff (by norm_num) n).mpr hA
  exact dstarConnected_of_liftFam hΩ h2 hlifts hex
    (Q3T8.Asc77.dstarConnected_of_triangle3 (Disc3.ih8T_three_proved n hcit) hcit hn hΦ hc.2.2
      hgen hAE M hM hMinj hMadj)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
