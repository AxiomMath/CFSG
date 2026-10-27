module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Existence

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem exists_isS (hT2 : IsPGroup 2 (sylT d)) (hTI : sylT d ≤ Ig d) : ∃ S, IsS d S := by
  have hfin : {P : Subgroup G | P ≤ Ig d ∧ IsPGroup 2 P ∧ sylT d ≤ P}.Finite := Set.toFinite _
  obtain ⟨S, hS, hmax⟩ := hfin.exists_maximalFor id _ ⟨sylT d, hTI, hT2, le_rfl⟩
  refine ⟨S, ⟨hS.1, hS.2.1, fun P hP hP2 hSP => ?_⟩, hS.2.2⟩
  exact le_antisymm (hmax ⟨hP, hP2, hS.2.2.trans hSP⟩ hSP) hSP

end Existence

section Final


theorem titsThm49StatementExclusion_of_steps
    (sZ0 : StepZ0Inv) (sK : StepKappa) (s05 : Step05) (s07 : Step07) (s08 : Step08) (s09 : Step09)
    (s10 : Step10) (s11 : Step11) (s12 : Step12) (s13 : Step13) (s14 : Step14) (s15 : Step15)
    (s16 : Step16) (s17s : Step17s) (s17 : Step17) (s18 : Step18) (s19 : Step19) (s19b : Step19b)
    (s20 : Step20) (s21 : Step21) (s22 : Step22) (s23a : Step23a) (s23b : Step23b) (s23c : Step23c)
    (s24 : Step24) (s25 : Step25) (s26 : Step26) :
    CFSG.Yardstones.M41b0c98b3153.TitsThm49StatementExclusion := by
  intro G _ _ d hd h49
  obtain ⟨z₀, hz⟩ := hd.s56_exists_S56Z0 h49
  have hinv := sZ0 h49 hd
  have h05 := s05 h49 hd hz
  have h06 := hd.s56_V_shape h49 hz
  have h07 := s07 h49 hd
  have h08 := s08 h49 hd hz hinv h05 h06 h07
  have h09 := s09 h49 hd hz (sK h49 hd) h05 h07 h08
  have h10 := s10 h49 hd hz hinv h05 h06 h07 h08 h09
  have h11 := s11 h49 hd hz h05 h07 h08 h09 h10
  have h12 := s12 h49 hd hz hinv h06 h09 h10 h11
  have h13 := s13 h49 hd hz h07 h08 h10 h11 h12
  have h14 := s14 h49 hd hz h10 h11 h12 h13
  have h15 := s15 h49 hd hz h10
  have h17s := s17s h49 hd hz h05 h09 h10
  have h16 := s16 h49 hd hz h09 h10 h12 h14 h15 h17s
  have h17 := s17 h49 hd hz h09 h10 h14 h15 h16 h17s
  have h18 := s18 h49 hd hz (sK h49 hd) h09 h10 h14 h17s h17
  have h19 := s19 h49 hd hz h09 h10 h14 h17s h17 h18
  have h19b := s19b h49 hd hz
  have h20 := s20 h49 hd hz h09 h14 h17s h17 h18 h19
  have h21 := s21 h49 hd hz h09 h19 h19b h20
  have h22 := s22 h49 hd hz h14 h17s h17 h19 h20 h21
  have h23a := s23a h49 hd hz hinv h10 h14 h16 h17s h17 h19 h20 h21 h22
  have h23b := s23b h49 hd hz hinv h10 h14 h17 h19 h23a
  have h23c := s23c h49 hd hz h10 h14 h17s h17 h19 h20 h21 h23a h23b
  have h24 := s24 h49 hd hz h07 h10 h11 h12 h13 h14 h16 h19 h20 h21 h22 h23a h23b h23c
  have h25 := s25 h49 hd hz h09 h17 h19 h20 h21 h22 h24
  have h26 := s26 h49 hd hz h22 h23a h25
  obtain ⟨S, hS⟩ := exists_isS h09.2.2.2.2.2.2.2.1.2.1 h20.2.2.1
  have : Group.IsPerfect G := Group.isPerfect_def.2 hd.setting.commutator_eq_top
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨S, S ⊓ H0 d z₀, d.t, h26 S hS⟩

end Final

end CFSG.LocalAnalysis.EvenBN.Tits.N
