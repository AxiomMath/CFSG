module

public import CFSG.GF2Type.Smith1979.CharTwoModelSpec
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Stab
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Orbit
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Sub6

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

theorem e0Facts :
    E0Facts E0 inO378 inO1701 a0V w0 where
  cases := fun _ hv hq => (singular_cases hv hq).1
  B_sing := fun _ hv => ne_zero_of_inO378 hv
  B_inv := fun _ he _ hv => inO378_invariant (E0_le_M0 he) hv
  A_inv := fun _ he _ hv => inO1701_invariant (E0_le_M0 he) hv
  B_trans := fun _ hv => inO378_trans_E0 hv inO378_w0
  A_trans := fun _ hv => inO1701_trans_E0 hv inO1701_a0V
  w0_mem := inO378_w0
  a0_mem := inO1701_a0V
  stab_w0 := fun _ hP hn h2 => normal_two_subgroup_stab_E0_eq_bot hP hn h2
  sub6 := fun _ hdim _ hinv => sub6_E0 hdim hinv
  orbit := fun _ hv hf => orbitC_ncard hv hf

end CFSG.GF2Type.Smith1979.IdxFour
