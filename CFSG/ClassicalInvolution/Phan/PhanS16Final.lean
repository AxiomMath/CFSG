module

public import CFSG.ClassicalInvolution.Phan.PhanS15Close
public import CFSG.ClassicalInvolution.Phan.PhanS15Fin
public import CFSG.ClassicalInvolution.Phan.PhanS15Setup
public import CFSG.ClassicalInvolution.Phan.PhanS12Dict
import CFSG.ClassicalInvolution.Phan.PhanS13M3Main

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem phanB3StdDict : PhanB3StdDict p f := by
  intro hp2 hq hmod hK h2 C M E hgood hrange
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  let _ : Algebra (GaloisField p f) (GaloisField p (2 * f)) :=
    (Aniso.nonempty_algebra hF hK).some
  obtain ⟨D, ⟨S⟩⟩ := exists_setup hp2 hq hmod M E hgood hrange
  obtain ⟨c₂, hc⟩ := exists_c2 D S.hodd
  exact ⟨stdModel D S.h2K, hF, ⟨S.dict c₂ hc (planeBase S) (planeMove S)⟩⟩

theorem phanB3Std_ne_seven (h7 : p ^ f ≠ 7) : PhanB3StdSimplyTwoConnected p f :=
  phanB3Std_of_dict_ne_seven phanB3StdDict h7

theorem phanB3Std_final (h7 : Q7Residual) : PhanB3StdSimplyTwoConnected p f :=
  phanB3Std_of_dict_q7 phanB3StdDict h7

theorem phanB3Std_of_q7 (h7 : p ^ f = 7 → Q7Residual) : PhanB3StdSimplyTwoConnected p f := by
  by_cases h : p ^ f = 7
  · exact phanB3Std_final (h7 h)
  · exact phanB3Std_ne_seven h

end Final

end CFSG.ClassicalInvolution.PhanB3.S
