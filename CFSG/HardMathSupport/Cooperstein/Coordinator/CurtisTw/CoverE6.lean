module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.ChevLD
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.MinE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.OfCentralCover
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isCentralCover_e6IsogenyT : IsCentralCover (Isogeny.e6IsogenyT K) 2 where
  surj := Isogeny.e6IsogenyT_surjective
  ker_le := (CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).le
  coprime := by
    have h1 : (Isogeny.e6IsogenyT K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) :=
      CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)
    rw [h1, (CentralExt.MinusculeClosed.card_center_e6 (k := K)).1]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 3 _) (by norm_num)

variable (K) in
@[expose] noncomputable def e6CoverData :
    CentralCoverData (chevDatumLD TwistTag.E6 K 2 e6LongestData) (Isogeny.e6IsogenyT K) 2 where
  cover := isCentralCover_e6IsogenyT
  nhatW := canonMin K
  map_nhatW w := Subtype.ext (e6Isogeny_canonMin w)
  nhatW_one := canonMin_one K
  nhatW_simple_mul w a h := by
    have h1 : (coxeterSystem TwistTag.E6.tag).length ((coxeterSystem TwistTag.E6.tag).simple a * w) =
        (coxeterSystem TwistTag.E6.tag).length ((coxeterSystem TwistTag.E6.tag).simple a) +
          (coxeterSystem TwistTag.E6.tag).length w := by
      rw [h, CoxeterSystem.length_simple, add_comm]
    exact canonMin_mul_of_length_eq' h1
  hcomm a ha b hb := by
    refine mul_comm_of_isogeny_mem_torusGroup ha hb

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
