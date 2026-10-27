module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] public def Sx (R : Type) [Field R] (p q : ι) : Matrix ι ι R :=
  single p q 1 + single q p 1 + single p p 1

public theorem trans_mul_Sx {R : Type} [Field R] (p q : ι) (hpq : p ≠ q) :
    transvection p q (1 : R) * transvection q p 1 = 1 + Sx R p q := by
  unfold transvection Sx
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single_same, single_mul_single_of_ne,
    hpq, hpq.symm]
  abel

public theorem trace_Sx {R : Type} [Field R] (p q : ι) (hpq : p ≠ q) :
    trace (Sx R p q) = 1 := by
  simp [Sx, trace_add, trace_single_eq_of_ne, trace_single_eq_same, hpq, hpq.symm]

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg
