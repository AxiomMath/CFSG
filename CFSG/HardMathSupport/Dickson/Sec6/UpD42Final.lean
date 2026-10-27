module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Spor
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Odd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6


theorem upD42Statement_of_certificates : UpD42Statement :=
  upD42Statement_of_leaves upD42SporLeaf_holds upD42OddLeaf_holds upD42Chev2Leaf_of_certificates

end CFSG.HardMathSupport.Dickson.Sec6

end
