module

public import CFSG.ClassicalInvolution.Q3.TL4D1ME8D
public import CFSG.ClassicalInvolution.Q3.TL4D1M64M
public import CFSG.ClassicalInvolution.Q3.TL4D1M29M

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem d1Facts : D1Facts where
  e8Normal := e8NormalFact
  e8Perfect := e8PerfectFact
  aeNormal := aeNormal
  aePerfect := aePerfect
  aeMembers := aeMembers
  e64 := e64_facts
  e29 := e29_facts

end CFSG.ClassicalInvolution.Q3.TL4
