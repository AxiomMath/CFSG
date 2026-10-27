module

public import CFSG.CGT.PushingUpLit.LIT.A4.Final
public import CFSG.CGT.PushingUpLit.LIT.A4.L35Final

public section

namespace CFSG.CGT.PushingUpLit.A4


theorem threeConjExcluded : ThreeConjExcluded := fun _ _ _ _ _ c h => three_conj_false c h

theorem a4BlockNormalThree_holds : A4BlockNormalThree :=
  a4BlockNormalThree_of_threeExcl threeConjExcluded

end CFSG.CGT.PushingUpLit.A4
