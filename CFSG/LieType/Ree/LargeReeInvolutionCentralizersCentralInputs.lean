module

public import CFSG.LieType.Ree.FixedWeylStructureData

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

abbrev centralRoot44 : Fin F4.tag.rank → ℤ := ![1, 2, 3, 2]

abbrev centralRoot47 : Fin F4.tag.rank → ℤ := ![2, 3, 4, 2]

abbrev centralWeylImage (k : Fin F4.fixedWeylOrder) (α : Fin F4.tag.rank → ℤ) :
    Fin F4.tag.rank → ℤ :=
  ((F4.fixedRelWord k).flatMap F4.fixedOrbitWord).foldr (reflect F4.tag) α

abbrev centralRootE1 : Fin F4.tag.rank → ℤ := ![1, 0, 0, 0]

abbrev centralRootE4 : Fin F4.tag.rank → ℤ := ![0, 0, 0, 1]

abbrev centralRootZE1 : Fin F4.tag.rank → ℤ := ![1, 2, 2, 0]

abbrev centralRootZE4 : Fin F4.tag.rank → ℤ := ![0, 1, 2, 1]

end CFSG.LieType.Ree.LargeReeInvolution
