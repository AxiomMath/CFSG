module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Asm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Ord
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3U48
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Bender
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Covers
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Ree

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Holds


theorem I137C3.core3Parts_holds : I137C3.Core3Parts where
  small := fun _ _ _ _ _ h => I137C3.core3Group_of_card_lt (lt_of_lt_of_le h (by norm_num))
  sp48 := I137C3.Core3At.mono (fun _ h => Or.inl h) I137C3.core3At_ord
  sp62 := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inl h)) I137C3.core3At_ord
  d42 := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inl h))) I137C3.core3At_ord
  u52 := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) I137C3.core3At_ord
  u62 := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    I137C3.core3At_ord
  td42 := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    I137C3.core3At_ord
  tits := I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    I137C3.core3At_ord
  g28 := I137C3.core3At_G2eight
  u48 := I137C3.core3At_U4eight
  ree8 := I137C3.core3At_reeF48
  l2 := I137C3.core3At_L2two
  u3 := I137C3.core3At_U3two
  l3 := I137C3.core3At_L3
  sl3 := I137C3.core3Group_of_SL3cover
  su3 := fun _ _ _ _ ⟨_, hn, _, h⟩ => I137C3.core3Group_of_SU3cover hn h
  su6 := fun Q _ _ _ h => I137C3.core3Group_of_SU6cover
    (I137C3.Core3At.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      I137C3.core3At_ord) Q h

theorem i137LieCore3_holds : I137LieCore3 :=
  I137C3.i137LieCore3_of_parts I137C3.core3Parts_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA

end
