module

public import CFSG.CGT.PushingUpLit.CGT6.EmbSix
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6X.OmegaThree

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem aschbacherEmbeddingK_of_endgames (h4End : Emb4End) (h5End : Emb5End) :
    AschbacherEmbeddingK :=
  aschbacherEmbeddingK_of_end CFSG.CGT.PushingUpLit.CGT6X.omega4OrderThree_holds o2Step4_holds
    commStep4_holds o2Step5_holds commStep5_holds h4End h5End

theorem aschbacherEmbeddingK_of_stages (h2 : Stage2Out) (h3 : EndFour) (h5End : Emb5End) :
    AschbacherEmbeddingK :=
  aschbacherEmbeddingK_of_endgames (emb4End_of_stages h2 h3) h5End

end CFSG.CGT.PushingUpLit.CGT6
