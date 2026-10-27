module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution

theorem noWeakClassical3_McLP (hP : Nat.card McLProof.P = 898128000) :
    NoWeakClassical3 McLProof.P := by
  have hS2 : IsPGroup 2 McLProof.S :=
    IsPGroup.of_card (n := 7) (by rw [McLProof.card_S]; norm_num)
  exact noWeakClassical3_of_single_class_quasisimple McLProof.P McLProof.S McLProof.K hS2
    (McLProof.S_index_odd hP) McLProof.pa_mem McLProof.cover_S (McLProof.centralizerIn_P hP)
    McLProof.K_quasisimple.1 McLProof.card_center_K
    (by rw [McLProof.card_K hP]; norm_num)

theorem noWeakClassical3_McL : NoWeakClassical3 CFSG.Blueprint.NativeSporadic.McL :=
  NoWeakClassical3.of_mulEquiv McLProof.mclEquivP (noWeakClassical3_McLP McLProof.card_P)

end CFSG.ClassicalInvolution.Q3
