module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigTh
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Sporadic.Bridge.ThSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

theorem elemAbelianLt_J_Th :
    CFSG.QuasithinUnique.Lin2.RankCert.ElemAbelianLt J (2 ^ 12) := by
  intro E hE
  have h := card_mul_le_of_elemAbelian_of_centralizer (G := ↥J) (a := a) (Q := Max3.Q)
    (M := Max3.M) (w := 4) (e := 15) (m := 2835) all_involutions_conjugate
    (Kernel.centralizer_a_eq_M th_kernel_facts).le isExtraspecialPGroup_Q
    (card_Q.trans (by norm_num)) Q_le_M M_le_normalizer_Q (card_M.trans (by norm_num))
    (by decide) (by norm_num) hE
  omega

theorem not_commute_of_order_thirteen_Th
    (t z : J) (ht : orderOf t = 2) (hz : orderOf z = 13) :
    t * z ≠ z * t :=
  not_commute_of_centralizer_le (a := a) (M := Max3.M) (p := 13) all_involutions_conjugate
    (Kernel.centralizer_a_eq_M th_kernel_facts).le
    (by rw [card_M]; norm_num) t z ht hz

theorem row_Th_13 :
    KFactSporLocalRow .Th 13 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have h12 : orderOf (2 : ZMod 13) = 12 :=
    orderOf_two_zmod_eq 13 12 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank (s := .Th) (p := 13) ↥J ?_ ?_ ?_
  · exact ⟨thEquivJ.symm.trans b⟩
  · intro t z ht hz
    exact not_commute_of_order_thirteen_Th t z ht hz
  · rw [h12]
    exact elemAbelianLt_J_Th

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
