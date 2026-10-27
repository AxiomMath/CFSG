module

public import CFSG.CGT.PushingUpLit.BHS6.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem six_three {G T E Q : Subgroup Γ} (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hQG : Q ≤ G) (hQ2 : IsPGroup 2 Q) (hQn : baum T ⊔ E ≤ Subgroup.normalizer (Q : Set Γ)) :
    Q ≤ Subgroup.normalizer (E : Set Γ) := by
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hBle : baum T ≤ T := inf_le_left
  have hBG : baum T ≤ G := hBle.trans hT'.1
  have hB2 : IsPGroup 2 (baum T) := hT'.2.1.to_le hBle
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hQB : baum T ≤ Subgroup.normalizer (Q : Set Γ) := le_sup_left.trans hQn
  have hQE : E ≤ Subgroup.normalizer (Q : Set Γ) := le_sup_right.trans hQn
  have hS2 : IsPGroup 2 ↥(baum T ⊔ Q) := hB2.to_sup_of_normal_right' hQ2 hQB
  have hSG : baum T ⊔ Q ≤ G := sup_le hBG hQG
  have hbS : baum (baum T ⊔ Q) = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT' hS2 hSG le_sup_left
  have hQb : Q ≤ Subgroup.normalizer (baum T : Set Γ) := by
    have h := normalizer_le_normalizer_baum (baum T ⊔ Q)
    rw [hbS] at h
    exact (le_sup_right : Q ≤ baum T ⊔ Q).trans (Subgroup.le_normalizer.trans h)
  have hKQ := le_normalizer_iSup_conj hQE hQb
  rw [iSup_conj_eq_sup_of_commutator_eq hE.commutator] at hKQ
  have hres : opResidual 2 (E ⊔ baum T) = E :=
    opResidual_sup_eq (opResidual_eq_of_isBTBlock hE) hB2 hBE
  intro q hq
  have h1 : conjSub q (E ⊔ baum T) = E ⊔ baum T := conjSub_eq_of_mem_normalizer (hKQ hq)
  have h2 : conjSub q E = E := by
    have h := opResidual_conjSub 2 q (E ⊔ baum T)
    rw [h1, hres] at h
    exact h.symm
  exact mem_normalizer_of_conjSub_eq h2

end CFSG.CGT.PushingUpLit.BHS6
