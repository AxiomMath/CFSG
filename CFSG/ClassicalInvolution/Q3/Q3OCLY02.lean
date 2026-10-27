module

public import CFSG.ClassicalInvolution.Q3.Q3OCLY01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23E01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y06
public import CFSG.ClassicalInvolution.Q3.Q3T7S23DY01
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerOdd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77


section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem oddCore_exactLayer_u_eq_bot
    [IsSimpleGroup G] (h : Q3T8.Asc77.Hyp23b Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
      Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤)
    (hE : Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1)) (hex : ExactMembers Ω)
    (hOE : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥) :
    classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥ := by
  classical
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := Q3T8.Asc77.Hyp23.setting h.std
  have hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g := Q3T8.Asc77.Hyp23b.data h
  have hπ : piSign 3 1 = false := by decide
  have hE0 : Q3T8.Asc77.LayerOrthType Ω e 6 false := by simpa [hπ] using hE
  obtain ⟨-, -, -, hgenE, -, -, -, -⟩ := Q3T8.Asc77.B3C.eSideU3 hs hd hα.1 hOE hE0
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨-, -, -, -, -, hJt, hJ't, -⟩ := Q3T8.Asc77.T7L.exists_uFrame hs hd
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJ't).2
  have hYu : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  have hEle : Q3T8.Asc77.ExactLayer.exactLayer Ω e ≤
      K ⊔ K' ⊔ Subgroup.centralizer ({u} : Set G) :=
    hgenE.trans (sup_le (sup_le (hJ'u.trans le_sup_right) (le_sup_left.trans le_sup_left))
      (hJu.trans le_sup_right))
  have hGen : K ⊔ K' ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hα.2]
    exact sup_le hEle (hYu.trans le_sup_right)
  have hV : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K ∨ M = K' := by
    intro M hM hMz
    have hmem : M ∈ twinSet Ω K := ⟨hM, z, hs.hz, hMz⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hMK : IsClassicalMember3 K z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hKΩ hs.hz).toQ3 (by norm_num)
  have hMK' : IsClassicalMember3 K' z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hK'Ω hzK').toQ3 (by norm_num)
  have hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥ :=
    oddCore_centralizer_eq_bot_of_twins hΩ.conjInvariant hex hKΩ hK'Ω hs.hz hzK' hs.hne.symm hV
      (hR.1 haR) (hR'.1 hbR') haa hbb hu hd.hu1 (Q3T7S23.twins_commute_of_exact hs hex) hMK hMK'
      hα.1 hGen
  exact Q3T8.Asc77.ExactLayer.oddCore_exactLayer_eq_bot_of_centralizer hΩ.conjInvariant hO

end Layer

theorem oddCoreLayer23Sp3_proved :
    Q3T7S23.OddCoreLayer23Sp3 := by
  intro G _ _ _ Ω K K' W z u e g h hα hE _ hex hOE
  exact oddCore_exactLayer_u_eq_bot h hα hE hex hOE

theorem oddCoreLayer23Plus3_proved :
    Q3T7S23.OddCoreLayer23Plus3 := by
  intro G _ _ _ Ω K K' W z u e g h hα hE _ hex hOE
  exact oddCore_exactLayer_u_eq_bot h hα hE hex hOE

end CFSG.ClassicalInvolution.Q3.Q3OCL
