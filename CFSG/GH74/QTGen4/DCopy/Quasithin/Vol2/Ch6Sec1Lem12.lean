module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_12_F4 (h331 : Stmt3_3_1_F4) (h6110 : Stmt6_1_10_F4) : Stmt6_1_12_F4 := by
  intro G _ _ T M L V n h
  have hV := h.toHyp611.isElemAbelian
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV =>
    ((h6110 G T M L V n h).2.1 hV).1

  have hkey : ∀ i : ℕ, i + 2 ≤ n → wClos V i T ≤ ch6S T L V := by
    intro i hi
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    exact h.le_S_of_le_conj hs hAg hAT (by rw [hm]; exact hi)
  refine ⟨?_, fun hn => ?_, hkey 0 (by have := h.two_le; omega)⟩
  ·
    obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
    obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
    have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
    rw [← hMeq] at hH
    have hTH : T ≤ H := hH.1.1
    have hSH : IsSylowIn 2 T H :=
      E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
        hTH le_top
    have h319 := e3_19 hV hSH (i := 0) (h.nParam_eq_one H hH)
      (by rw [hs hV]; have := h.two_le; omega)
    by_contra hcon
    push Not at hcon
    obtain ⟨hW, hC⟩ := hcon
    apply hH.2.1
    rw [← h319]
    exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hW)
  ·
    have hW1 := hkey 1 (by omega)
    refine le_inf (h.ZS_le.trans h.toHyp611.le_T) fun z hz => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hW1 hw).2 z hz).symm

end CFSG.Quasithin.H13
