module

public import CFSG.ClassicalInvolution.AschTight.S19LFix
public import CFSG.ClassicalInvolution.AschTight.S19LDer
public import CFSG.ClassicalInvolution.AschTight.S19LQuat
public import CFSG.ClassicalInvolution.AschTight.S1911SecF
public import CFSG.ClassicalInvolution.AschTight.S19QTMain
public import CFSG.ClassicalInvolution.AschTight.Hall196Rec
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3
public import CFSG.ClassicalInvolution.AschTight.S19LDih
public import CFSG.ClassicalInvolution.AschTight.S19LSwap

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem false_of_sectionType_L3 (h11b : C19_11bTmp p f) (hB3 : GoldschmidtB3Tmp)
    (hFG2 : S19Q.FactFG2) (hd : Sec19Data p f K z S W) (h9 : p ^ f ≠ 9) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) {e₀ : ℕ}
    (hsec : SectionLieType p e₀ (S1911.conjFamily (S1911.perfectCoreIn K a))
        (S1911.conjGen (S1911.perfectCoreIn K a)) .PSL 3 ∨
      SectionLieType p e₀ (S1911.conjFamily (S1911.perfectCoreIn K a))
        (S1911.conjGen (S1911.perfectCoreIn K a)) .PSU 3) : False := by
  obtain ⟨e₁, -, h5, hzA, hmem, hΩ, hDE, -, -, -⟩ :=
    S1911.sectionData_fieldInvolution hd h9 haS ha2 haX
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd
  have ef := S1911.etaYForm p f G K z S W L t V hdT
  have hstar := S1911.c19_11a_of p f h11b
  by_cases hPC : (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z
  · exact S19Q.c19_14_of_c19_11b p f h11b hB3 G K z S W hd (sup_eq_of_le hdT hPC)
  obtain ⟨q, hqP, hqC, hqt, hqinv, hq2, hcoset, hcardP, hquat⟩ := exists_swap hstar hdT hPC
  obtain ⟨u, hU, h8, -, -⟩ := exists_gen_conj_eq hdT haS ha2 haX
  have hC8 : 8 ≤ Nat.card ↥(W ⊓ sec19Y K z) := by
    rw [ef.card, ← S1911.card_inf_eq_card hdT, ← hU, Nat.card_zpowers]
    exact h8
  rcases hq2 with hq2 | hq2
  · exact false_of_dihedral h11b hdT hqP hqC hqinv hq2 hcoset
  · rcases Hall196.isSL2ModOdd_sec19Y p f hstar hd (hquat hq2) with hY | ⟨m', hY2⟩
    · exact false_of_quat h11b hdT hY hqP hqt hqinv hq2 hcoset hC8
    · have h16 : 16 ≤ Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) := by rw [hcardP]; omega
      obtain ⟨H, y, hH, hy, hodd⟩ := exists_mem_derived hdT haS ha2 haX hzA hY2 h16
      exact false_of_mem_derived hFG2 hd h5 hzA hmem hΩ hDE hsec hH hy hodd

variable (p f) in
theorem c19_16FusL3Graph_of' (h11b : C19_11bTmp p f) (hFG2 : S19Q.FactFG2) :
    S1911.C19_16FusL3GraphTmp p f := by
  intro G _ _ _ K z S W hd h9 a haS ha2 haX e₀ hsec _ _ _
  exact (false_of_sectionType_L3 h11b goldschmidtB3Tmp_holds hFG2 hd h9 haS ha2 haX hsec).elim

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
