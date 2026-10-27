module

public import CFSG.Quasithin.EmptyFaithful.S152L26
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

section Finite

variable [CFSG.GH74.QTGen4.Finite4 G]

variable {T Mc M : Subgroup G}

theorem stageLemma15226_of_F4 (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4)
    (h1 : StageLemma15226One_F4) : StageLemma15226_F4 := by
  intro G _ _ T Mc M hs
  obtain ⟨hV, hr, hsP⟩ := h1 G T Mc M hs
  obtain ⟨H₀, hH₀⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  obtain ⟨B₀, hB₀, -, -⟩ := (h13 G T Mc M hs H₀ hH₀).exists_B0
  obtain ⟨hV', -, ha⟩ := (h14 G T Mc M hs B₀ hB₀).params
  have hw : E3.wClos (V154 T Mc M) 0 T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    lemma_15_2_26_two hs.qtfe hs.mf hV hsP ha
  refine ⟨⟨⟨hV, hr, hsP⟩, hw⟩, fun H hH => ?_⟩
  obtain ⟨S, hS⟩ := hs.qtfe.exists_sylow
  have hQT : pCoreOf 2 H ≤ T := by
    have := pCoreOf_two_le_sylow H S (hS ▸ hH.1.1)
    rwa [hS] at this
  have hVe : IsElemAbelian 2 (V154 T Mc M) := hV
  have hVp : IsPGroup 2 (V154 T Mc M) := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  exact wClos_zero_le_centralizer hQT hVp hw

end Finite

end CFSG.Quasithin
