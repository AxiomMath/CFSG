module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch4Sec3Setup

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

@[expose] def Core432_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L : Subgroup G) (n : ℕ) (I H : Subgroup G),
    Setting432 G T M L n I H → False

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem theorem_4_3_2_F4 (hcore : Core432_F4) (h : Hyp5_0_1 G T M L n) : IsUniqueM L M := by
  by_contra hL
  obtain ⟨I, H, s⟩ := exists_setting432 h hL
  exact hcore G T M L n I H s

theorem theorem_4_3_17_F4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (hcore : Core432_F4)
    (h : Hyp5_0_1 G T M L n) {S : Subgroup G} (hST : S ≤ T) (hSL : IsSylowTwoOf (S ⊓ L) L) :
    Subgroup.normalizer (S : Set G) ≤ M := by
  have hU := theorem_4_3_2_F4 hcore h
  have hSM : S ≤ M := hST.trans h.T_le
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le hST
  obtain ⟨TH, hTH, -⟩ := exists_isSylowTwoOf_ge (le_inf hSM Subgroup.le_normalizer) hS2
  refine lemma_4_3_1 hR hC h hS2 hSM hTH hSL (isUniqueM_mono hU le_sup_left ?_)
  exact _root_.sup_le h.L_le (hTH.1.trans inf_le_left)

theorem stmt4_3_2_of_F4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (hcore : Core432_F4) :
    Stmt4_3_2_F4 := by
  intro G _ _ T M L hs hnab hK hT hM hTM hLmax hLf hLM hn hlie
  obtain ⟨n, hn2, hL2⟩ := hlie
  have h : Hyp5_0_1 G T M L n :=
    { simple := hs
      nonabelian := hnab
      qtke := hK
      sylow := hT
      maxTwoLocal := hM
      T_le := hTM
      maximal := hLmax
      faithful := hLf
      L_le := hLM
      normal := hn
      two_le := hn2
      lie := hL2 }
  have hU := theorem_4_3_2_F4 hcore h
  exact ⟨fun M' hM' hLM' => hU.2 M' ⟨hM', hLM'⟩,
    fun S hST hSL => theorem_4_3_17_F4 hR hC hcore h hST hSL⟩

end CFSG.Quasithin.H13.Ch4
