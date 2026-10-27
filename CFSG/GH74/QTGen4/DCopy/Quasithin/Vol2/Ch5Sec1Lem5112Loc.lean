module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_12_loc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G →
    ∀ (S X K Kh : Subgroup G) (k : ℕ), 2 ≤ k → pCoreOf 2 X ≠ ⊥ → IsSylowTwoOf S X → K ≤ X →
      K ∈ lFamily S → S ≤ Subgroup.normalizer (K : Set G) → IsHatComp X K Kh → K < Kh →
      IsBenderCh5 k (O2Q K) →
        (SuzukiModel (O2Q K) 2 k ∧ Is2F4 k (O2Q Kh)) ∨
        (LieModel (O2Q K) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Kh)) ∨
        (LieModel (O2Q K) .PSL 2 2 2 ∧ ¬ IsLieTypeChar2 (O2Q Kh) ∧
          A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh))

end CFSG.Quasithin.H13
