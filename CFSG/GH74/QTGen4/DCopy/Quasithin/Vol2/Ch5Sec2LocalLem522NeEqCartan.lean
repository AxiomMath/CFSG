module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartan

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_2_2_eq_cartan_rank2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → L₂ < oTwoUpper H → LieModel (O2Q L₂) .PSL 2 2 2 →
    quasithinIsCComponent (oTwoUpper H) H → ¬ IsBenderAny (O2Q (oTwoUpper H)) →
    ∀ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
      quasithinIsCComponent L₂ P →
      IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧
        Lin2.IsHallTwoPrimeOf (B ⊓ L₂) (L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup G) : Set G))

theorem stmt5_2_2_eq_cartan_of_F4 (h510 : Stmt5_1_10_F4) (h38 : Vol2Native.A38ForSQTKCat)
    (hres : Stmt5_2_2_eq_cartan_rank2_F4) : Stmt5_2_2_eq_cartan_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hL₂K hL4
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, rfl, P, hP, hL₂P⟩
  ·
    obtain ⟨-, -, hBorel, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
    rw [hyp.toHyp5_1_8.borel_eq hBorel] at hBH
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hyp.hStar.1.2 hTH hK₁ hKeq hL₂K
    exact tc.elemAbelian_nine hK₁ hTH hL4 hBH
  · exact hres G T M L V H B D L₂ Dp n p hyp hL₂K hL4 hK₁ hnb P hP hL₂P

end CFSG.Quasithin.H13
