module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockBC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BlockD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_bc_hat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    C126Third H T → Nat.card T ≤ 2 ^ 7

@[expose] def Stmt5_1_13_bc_false_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n → Nat.card T ≤ 2 ^ 7 → False

theorem stmt5_1_13_four_block_bc_of_F4 (hhat : Stmt5_1_13_bc_hat_F4) (horder : Stmt5_1_13_bc_order)
    (hfalse : Stmt5_1_13_bc_false_F4) : Stmt5_1_13_four_block_bc_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat hdich
  have hT7 : ¬ Nat.card T ≤ 2 ^ 7 :=
    hfalse G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat

  have hnK : ¬ C126Third H T := fun hKb =>
    hT7 (hhat G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK hKb)
  refine ⟨hnK, ?_⟩

  have hL : C126Third (L ⊔ T) T := hdich.resolve_right hnK
  by_contra hn
  have hn2 : n = 2 := by
    have := m.hyp.toHyp5_0_1.two_le
    omega
  exact hT7 (horder G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat hL hn2)

end CFSG.Quasithin.H13
