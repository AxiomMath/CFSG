module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Block

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_four_A7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7))

@[expose] def Stmt5_1_13_four_nat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) =
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) ∧
        (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) = ⊥ →
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥) ∧
        ∃ V' : Subgroup G, IsCh5Module T L V' ∧ quasithinOmegaOneCenter T ≤ V' ∧
          IsNatQuotCh5 L V' n

@[expose] def Stmt5_1_13_four_block_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      2 < n ∧ ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧
        oTwoUpper H ⊔ T ≤ Subgroup.normalizer (C : Set G) ∧
        D ⊔ T ≤ Subgroup.normalizer (C : Set G)

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem inf_centralizer_eq_bot_of_eq_F4 (h432 : Stmt4_3_2_F4) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) =
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G)) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  obtain ⟨huniq, -⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
    h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
  by_contra hne
  have hY2 : IsPGroup 2 ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) :=
    h.sylow.1.to_le (inf_le_left.trans (quasithinOmegaOneCenter_le_self T))
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :=
    ⟨_, hne, hY2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLY : L ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine le_trans (fun l hl => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 l hl).symm

  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHY : H ≤ Subgroup.normalizer
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTH]
    refine sup_le (fun x hx => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hCZ] at hy
      exact (Subgroup.mem_centralizer_iff.mp hy.2 x (m.lt.le hx)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hy.1).2 t ht).symm
  have hM'eq : M' = M := huniq M' hM' (hLY.trans hle)
  exact m.hyp.hStar.2.1 (hM'eq ▸ hHY.trans hle)

end Main513

theorem stmt5_1_13_four_be_of_F4 (h432 : Stmt4_3_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hgen : FactA7Gen) (hA7 : Stmt5_1_13_four_A7_F4)
    (hnat : Stmt5_1_13_four_nat_F4) (hblk : Stmt5_1_13_four_block_F4) : Stmt5_1_13_four_be_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  have hA := hA7 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  obtain ⟨hCZ, hCK, V', hV', hZV', hnat'⟩ := hnat G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA
  have hCZL := m.inf_centralizer_eq_bot_of_eq_F4 h432 hCZ
  obtain ⟨hn, C, hC1, hC2, hKC, hDC⟩ := hblk G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hCZL
    (hCK (hCZ.symm.trans hCZL)) V' hV' hZV' hnat'
  exact ⟨hn, m.le_normalizer_hat_of h37 h38 h39 hgen ty hmax hA hC1 hC2 hKC hDC, V', hV', hnat'⟩

end CFSG.Quasithin.H13
