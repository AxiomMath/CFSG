module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_four_ZK_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
      ¬ oTwoUpper H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Stmt5_1_13_four_nA5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      ⁅V', thompsonJ T⁆ ≠ ⊥ → n = 2 → IsCommCentralSplit L T V' → IsBarS5 L T V' →
      IsS5ModCh5 L T ⁅V', L⁆ → False

@[expose] def Stmt5_1_13_four_CZ_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    L = ⁅L, thompsonJ T⁆ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) =
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) ∧
        (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (conjClosure Kh₁ T : Set G) = ⊥ →
          quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥)

theorem stmt5_1_13_four_nat_of_F4 (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (h512 : Stmt5_1_2_F4) (h5172 : Stmt5_1_7_two_F4) (hZK : Stmt5_1_13_four_ZK_F4)
    (hA5 : Stmt5_1_13_four_nA5_F4) (hCZ : Stmt5_1_13_four_CZ_F4) : Stmt5_1_13_four_nat_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1

  have hTLT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hchar : CharTwo (L ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, h.maximal.1.2.2.2⟩
  obtain ⟨-, -, hZred⟩ := conjClosure_isTwoReducedIn_of_charTwo hTLT hchar le_rfl
  have hred := A4.isTwoReducedIn_twoReducedJoin (L ⊔ T)
  have hZV : quasithinOmegaOneCenter T ≤ twoReducedJoin (L ⊔ T) :=
    (le_conjClosure _ _).trans (A4.le_twoReducedJoin hZred)
  have hVL : ⁅twoReducedJoin (L ⊔ T), L⁆ ≠ ⊥ :=
    ((lemma_1_2_10_of_maximal h.qtke h.simple h.nonabelian h36 h37 h39 h.sylow h.maximal
      ⟨le_rfl, h.maximal.1.2.2.2⟩).out 1 3).mp h.faithful
  have hmod : IsCh5Module T L (twoReducedJoin (L ⊔ T)) :=
    ⟨hred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hred).2, hVL⟩

  have hZK' := hZK G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro hb
    apply hZK'
    have h1 : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    exact (oTwoUpper_le H).trans (Subgroup.le_centralizer_iff.mp h1)
  obtain ⟨hLJ, -, -⟩ :=
    h5172 G T M L (twoReducedJoin (L ⊔ T)) H n h hmod m.hyp.hStar hZH

  rcases h512 G T M L (twoReducedJoin (L ⊔ T)) n h hmod with
    ⟨hJC, -⟩ | ⟨-, hnat⟩ | ⟨hJV, hn2, hsplit, hS5, hmodS5⟩
  ·
    exfalso
    apply hVL
    have hJC' : ⁅L, thompsonJ T⁆ ≤
        Subgroup.centralizer ((twoReducedJoin (L ⊔ T) : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have hlN := B6.le_normalizer_centralizer hred.2.1 (Subgroup.mem_sup_left hl)
      have hj' : j ∈ Subgroup.centralizer
          ((twoReducedJoin (L ⊔ T) : Subgroup G) : Set G) := (hJC hj).2
      have h1 : l * j * l⁻¹ ∈ Subgroup.centralizer
          ((twoReducedJoin (L ⊔ T) : Subgroup G) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hlN j).mp hj'
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hj')
    have hLC := hLJ.le.trans hJC'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hLC
  · obtain ⟨h1, h2⟩ := hCZ G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ _ hmod hZV hnat
    exact ⟨h1, h2, _, hmod, hZV, hnat⟩
  · exact (hA5 G T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ _ hmod hZV hJV hn2 hsplit hS5
      hmodS5).elim

end CFSG.Quasithin.H13
