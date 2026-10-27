module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_14_one_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 →
      quasithinIsMaximalLocal T (oTwoUpper H) ∧ ¬ quasithinIsFaithfulLocal T (oTwoUpper H)

@[expose] def Stmt5_1_14_four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → Concl5_1_14_four T L V B D n

theorem stmt5_1_14_first_of_F4 (h331 : Stmt3_3_1_F4) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1 : Stmt5_1_14_one_F4) : Stmt5_1_14_first_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨hmax, hnf⟩ := h1 G T M L V H B D n hyp hN hV hK
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hHeq : H = oTwoUpper H ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hcc : conjClosure (oTwoUpper H) T = oTwoUpper H := by
    apply le_antisymm _ (le_conjClosure _ T)
    exact conjClosure_le fun t ht z hz =>
      (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz

  have hU : IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) := by
    have := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow hmax
    rwa [hcc, ← hHeq] at this

  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  have hInH : InH (oTwoUpper H ⊔ T) H := ⟨hHeq.symm.le, hH.1.2⟩
  have htfae := lemma_1_2_10_of_maximal h.qtke h.simple h.nonabelian h36 h37 h39 h.sylow hmax hInH
  have hno : ¬ ∃ W, IsTwoReducedIn H W ∧ ⁅W, oTwoUpper H⁆ ≠ ⊥ := fun hW =>
    hnf ((htfae.out 1 2).mpr hW)
  have hcharH : CharTwo H := charTwo_of_inH' h.qtke h.sylow hH.1
  have hVZ : IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H) := by
    have := isTwoReducedIn_conjClosure H S (hS ▸ hH.1.1) hcharH (Z := quasithinOmegaOneCenter T)
      (by rw [hS])
    exact this
  have hKZ : ⁅conjClosure (quasithinOmegaOneCenter T) H, oTwoUpper H⁆ = ⊥ := by
    by_contra hne
    exact hno ⟨_, hVZ, hne⟩
  have hZT : quasithinOmegaOneCenter T ≤ T := quasithinOmegaOneCenter_le_self T
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) := by
    rw [hHeq]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hKC : oTwoUpper H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKZ
      rw [Subgroup.le_centralizer_iff] at this
      exact this.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H)))
    have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwc := quasithinOmegaOneCenter_le_inf T hw
      exact (Subgroup.mem_centralizer_iff.mp hwc.2 t ht).symm
    have hx' : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      sup_le hKC hTC hx
    exact (Subgroup.mem_centralizer_iff.mp hx' z hz).symm
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZC
  have hcent : ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    intro z hz hz1
    refine centralizer_le_of_isUniqueM hU h.sylow.1 (hZT hz) hz1 ?_
    intro x hx
    exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  refine ⟨⟨hmax, hU, hnf⟩, ⟨hZH, hcent⟩, ?_⟩

  rw [eq_bot_iff]
  intro z hz
  by_contra hz1
  rw [Subgroup.mem_bot] at hz1
  obtain ⟨hzZ, hzL⟩ := hz
  have hLTz : L ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := by
    apply sup_le
    · intro l hl
      exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp hzL l hl).symm
    · intro t ht
      have hzc := quasithinOmegaOneCenter_le_inf T hzZ
      exact mem_centralizer_singleton_of (Subgroup.mem_centralizer_iff.mp hzc.2 t ht).symm
  have hLTK : L ⊔ T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hLTz.trans (hcent z hzZ hz1)
  have hMeq : Subgroup.normalizer (oTwoUpper H : Set G) = M :=
    (h.isUniqueM_F4 h331).2 _ ⟨hU.1.1, hLTK⟩
  exact hH.2.1 (hMeq ▸ hU.1.2)

theorem stmt5_1_14_of_F4 (hfirst : Stmt5_1_14_first_F4) (h4 : Stmt5_1_14_four_F4) (h5116 : Stmt5_1_16_F4) :
    Stmt5_1_14_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  obtain ⟨h1, h2, h3⟩ := hfirst G T M L V H B D n hyp hN hV hK
  have hc4 := h4 G T M L V H B D n hyp hN hV hK
  obtain ⟨h3', hsolv⟩ := h5116 G T M L V H B D n hyp hN hV hK
  have hDK : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [hc4.2.2]
    exact (hN.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H)
  refine ⟨h1, h2, h3, hc4, ?_, h3'⟩
  by_contra hns
  exact (hsolv hns).2.2 hDK

end CFSG.Quasithin.H13
