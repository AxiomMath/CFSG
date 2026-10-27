module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6OrthC27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtCh6P778Cent
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6OrthNotNat
public import CFSG.Quasithin.EmptyFaithful.T1515Der4

public section

namespace CFSG.Quasithin.H13

section CaseAi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix

theorem lem614OrthFour_ofC_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h513 : Stmt5_1_3_F4) (h5172 : Stmt5_1_7_two_F4) (hH11 : Ch6InH11) (hE610 : Ch6InE610Four)
    (hC27 : ∀ (G' : Type) [Group G'] [CFSG.GH74.QTGen4.Finite4 G'], ASC27Statement_F4 G')
    (hP121 : CFSG.QuasithinUnique.Id2519.Prop121Three)
    (hRes : Res614EndGame_F4) : Lem614OrthFour_F4 := by
  intro G _ _ T M L V h horth
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVΩ := h.omegaOne_le_of_orth_ch6_F4 h512 h513 horth (by norm_num)
  have hr := h.one_lt_rParam_orth_ch6_F4 h432 hH11 hE610 horth hVΩ

  obtain ⟨hVL, hVC⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth (by norm_num)
  have hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rcases ((stmt6_1_2_F4 h512 h513) G T M L V 4 h).2 with hnat | ⟨-, -, hJN, -⟩
    · exact (horth.false_of_isNatQuot_ch6 hVL.symm.le hVC hnat).elim
    · exact hJN

  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, ⟨H₀, hH₀⟩, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  rw [← hMeq] at hH₀
  set Z := quasithinOmegaOneCenter T with hZdef
  have hH₀Z := h.le_centralizer_of_isHStar_ch6_F4 h5172 hJN hH₀

  have hZT : Z ≤ T ⊓ Subgroup.centralizer (T : Set G) := quasithinOmegaOneCenter_le_inf T
  have hZ2 : IsPGroup 2 Z := h.sylow.1.to_le (hZT.trans inf_le_left)
  have hZZ : Z ≤ Subgroup.centralizer (Z : Set G) :=
    fun z hz => Subgroup.centralizer_le (hZT.trans inf_le_left) (hZT hz).2
  have hZ1 : Z ≠ ⊥ := fun h0 =>
    inf_omegaOneCenter_ne_bot h.sylow.1 h.isElemAbelian h.le_T h.T_le_normalizer h.ne_bot
      (by rw [← hZdef, h0, inf_bot_eq])
  have hCZ : pCoreOf 2 (Subgroup.centralizer (Z : Set G)) ≠ ⊥ := fun h0 => hZ1 (le_bot_iff.mp
    (h0 ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZZ
      (Subgroup.centralizer_le_normalizer _) hZ2))
  obtain ⟨M₁, hM₁, hCM₁⟩ := exists_inM_of_pCoreOf_ne_bot hCZ
  have hTC : T ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hZT.trans inf_le_right)
  have hTM₁ : T ≤ M₁ := hTC.trans hCM₁
  have hne : M₁ ≠ M := fun heq => hH₀.2.1 (hH₀Z.trans (hCM₁.trans heq.le))

  have hFstar := h.not_oTwoFstarIn_le_of_orth_ch6_F4 hC27 h432 horth hM₁ hTM₁ hne

  set X := xFiveCh6 T L with hXdef
  have hXL : X ≤ L := (xFiveCh6_le T L).trans inf_le_left
  have hXM₁ : X ≤ M₁ := (h.xFiveCh6_le_centralizer_ch6 horth hVΩ).trans hCM₁
  have hXT : X ⊔ T ≤ M₁ := sup_le hXM₁ hTM₁
  obtain ⟨hX5, hXn⟩ := h.relIndex_xFiveCh6_ch6 horth
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_xFiveCh6 h.toHyp5_0_1.T_le_normalizer

  have hO2F := h.oTwoFIn_le_ch6_F4 h432 hH11 horth hr hXT
  have hPM : pCoreOf 2 M₁ ≤ M :=
    (F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf hTM₁)).trans h.T_le
  obtain ⟨K₁, hK₁, hK₁q, hK₁M⟩ : ∃ K₁ : Subgroup G, K₁ ∈ cComp M₁ ∧
      CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∧ ¬ K₁ ≤ M := by
    by_contra hcon
    push Not at hcon
    exact hFstar (oTwoFstarIn_le_of_components1516 hPM hO2F fun K hK hq => hcon K hK hq)

  have : IsSimpleGroup G := h.simple
  have hq := CFSG.QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke
  have hXK₁ : X ≤ Subgroup.normalizer (K₁ : Set G) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact mem_normalizer_of_prop121_ch6 hP121 h.simple h.nonabelian hq
      (pCoreOf_ne_bot_of_isTwoLocal hM₁.1) hK₁ (hXM₁ (Subgroup.subset_closure hx))
      (hx.2 ▸ pow_orderOf_eq_one x)

  have hnot := h.not_le_normalizer_inf_ch6C_F4 h432 hH11 horth hr hM₁ hXT
    (le_of_mem_cComp hK₁) hK₁M
  have hXK₀ := le_of_not_le_normalizer_inf_ch6 (le_normalizer_conjClosure_ch6 hXK₁ hTX) hTX
    h.sylow.1 hX5 (xFiveCh6_eq_oTwoUpper T L) hnot
  exact hRes G T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ hK₁q hK₁M hXL hXM₁
    (xFiveCh6_eq_oTwoUpper T L) hX5 hXn hTX hXK₁ hXK₀ hnot

end CaseAi

end CFSG.Quasithin.H13
