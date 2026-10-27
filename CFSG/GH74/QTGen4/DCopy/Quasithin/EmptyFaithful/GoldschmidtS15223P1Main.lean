module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Fin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Norm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Canon
public import CFSG.Quasithin.EmptyFaithful.S152U18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem p1_of_F4 {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}
    (hOm : Om4FactsStatement) (h8 : StageLemma15208_F4) (hNot : StageNotation15209_F4)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hB₀ : IsB0 T Mc M B₀) (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I)
    (hL12 : ∀ B ∈ sigmaPrime T H (V154 T Mc M), He12.Lemma15212ConclW T Mc M H B)
    {X : Subgroup G} (hX3 : GenByOrderThree X) (hXI : X ≤ I)
    (hIX : I ≤ Subgroup.normalizer (X : Set G))
    (hXMc : X ≤ Mc) (hXK : ¬ X ≤ oTwoUpper H) : quasithinV2 X = ⊥ := by
  obtain ⟨B, hB⟩ := hD.hN.sigmaPrime_nonempty
  have h12 := hL12 B hB
  have hX : X = oPrimeResidualOf 3 X := hX3.eq_oPrimeResidualOf
  set Kc := conjClosure (oTwoUpper H) Mc with hKcdef
  by_cases hKK : Kc = oTwoUpper H
  ·
    exfalso
    refine hXK (hX3.trans ((Subgroup.closure_le _).mpr fun x hx => ?_))
    exact He12.mem_of_orderOf_three_F4 h8 hNot hs hH hKK (hXMc hx.1) hx.2
  have heq : Kc = oPrimeResidualOf 3 Mc := h12.eq_oThreePrime_of_ne hKK
  have hKcMc : Kc ≤ Mc := heq.le.trans oPrimeResidual_le
  have hXKc : X ≤ Kc := hX.le.trans ((oPrimeResidual_mono hXMc).trans heq.ge)
  have hKn : Mc ≤ Subgroup.normalizer (Kc : Set G) := le_normalizer_conjClosure (oTwoUpper H) Mc
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc

  have hQ2 : IsPGroup 2 (pCoreOf 2 Kc) := pCoreOf_isPGroup 2 Kc
  have hQN : Mc ≤ Subgroup.normalizer (pCoreOf 2 Kc : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 Kc)
  have hQT : pCoreOf 2 Kc ≤ T := by
    have hSylT : IsSylowTwoOf T (Kc ⊔ T) := isSylowTwoOf_of_le151 hs.qtfe.sylow le_sup_right
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Kc).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 Kc) (hTMc.trans hQN)) hQ2).trans ?_
    exact B6.pCoreOf_two_le_of_isSylowTwoOf hSylT
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 Kc : Set G) :=
    hXKc.trans (le_normalizer_pCoreOf 2 Kc)

  have hSyl : IsSylowTwoOf (sOf152 T Mc M B₀) I := isSylowTwoOf_S152 hs hH hB₀ hI hD hOm
  have hQX : pCoreOf 2 Kc ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_sylow_index_two hSyl S_le_T152 hD.h17.2.2 hQT hQ2 (hTMc.trans hQN) hXQ hXI
      hIX hX

  have hAB : ⁅X, pCoreOf 2 Kc⁆ ≤ Subgroup.centralizer (z2Of X : Set G) := by
    have h1 : ⁅X, pCoreOf 2 Kc⁆ ≤ X ⊓ pCoreOf 2 Kc := commutator_le_inf_of_normalizes hXQ hQX
    have h2 : X ⊓ pCoreOf 2 Kc ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (le_normalizer_inf_of_both Subgroup.le_normalizer hXQ) hQ2.to_inf_right
    exact (h1.trans h2).trans (pCoreOf_le_centralizer_z2Of X)

  have hMcM : InM T Mc := (hD.m_eq Mc).mpr (Or.inr rfl)
  have hcharMc : CharTwo Mc := by
    obtain ⟨S₂, hS₂⟩ := hs.qtfe.exists_sylow
    exact hs.qtfe.qtke.2.1 Mc hMcM.1.1 ⟨S₂, hS₂.le.trans hMcM.2⟩
  have hchar : CharTwo Kc :=
    CharTwo.of_normal hcharMc hKcMc ((Subgroup.normal_subgroupOf_iff_le_normalizer hKcMc).mpr hKn)

  by_contra hne
  have hnotc : ¬ X ≤ Subgroup.centralizer (z2Of X : Set G) := by
    intro hc
    apply hne
    rw [quasithinV2_eq_commutator, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  have hnfix : ¬ X ≤ Subgroup.centralizer
      ((z2Of X ⊓ Subgroup.centralizer (pCoreOf 2 Kc : Set G) : Subgroup G) : Set G) := by
    intro hfix
    refine hnotc (A4.thompson_axb (isPGroup_z2Of X) (eq_oTwoUpper_of_eq_oPrimeResidual hX)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_z2Of X))
      (hQX.trans (normalizer_le_normalizer_z2Of X)) ?_ hAB hfix)
    intro b hb
    obtain ⟨k, hk⟩ := hQ2 ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have h1 : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨x, hxX, hxc⟩ := IsConcreteLE.not_le_iff_exists.mp hnfix
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ z2Of X ⊓ Subgroup.centralizer (pCoreOf 2 Kc : Set G),
      z * x ≠ x * z := by
    by_contra hall
    push Not at hall
    exact hxc (Subgroup.mem_centralizer_iff.mpr hall)
  obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz

  have hzP : z ∈ pCoreOf 2 Kc :=
    hchar ⟨hXKc (pCoreOf_le 2 X (z2Of_le_pCoreOf X hzV)), hzC⟩
  have hzZ : z ∈ z2Of Kc :=
    Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hzP, hzC⟩, z2Of_sq X z hzV⟩
  have hne' : ⁅z2Of Kc, Kc⁆ ≠ ⊥ := by
    intro h0
    have hmem : ⁅z, x⁆ ∈ ⁅z2Of Kc, Kc⁆ := Subgroup.commutator_mem_commutator hzZ (hXKc hxX)
    rw [h0, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply hzx
    have h1 : z * x * z⁻¹ = x := mul_inv_eq_one.mp (by simpa [mul_assoc] using hmem)
    calc z * x = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  rcases h12.cases with hKK' | hcases
  · exact absurd hKK' hKK
  · exact false_of_z2Of_commutator_ne_bot hs.qtfe hKcMc hKn hTMc hchar hcases hne'

end S15223

@[expose] def Reduction15223P1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → ∀ X : Subgroup G, S15223.GenByOrderThree X →
        X ≤ I → I ≤ Subgroup.normalizer (X : Set G) → X ≤ Mc → ¬ X ≤ oTwoUpper H →
          quasithinV2 X = ⊥

namespace S15223

theorem reduction15223P1_of_F4 (hOm : Om4FactsStatement) (h5 : StageLemma15205_F4)
    (h159 : StageLemma1519) (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4)
    (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4)
    (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) :
    Reduction15223P1_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI X hX hXI hIX hXMc hXK
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  exact p1_of_F4 hOm h8 hN hs hH hB₀ hI hD (fun B hB => h12 G T Mc M hs H hH B hB) hX hXI hIX hXMc hXK

end S15223

end CFSG.Quasithin
