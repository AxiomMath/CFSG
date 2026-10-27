module

public import CFSG.GH74.GLS.Prop27.Shapes
public import CFSG.GH74.E2.K0Simple
public import CFSG.GH74.GLS.Prop27.Unique
public import CFSG.GH74.GLS.Prop27.Balance

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.E2
  CFSG.Blueprint Assembly.LowTwoRank CFSG.Assembly.Dichotomy

variable {G : Type} [Group G] [Finite G]

theorem k0Shape_of_shapes7 {K : Type} [Group K] (h : Shapes7 K) : K0Shape K := by
  rcases h with ⟨-, h | h | h | h | h⟩ | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

theorem prop27TableFacts :
    Prop27TableFacts where
  sylow_rank_simple K _ _ h hc := exists_twoSubgroup_rank_two_of_K0Shape (k0Shape_of_shapes7 h) hc
  sylow_rank_cover K _ _ h hc := by
    rcases h with ⟨hbot, -⟩ | h | h
    · exact absurd hbot hc
    · obtain ⟨U, hU, hr⟩ := rank_ge4_of_shape2M12 h
      exact ⟨U, hU, by omega⟩
    · exact rank_ge3_of_shape2Sz8 h

theorem compData7_of_component (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hInC2 : InC2 ↥K) (hno : ¬ HasL2Model ↥K IsFM9) :
    CompData7 ↥K where
  quasi := hInC2.1
  pgroup := by
    have h := hInC2.2.1
    have : IsPGroup 2 ↥(center ↥K) := by
      rw [h]
      exact CFSG.pCore_isPGroup
    exact this
  not_excluded := hInC2.2.2.2
  gen4 := Gen4.subgroup K (gen4_centralizerBar hgen x)
  rank := by
    by_cases hxb : xbar x ∈ K
    · right
      intro hbot
      exact xbar_not_mem_of_center_eq_bot hx hbot hxb
    · left
      by_contra hcon
      exact not_rankCertified_three_of_xbar_not_mem hgen hx hxb
        (rankCertified_of_not_sectionalTwoRankLE hcon)
  no_fm9 := hno

theorem shapes7_bar
    (L : Prop27Leaves) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hInC2 : InC2 ↥K) (hno : ¬ HasL2Model ↥K IsFM9) :
    Shapes7 ↥K :=
  shapes7_of_component L.generic L.e2 (compData7_of_component hgen hx hInC2 hno) hInC2.2.2.1

theorem locBal2_of_shapes7 (L : Prop27LocalBalance) {K : Type} [Group K] [Finite K]
    (h : Shapes7 K) : LocBal2 (fun S _ => Nonempty (S ≃* (K ⧸ center K))) := by
  rcases h with ⟨hbot, h⟩ | ⟨-, -, hM⟩ | ⟨-, -, hS⟩
  · have e : K ≃* K ⧸ center K := mulEquivOfCenterBot hbot
    rcases h with h | h | h | h | h
    · intro X _ _ N hN ⟨e'⟩ hc
      exact L.L28 X N hN (lieModel_of_mulEquiv (e'.trans e.symm).symm h) hc
    · intro X _ _ N hN ⟨e'⟩ hc
      exact L.L33 X N hN (lieModel_of_mulEquiv (e'.trans e.symm).symm h) hc
    · intro X _ _ N hN ⟨e'⟩ hc
      exact L.U33 X N hN (lieModel_of_mulEquiv (e'.trans e.symm).symm h) hc
    · intro X _ _ N hN ⟨e'⟩ hc
      exact L.Sz8 X N hN (lieModel_of_mulEquiv (e'.trans e.symm).symm h) hc
    · intro X _ _ N hN ⟨e'⟩ hc
      exact L.M11 X N hN (isSporadic_of_mulEquiv (e'.trans e.symm).symm h) hc
  · intro X _ _ N hN ⟨e'⟩ hc
    exact L.M12 X N hN (isSporadic_of_mulEquiv e'.symm hM) hc
  · intro X _ _ N hN ⟨e'⟩ hc
    exact L.Sz8 X N hN (lieModel_of_mulEquiv e'.symm hS) hc

theorem oddCoreFree_bar
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9) {b : G} (hb : orderOf b = 2) :
    ∀ v : CentralizerBar b, orderOf v = 2 → involutionOddCore v = ⊥ := by
  have hshape : ∀ K : Subgroup (CentralizerBar b), IsComponent K → Shapes7 ↥K := fun K hK =>
    shapes7_bar L hgen hb (hL2 b hb K hK).1 (hL2 b hb K hK).2
  refine involutionOddCore_eq_bot_of_components (pPrimeCore_quotient_eq_bot _) ?_ ?_
  · intro K₁ K₂ h₁ h₂
    by_contra hne
    exact false_of_two_components7 prop27TableFacts (gen4_centralizerBar hgen b) (orderOf_xbar hb)
      (fun y => xbar_comm b y) h₁ h₂ hne (hshape K₁ h₁) (hshape K₂ h₂)
  · intro K hK
    have hs := hshape K hK
    have hpg : IsPGroup 2 ↥(center ↥K) := by
      have h := (hL2 b hb K hK).1.2.1
      have : IsPGroup 2 ↥(center ↥K) := by
        rw [h]
        exact CFSG.pCore_isPGroup
      exact this
    refine ⟨hpg, ?_, locBal2_of_shapes7 L.localBalance hs⟩
    rcases hs with ⟨hbot, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
    · rw [hbot, Subgroup.card_bot]
      norm_num
    · exact hc.le
    · exact hc.le

theorem involutionOddCore_inf_le_of_leaves
    (L : Prop27Leaves) (hgen : Gen4 G)
    (hL2 : ∀ x : G, orderOf x = 2 → ∀ K : Subgroup (CentralizerBar x), IsComponent K →
      InC2 ↥K ∧ ¬ HasL2Model ↥K IsFM9) {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) :
    involutionOddCore a ⊓ centralizer ({b} : Set G) ≤ involutionOddCore b :=
  involutionOddCore_inf_le_of_oddCoreFree ha hab (oddCoreFree_bar L hgen hL2 hb)

end CFSG.GH74.GLS.Prop27
