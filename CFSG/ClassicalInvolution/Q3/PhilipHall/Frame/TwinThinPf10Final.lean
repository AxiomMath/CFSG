module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Seven
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Aut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThinPf10

theorem aePerm_small {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7) : TwinThinPf8.AEPerm n := by
  by_cases h7 : n = 7
  · subst h7; exact aePerm_seven
  · exact aePerm_of_le_six hn5 (by omega)

theorem aeThree_small (h117 : TL4.Model117) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7) :
    TwinThinPf8.AEThree n :=
  TwinThinPf8.aeThree_of_aut_perm (TwinThinPf8.aeAut_of_model117 h117 hn5 hn7)
    (aePerm_small hn5 hn7)

theorem aeBlocks_small {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7) : AEBlocks' n := by
  refine aeBlocks_of_prim hn5 hn7 ?_
  interval_cases n
  · exact fourSetPrim_five
  · exact fourSetPrim_six
  · exact fourSetPrim_seven

end TwinThinPf10

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem twelve_eight_small (h117 : TL4.Model117) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    (hk : n = 7 → J.φ.ker = ⊥) :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'} ∧
      ∃ y : ↥(pSpan (fam K (conjSub g (piGen π)))), J.φ y = AE.yBar α h ∧
        (∃ a : ℕ, y ^ 3 ^ a = 1) ∧ (y : G) * z = z * (y : G) ∧
        ∀ x ∈ piGen π, (y : G) * x = x * (y : G) := by
  have hn8 : n ≠ 8 := by omega
  refine ⟨S.beta_eq_pair' hn5 hn8 (TwinThinPf10.aeBlocks_small hn5 hn7) J hlab, ?_⟩
  have h7 : n = 7 → TwinThinPf8.AEThreeC n ∧ TwinThinPf8.AEChar n ∧ TwinThinPf8.AEAut n ∧
      J.φ.ker = ⊥ := by
    intro h7
    subst h7
    exact ⟨TwinThinPf10.aeThreeC_seven (TwinThinPf8.aeAut_of_model117 h117 hn5 hn7),
      TwinThinPf10.aeChar_of hn8, TwinThinPf8.aeAut_of_model117 h117 hn5 hn7, hk rfl⟩
  exact S.exists_y_cent_all hn5 hn8 (TwinThinPf10.aeThree_small h117 hn5 hn7) J h7 hlab

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
