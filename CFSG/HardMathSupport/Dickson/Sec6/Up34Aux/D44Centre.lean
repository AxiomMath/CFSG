module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Generic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem up34D44Centre_holds :
    Up34D44Centre := by
  intro Q _ _ hq ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  cases d with
  | D r q =>
    have hd' : r = 4 ∧ q.p = 2 ∧ q.exponent = 2 := hd
    obtain ⟨rfl, hp, hexp⟩ := hd'
    have hmod : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .POmegaPlus 4 q.p q.exponent :=
      CFSG.Models.lieModel_D 4 q hv e
    rw [hp, hexp] at hmod
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmod
    · obtain ⟨-, ⟨m⟩⟩ := pomegaPlus_row hcl (Or.inl (by norm_num))
      have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (Q ⧸ Subgroup.center Q)) := by
        have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 2 = (1, 1) := by
          unfold CFSG.Blueprint.Multiplier.genericOrders
          simp [Nat.even_iff]
        have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 2 = (1, 1) := by
          unfold CFSG.Blueprint.Multiplier.exceptionalOrders
          rfl
        have hu : Subsingleton (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 2 ×
            CFSG.Blueprint.Multiplier.exceptional .POmegaPlus 4 2 2) := by
          unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
          rw [hg, he]
          infer_instance
        exact m.toEquiv.subsingleton
      exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.center_eq_bot_of_hopf_subsingleton'
        hq (MulEquiv.refl _) hsub
    · exact absurd h0 (by norm_num)
  | _ => exact absurd hd (by simp [IsD44Index])

end CFSG.HardMathSupport.Dickson.Sec6
