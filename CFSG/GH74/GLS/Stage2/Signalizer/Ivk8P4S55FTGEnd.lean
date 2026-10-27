module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGAlt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGMcl
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2


theorem endgame55_of (hInv : InvSec) (hL3 : EndgameL3) : Endgame55 := by
  intro G _ _ z k S T Tstar p H P g X Y hcfg Γ _ _ V _ _ _ ρ K a P' R hf hl hconc
  have hKn : K.Normal := hf.normal
  rcases hconc with hL | ⟨hp, hK⟩
  · exact (hL3 G z k S T Tstar p H P g X Y hcfg Γ V ρ K a P' R hf hl hL).elim
  · obtain ⟨J, hd⟩ := FTG.compData_of_link hf hl
    have hSH : S ≤ H := hcfg.T_eq ▸ hcfg.T_le
    rcases hK with hK7 | hK11
    · refine FTG.endgame_alt hInv hcfg hd hp (Or.inl rfl) hK7 (fun hk _ => ?_)
      obtain ⟨-, -, ⟨eK⟩⟩ := hK7
      obtain ⟨eKJ⟩ := hd.quot
      have hctx := hcfg.ctx
      subst hk
      exact FTG.false_of_mcl_alt7 hctx hSH hd.comp (eKJ.symm.trans eK)
    · exact FTG.endgame_alt hInv hcfg hd hp (Or.inr rfl) hK11
        (fun _ h => absurd h (by norm_num))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
