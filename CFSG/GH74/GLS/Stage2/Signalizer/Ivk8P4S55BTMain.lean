module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTMainB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTBr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSmA7
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSmSz
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalBase
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTKfa
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTMainA

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

theorem case55b_of_inputs (hIn : Inputs55B) : Case55B := by
  intro G _ _ z k S hctx T Tstar p H P hc51 hnot hl52 g X Y hs53 htwo
  have h : Cfg55E G z k S T Tstar p H P g X Y := ⟨hctx, hc51, hnot, hl52, hs53, htwo⟩
  obtain ⟨t, q, I, Q₁, hd⟩ := exists_data5A2 h
  have hk := hd.u.kind
  have hInv : InvSec := final_hInv
  have hL31 : Lemma31Narrow := final_hL31
  obtain ⟨J, hB⟩ := bridgeB_of final_hSch hL31 hInv h hd (outTwoNilp_of_component hInv h hd)
  have hJ : IsComponent J := by
    obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', -, -, hL⟩ := hB
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  have hgh : GHList (↥J ⧸ center ↥J) := ghList_of_quotient_component h.ctx.std.kgh (H_ne_top h)
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)) (QuotientGroup.mk'_surjective _) hJ.1
  have hkill := false_of_killed hInv h hd hJ
  have hfin : ∀ {F : (Y : Type) → [Group Y] → Prop}, (∀ (k : Kind), IsClassicalKind k →
      ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → F Y →
        ¬ KindFactorAll k Y ∧ FinCellB Y) → F (↥J ⧸ center ↥J) → False :=
    fun hF hFJ => cellV_of_finCellB hInv hF G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hFJ
  have hrank : ∀ {F : (Y : Type) → [Group Y] → Prop}, RankCell F → F (↥J ⧸ center ↥J) → False :=
    fun hR hFJ => false_of_rankCellK hInv (hR k hk) h hd J hJ hFJ
  rcases ghList_cases hgh with hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF |
    hF | hF
  · obtain ⟨n, hn7, hn11, hY⟩ := hF
    rcases Nat.lt_or_ge n 8 with h8 | h8
    · obtain rfl : n = 7 := by omega
      rcases hk with hk | ⟨ε, hk⟩
      · subst hk
        exact false_of_rankCellK hInv rankCellK_a7 h hd J hJ hY
      · exact cellV_of_finCellA hL31 hIn.res
          (F := fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin 7)))
          (fun Y _ _ _ hY => hIn.a7 Y hY) G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hY
    · exact hfin (F := fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin n)))
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_alt hk h8 hn11 hY, hIn.alt n h8 hn11 Y hY⟩) hY
  · rcases hF with hF | hF | hF | hF | hF | hF | hF
    · exact hrank rankCell_m11j1 (Or.inl hF)
    · exact hfin (F := fun Y _ => NativeSporadic.IsSporadic Y .M12)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_m12 hk hY, hIn.m12 Y hY⟩) hF
    · exact hfin (F := fun Y _ => NativeSporadic.IsSporadic Y .M22)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_m22 hk hY, hIn.m22 Y hY⟩) hF
    · exact hfin (F := fun Y _ => NativeSporadic.IsSporadic Y .M23)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_m23 hk hY, hIn.m23 Y hY⟩) hF
    · exact hrank rankCell_m11j1 (Or.inr hF)
    · exact hfin (F := fun Y _ => NativeSporadic.IsSporadic Y .J2)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_j2 hk hY, hIn.j2 Y hY⟩) hF
    · exact hfin (F := fun Y _ => NativeSporadic.IsSporadic Y .J3)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_j3 hk hY, hIn.j3 Y hY⟩) hF
  · exact hkill (by simp only [hF, or_true])
  · rcases hF with hF | hF | hF | hF | hF
    · exact hrank rankCell_l28sz8 (Or.inl hF)
    · exact hfin (F := fun Y _ => LieModel Y .PSL 2 2 4)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_l216 hk hY, hIn.l216 Y hY⟩) hF
    · exact hfin (F := fun Y _ => LieModel Y .PSL 3 2 2)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_l34 hk hY, hIn.l34 Y hY⟩) hF
    · exact hfin (F := fun Y _ => LieModel Y .PSU 3 2 2)
        (fun k hk Y _ _ _ hY => ⟨not_kindFactorAll_u34 hk hY, hIn.u34 Y hY⟩) hF
    · exact hrank rankCell_l28sz8 (Or.inr hF)
  · exact cellV_fl2 (fl2Res_of_resB hIn.res) G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF
  · exact hkill (by simp only [hF, true_or])
  · exact hkill (by simp only [hF, true_or, or_true])
  · exact hIn.sp4 G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF
  · exact hkill (by simp only [hF, true_or, or_true])
  · exact hkill (by simp only [hF, true_or, or_true])
  · exact hIn.l4 G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF
  · exact hIn.u4 G z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hF
  · exact hkill (by simp only [hF, true_or, or_true])
  · exact hkill (by simp only [hF, true_or, or_true])
  · exact hkill (by simp only [hF, true_or, or_true])

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
