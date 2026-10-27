module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Main
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdFull
public import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27DatumPlusQ

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
open CFSG.GH74.GLS.Stage2.Local.P27 CFSG.GH74.GLS.Stage1.Main

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

theorem l203Prop27_of_datum
    (hdat : ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
      (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S →
        Stage1L4 G z S ε q L₁ L₂ → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) →
        ∃ (x : G) (T D₁ D₂ U T₁ : Subgroup G) (n : ℕ) (t' : G), Cfg z x T q ∧
          Syl z x T D₁ D₂ U n t' ∧ Tr z x T D₁ D₂ U T₁ ∧ Extra z x T D₁ D₂ U t' ∧
          Nat.card ↥D₂ = 2 * Nat.card ↥U) :
    L203Prop27 := by
  intro G _ _ z S ε q L₁ L₂ hctx hL4 hmod
  have hx₀ : ∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀ := by
    rcases hL4.fusion with ⟨h1, -⟩ | ⟨-, x₀, hx₀, -⟩
    · exfalso
      cases ε <;> simp at h1 hmod <;> omega
    · exact ⟨x₀, hctx.S_le_Cen hx₀.x_mem, hx₀.x_inv, hx₀.x_nonCentral⟩
  obtain ⟨x, T, D₁, D₂, U, T₁, n, t', hcfg, hsyl, htr, hex, hD₂⟩ := hdat G z S ε q L₁ L₂ hctx hL4 hx₀
  have hc : FullCL4 x q := QId.fullCL4_of_extra hcfg hsyl htr hex hD₂
  have hx2 : orderOf x = 2 := hcfg.x_nc.1
  have hnc : ¬ IsConj z x := fun h => hcfg.x_nc.2 (isCentralInvolution_of_isConj' hcfg.z_central h)
  obtain ⟨T₁s, h1, h2, h3, -, -, h6⟩ := fullFT1_of_extra hsyl hex
  have hE := S45.fullE_of_T1 hcfg.T_syl hx2 (S45.center_bot_of_fullCL4 hc) ⟨T₁s, h1, h2, h3, h6⟩
  exact ⟨x, hx2, hnc, hc, hE.1⟩

theorem l203Prop27_thm
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : L203Prop27 :=
  l203Prop27_of_datum fun G _ _ z S ε q L₁ L₂ hctx hL4 hx₀ => by
    obtain ⟨x, T, D₁, D₂, U, T₁, n, t', hcfg, hsyl, htr, hex, -, hD₂⟩ :=
      p27DatumPlusQL4_of_data (hfld G z (Kind.l4 ε) S hctx) hctx.central hctx.sylow hctx.std.kgh hSch
        ε rfl q L₁ L₂ hL4 hx₀
    exact ⟨x, T, D₁, D₂, U, T₁, n, t', hcfg, hsyl, htr, hex, hD₂⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
