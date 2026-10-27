module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cP27
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDm12
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4Datum
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFG
public import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27DatumPlus
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cHyp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

section Classical

variable {G : Type} [Group G] [Finite G] {z : G}

theorem fullG_of_datumPlus
    {xd : G} (hDP : DatumPlus z xd) : P27.FullG xd := by
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr, hEx⟩ := hDP
  have hWJ := P27Br.prop27WJ_of_datum
    (⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr⟩ : P27.Datum z xd)
  rcases hWJ.2.1 with ⟨r, hrodd, hr3, hJL2⟩ | ⟨⟨eA⟩⟩
  · exact fullG_of_datum hC hS hEx (S45.center_eq_bot_of_isL2 hJL2) (outAbel_of_isL2 hJL2)
  · have hcl : FullCL4 xd 5 := Or.inr ⟨rfl, ⟨eA⟩⟩
    exact fullG_of_datum hC hS hEx (S45.center_bot_of_fullCL4 hcl) (outAbel_of_fullCL4 hcl)

theorem fullG_of_datumPlus_conj
    (hcen : IsCentralInvolution z) {xd : G} (hDP : DatumPlus z xd) {x : G}
    (hx : IsNonCentralInvolution x) : P27.FullG x := by
  have hncx : ¬ IsConj z x := fun hc =>
    hx.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hcen hc)
  have hF := fullG_of_datumPlus hDP
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr, hEx⟩ := hDP
  have hxdx : IsConj xd x := (hC.classes x hx.1).resolve_left hncx
  exact fullG_of_isConj hxdx hF

end Classical

theorem nonCentralDihedral_of_ctx
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : NonCentralDihedral := by
  intro G _ _ z k S hctx x hx
  classical
  have hcen : IsCentralInvolution z := hctx.central
  have hncx : ¬ IsConj z x := fun hc =>
    hx.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hcen hc)
  rcases kind_cases_of_data hcen hctx.data with hone | ⟨hk, -⟩
  · exact absurd (hone z x hctx.orderOf_z hx.1) hncx
  rcases hk with hcl | hm12
  · rcases hcl with hpsp | ⟨ε, hl4⟩
    · subst hpsp
      obtain ⟨xd, q, hDP⟩ := datumPlusPsp4_of_ctx hctx hSch
      exact fullG_of_datumPlus_conj hcen hDP.toDatumPlusQ.toDatumPlus hx
    · subst hl4
      have hcl : IsClassicalKind (Kind.l4 ε) := Or.inr ⟨ε, rfl⟩
      obtain ⟨g, hg⟩ := exists_conj_cen_of_central hcen hx.1
      have hx'nc : IsNonCentralInvolution (g * x * g⁻¹) :=
        ⟨by rw [← hx.1]; exact (MulAut.conj g).orderOf_eq x, fun hc => hx.2
          (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hc (isConj_iff.mpr ⟨g, rfl⟩).symm)⟩
      obtain ⟨xd, hDP⟩ := leaf_p27datumPlus_of_ctx (Ctx := Stage2Ctx) hfld
        (fun _ _ _ _ _ _ c => c.data) (fun _ _ _ _ _ _ c => c.central)
        (fun _ _ _ _ _ _ c => c.sylow) (fun _ _ _ _ _ _ c => c.std.kgh) hSch G z (Kind.l4 ε) S hctx hcl
        ⟨_, hg, hx'nc⟩
      exact fullG_of_datumPlus_conj hcen hDP hx
  · subst hm12
    exact fullG_of_m12 hx.1 (hctx.detail.m12 rfl x hx.1 hncx)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
