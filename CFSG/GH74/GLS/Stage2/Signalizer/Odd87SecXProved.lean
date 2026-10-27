module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SecX
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFG
public import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27DatumPlus
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4Datum
public import CFSG.GH74.GLS.Stage2.Local.Prop27Br
public import CFSG.GH74.GLS.Stage2.Local.P27M12Main
import CFSG.GH74.GLS.Stage1.Thm4.Core98b
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.Th.Max3.Packet
import CFSG.GH74.GLS.Stage1.Thm4.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

@[expose] def Psp4NotA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.psp4 S →
    ∀ (x : G) (q : ℕ), DatumPlusPsp4 z x q →
      ¬ Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7))

section Res

variable {G : Type} [Group G] [Finite G]

theorem res_eq_of_le {x : G} {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hle : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T) :
    oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := by
  refine le_antisymm hle (sup_le (sup_le le_sup_right ?_) ?_)
  · exact le_sup_of_le_left (le_oPrimeResidualOf_of_perfect (P34.Jx_le_centralizer x)
      (pLayerOf_two_perfect_P27 _))
  · exact le_sup_of_le_left (le_oPrimeResidualOf_of_isPGroup' hT.le hT.isPGroup)

end Res

section M12

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem secX_m12 (hctx : Stage2Ctx G z Kind.m12 S) {x : G}
    (hx : IsNonCentralInvolution x) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y ↥(centralizer ({x} : Set G))) :
    IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  classical
  have hcen : IsCentralInvolution z := hctx.central
  obtain ⟨g, hg⟩ := exists_conj_mem_cen hcen hx.1
  have hxx' : IsConj x (g * x * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hx'2 : orderOf (g * x * g⁻¹) = 2 := by
    rw [← hx.1]; exact (MulAut.conj g).orderOf_eq x
  have hx'nc : IsNonCentralInvolution (g * x * g⁻¹) :=
    ⟨hx'2, fun hc => hx.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hc hxx'.symm)⟩
  generalize hx₁def : g * x * g⁻¹ = x₁ at hg hxx' hx'2 hx'nc
  have hncz : ¬ IsConj z x₁ := fun hc => hx'nc.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hcen hc)
  have hM : M12NonCentral x₁ := hctx.detail.m12 rfl x₁ hx'2 hncz
  have hW := P27M12.prop27WM12_of_detail hcen hg hx'nc hM
  obtain ⟨q, hqodd, hJb, -⟩ := hW
  obtain ⟨K, y, q', hKc, hKL2, hq8, hyC, hy2, hPGL, hxy, hRO, hout⟩ := hM
  have hx₁y : x₁ ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    exact hyC.symm
  obtain ⟨T, hT, hyT⟩ := exists_sylow_cen_ge (x := x₁) (z := y) hy2 hx₁y
  have hx₁T : x₁ ∈ T := Stage1.Thm4.mem_sylow_of_central hx'2 hT
  have hKJ : K ≤ Jx x₁ := le_sSup hKc
  have hle : oPrimeResidualOf 2 (centralizer ({x₁} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ⊔ Jx x₁ ⊔ T := by
    rw [hRO]
    have hO : pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ≤
        pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ⊔ Jx x₁ ⊔ T := le_sup_left.trans le_sup_left
    have hxle : zpowers x₁ ≤ pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ⊔ Jx x₁ ⊔ T :=
      ((Subgroup.zpowers_le).2 hx₁T).trans le_sup_right
    have hKle : K ≤ pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ⊔ Jx x₁ ⊔ T :=
      hKJ.trans (le_sup_right.trans le_sup_left)
    have hyle : zpowers y ≤ pPrimeCoreOf 2 (centralizer ({x₁} : Set G)) ⊔ Jx x₁ ⊔ T :=
      ((Subgroup.zpowers_le).2 hyT).trans le_sup_right
    exact sup_le (sup_le hO hxle) (sup_le hKle hyle)
  have hres := res_eq_of_le hT hle
  obtain ⟨e⟩ := cenConj_nonempty (z := x) (x := x₁) g hx₁def
  have h1 : IsSection Y ↥(centralizer ({x₁} : Set G)) := IsSection.of_equiv e.symm h
  have hJ := isSection_Jbar_of_residual hT hres hns h1
  exact isL2_odd_of_section hqodd hJb hns hJ

end M12

section Classical

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}

theorem secX_classical
    (hctx : Stage2Ctx G z k S) (hk : IsClassicalKind k)
    (hDP : ∃ xd : G, DatumPlus z xd ∧ (k = Kind.psp4 → ∃ q : ℕ, DatumPlusPsp4 z xd q))
    (hA7 : k = Kind.psp4 → ∀ (xd : G) (q : ℕ), DatumPlusPsp4 z xd q →
      ¬ Nonempty ((↥(Jx xd) ⧸ pPrimeCore 2 ↥(Jx xd)) ≃* alternatingGroup (Fin 7)))
    {x : G} (hx : IsNonCentralInvolution x) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y ↥(centralizer ({x} : Set G))) :
    KindFactorAll k Y := by
  classical
  obtain ⟨xd, hDP1, hDP2⟩ := hDP
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr, hEx⟩ := hDP1
  have hcen : IsCentralInvolution z := hctx.central
  have hncx : ¬ IsConj z x := fun hc =>
    hx.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hcen hc)
  have hxdx : IsConj xd x := (hC.classes x hx.1).resolve_left hncx
  obtain ⟨c, hc⟩ := isConj_iff.mp hxdx
  obtain ⟨e⟩ := cenConj_nonempty c hc
  have h1 : IsSection Y ↥(centralizer ({xd} : Set G)) := IsSection.of_equiv e h
  have hWJ := P27Br.prop27WJ_of_datum
    (⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr⟩ : P27.Datum z xd)
  have hkey : Subgroup.center (↥(Jx xd) ⧸ pPrimeCore 2 ↥(Jx xd)) = ⊥ →
      OutAbel (↥(Jx xd) ⧸ pPrimeCore 2 ↥(Jx xd)) →
      IsSection Y (↥(Jx xd) ⧸ pPrimeCore 2 ↥(Jx xd)) := fun hZ hO =>
    isSection_Jbar_of_residual hC.T_syl (fullF_of_datum hC hS hEx hZ hO).res hns h1
  rcases hWJ.2.1 with ⟨r, hrodd, hr3, hJL2⟩ | ⟨⟨eA⟩⟩
  · have hJ := hkey (S45.center_eq_bot_of_isL2 hJL2) (outAbel_of_isL2 hJL2)
    have hY := isL2_odd_of_section hrodd hJL2 hns hJ
    rcases hk with rfl | ⟨ε, rfl⟩
    · exact hY
    · exact Or.inl hY
  · have hcl : FullCL4 xd 5 := Or.inr ⟨rfl, ⟨eA⟩⟩
    have hJ := hkey (S45.center_bot_of_fullCL4 hcl) (outAbel_of_fullCL4 hcl)
    rcases hk with rfl | ⟨ε, rfl⟩
    · obtain ⟨q', hq'⟩ := hDP2 rfl
      exact absurd ⟨eA⟩ (hA7 rfl xd q' hq')
    · exact Or.inr (IsSection.of_equiv eA.symm hJ)

end Classical

theorem secX_of_ctx
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) (hA7 : Psp4NotA7) : SecX := by
  intro G _ _ z k S hctx hk x hx Y _ _ hns h
  classical
  rcases hk with hpsp | hm12 | ⟨ε, hl4⟩
  · subst hpsp
    have hcl : IsClassicalKind Kind.psp4 := Or.inl rfl
    obtain ⟨xd, q, hDP⟩ := datumPlusPsp4_of_ctx hctx hSch
    exact secX_classical hctx hcl ⟨xd, hDP.toDatumPlusQ.toDatumPlus, fun _ => ⟨q, hDP⟩⟩
      (fun _ => hA7 G z S hctx) hx hns h
  · subst hm12
    exact secX_m12 hctx hx hns h
  · subst hl4
    have hcl : IsClassicalKind (Kind.l4 ε) := Or.inr ⟨ε, rfl⟩
    obtain ⟨g, hg⟩ := exists_conj_mem_cen hctx.central hx.1
    have hx'nc : IsNonCentralInvolution (g * x * g⁻¹) :=
      ⟨by rw [← hx.1]; exact (MulAut.conj g).orderOf_eq x, fun hc => hx.2
        (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hc (isConj_iff.mpr ⟨g, rfl⟩).symm)⟩
    obtain ⟨xd, hDP⟩ := leaf_p27datumPlus_of_ctx (Ctx := Stage2Ctx) hfld
      (fun _ _ _ _ _ _ c => c.data) (fun _ _ _ _ _ _ c => c.central)
      (fun _ _ _ _ _ _ c => c.sylow) (fun _ _ _ _ _ _ c => c.std.kgh) hSch G z (Kind.l4 ε) S hctx hcl
      ⟨_, hg, hx'nc⟩
    exact secX_classical hctx hcl ⟨xd, hDP, fun hh => absurd hh (by simp)⟩
      (fun hh => absurd hh (by simp)) hx hns h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
