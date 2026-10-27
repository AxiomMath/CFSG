module

public import CFSG.GH74.Generic.S3.BFreeBasic
public import CFSG.GH74.Generic.S3.PumpStep
public import CFSG.GH74.Generic.S3.Main19
public import CFSG.GH74.GLS.C3.Layer1.St1RigMain
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem exists_rigid_gilman_rank {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}
    (hrig : IsPRigid 2 x K) :
    ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsPRigid 2 x' K' ∧
      IsGilmanMax x' K' ∧ pRank 2 ↥(CxK x K) ≤ pRank 2 ↥(CxK x' K') := by
  classical
  let S := {p : G × Subgroup G // LongPumpUp 2 x K p.1 p.2}
  have : Nonempty S := ⟨⟨(x, K), LongPumpUp.refl' hrig.1⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max
    (fun p : S => toLex (pRank 2 ↥(CxK p.1.1 p.1.2), sylVal p.1.1 p.1.2))
  refine ⟨p.1.1, p.1.2, p.2, ⟨p.2.isILo_right, fun x'' K'' hlong => ?_⟩, fun x'' K'' hlong => ?_, ?_⟩
  · obtain ⟨e1⟩ := hrig.2 p.1.1 p.1.2 p.2
    obtain ⟨e2⟩ := hrig.2 x'' K'' (LongPumpUp.trans' p.2 hlong)
    exact ⟨e2.trans e1.symm⟩
  · have h1 := hp ⟨(x'', K''), LongPumpUp.trans' p.2 hlong⟩
    rw [Prod.Lex.le_iff] at h1
    exact h1
  · have h1 := hp ⟨(x, K), LongPumpUp.refl' hrig.1⟩
    rw [Prod.Lex.le_iff] at h1
    rcases h1 with h1 | ⟨h1, -⟩
    · exact h1.le
    · exact h1.le

@[expose] def PumpGood {G : Type} [Group G] {x : G} (K : Subgroup (CentralizerBar x)) (M₀ : Subgroup G)
    (y : G) (N : Subgroup G) : Prop :=
  GLS.IsILo 2 y N ∧ G2Pair y (imgBar y N) ∧ d2 ↥(imgBar y N) = d2 ↥K ∧
    FRank ↥(imgBar y N) = FRank ↥K ∧
    Nonempty ((↥N ⧸ pPrimeCore 2 ↥N) ≃* (↥M₀ ⧸ pPrimeCore 2 ↥M₀))

theorem pumpGood_step {d : ℕ} (hd0 : d ≠ 0) (hTab : B_pumpupStepAt d) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G)
    {x : G} {K : Subgroup (CentralizerBar x)} (hd : d2 ↥K = d) (hmax : IsJMax x K)
    {M₀ : Subgroup G} {y u : G} {N H : Subgroup G}
    (hgood : PumpGood K M₀ y N) (hlt : GLS.PumpUpLT 2 y N u H) : PumpGood K M₀ u H := by
  obtain ⟨hILoN, hG2N, hdL, hFL, ⟨eN⟩⟩ := hgood
  have hILoH : GLS.IsILo 2 u H := hlt.2.1
  have hNpc : GLS.IsPCompIn 2 (centralizer ({y} : Set G)) N := hILoN.2.2
  have hHpc : GLS.IsPCompIn 2 (centralizer ({u} : Set G)) H := hILoH.2.2
  obtain ⟨eNb⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hNpc
  obtain ⟨eHb⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hHpc
  have hLdepth : InG2Depth d ↥(imgBar y N) := by
    have h1 : d2 ↥(imgBar y N) ≠ 0 := by rw [hdL, hd]; exact hd0
    have := inG2Depth_d2_of_ne_zero h1
    rwa [hdL, hd] at this
  have hNdepth : InG2Depth d (↥N ⧸ pPrimeCore 2 ↥N) := inG2Depth_of_mulEquiv eNb.symm hLdepth
  obtain ⟨hInG2H, hcases⟩ := hTab G hs hn hgen hK y u N H hlt hNdepth
  have hG2H : G2Pair u (imgBar u H) :=
    ⟨hILoH.1, C3.Layer1.PumpCalc.isComponent_bar hHpc, inG2_of_mulEquiv eHb hInG2H⟩
  obtain ⟨h1, h2⟩ := hmax.2 u (imgBar u H) hG2H
  rw [hd] at h1 h2
  have hdH : d2 (↥H ⧸ pPrimeCore 2 ↥H) = d2 ↥(imgBar u H) := d2_congr eHb
  have hFH : FRank (↥H ⧸ pPrimeCore 2 ↥H) = FRank ↥(imgBar u H) := fRank_congr eHb
  have hdN : d2 (↥N ⧸ pPrimeCore 2 ↥N) = d2 ↥(imgBar y N) := d2_congr eNb
  have hFN : FRank (↥N ⧸ pPrimeCore 2 ↥N) = FRank ↥(imgBar y N) := fRank_congr eNb
  rcases hcases with hlt' | ⟨heq, hF⟩ | he
  · omega
  · exfalso
    have h3 := h2 (by omega)
    omega
  · obtain ⟨e⟩ := he
    refine ⟨hILoH, hG2H, ?_, ?_, ⟨e.trans eN⟩⟩
    · rw [← hdH, d2_congr e, hdN, hdL]
    · rw [← hFH, fRank_congr e, hFN, hFL]

theorem noIsJ2Alt_of_depth {d : ℕ} (hd0 : d ≠ 0) (hAlt : ∀ (K : Type) [Group K], InG2Depth d K → ¬ IsAltQuot K)
    {G : Type} [Group G] (hdepth : depthOfG G = d) :
    ¬ ∃ (x' : G) (M' : Subgroup G), IsJ2Alt x' M' := by
  rintro ⟨x', M', hJ2', hAlt'⟩
  have hd' : d2 (↥M' ⧸ pPrimeCore 2 ↥M') = d := hJ2'.2.1.trans hdepth
  have hcl : InG2Depth d (↥M' ⧸ pPrimeCore 2 ↥M') := by
    have := inG2Depth_d2_of_ne_zero (K := ↥M' ⧸ pPrimeCore 2 ↥M') (by rw [hd']; exact hd0)
    rwa [hd'] at this
  exact hAlt _ hcl hAlt'

theorem not_isAltQuot_of_inG2Depth_seven (K : Type) [Group K] (h : InG2Depth 7 K) : ¬ IsAltQuot K := by
  obtain ⟨hG, hdisj⟩ := h
  have hL3 : IsL3OddGt3 K := by
    rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩ | ⟨h1, -⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h
    · omega
  obtain ⟨p, f, -, -, -, hmod⟩ := hL3
  exact fun hA => hA.2 (ofLieType_of_lieModel_L3 hG.1.1 hmod)

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}

end CFSG.GH74.Generic.S3
