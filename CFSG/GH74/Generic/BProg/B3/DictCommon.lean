module

public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.GH74.Generic.S3.BFreePromote
public import CFSG.GH74.GLS.Balance.OResidual
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isJ2_of_isPCompIn (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G)
    (hK : KGH G) {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L)
    (hOnly : S3.OnlyInvX x K) {M : Subgroup G} (hM : IsPCompIn 2 (centralizer ({x} : Set G)) M)
    (himg : S3.imgBar x M = K) : IsJ2 x M := by
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hr
  have hILo : IsILo 2 x M :=
    ⟨hx, by simpa [oBound] using TwoThin.rankThreeCentralizers G hs hn h3 x hx, hM⟩
  have hbar : C3.Layer1.PumpCalc.bar x M = K := himg
  obtain ⟨e⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hM
  have eMK : (↥M ⧸ pPrimeCore 2 ↥M) ≃* ↥K := e.trans (MulEquiv.subgroupCongr hbar)
  have hILoG2 : IsILoG2 x M := ⟨hILo, inG2_of_mulEquiv eMK.symm hg2⟩
  have hdepth := S3.depthOfG_eq_of_mindepth hs hn hr hK hx hKc hg2 hmin
  have hdM : d2 (↥M ⧸ pPrimeCore 2 ↥M) = d2 ↥K := d2_congr eMK
  have hT : IsTwoTerminal x M :=
    C3.Layer1.PumpH1.isTwoTerminal_of_pRank_le_one hILo
      (S3.pRank_CxK_le_one_of_onlyInvX hx hM himg hOnly)
  exact ⟨hILoG2, hdM.trans hdepth.symm, hT⟩

theorem noAltJ2_of_minDepth (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G)
    (hK : KGH G) {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L)
    (hd : d2 ↥K = 6 ∨ d2 ↥K = 7) : NoAltJ2 G := by
  have hdepth := S3.depthOfG_eq_of_mindepth hs hn hr hK hx hKc hg2 hmin
  rcases hd with h6 | h7
  · refine S3.noIsJ2Alt_of_depth (d := 6) (by norm_num) (fun K' _ hK' hAlt => ?_) (hdepth.trans h6)
    obtain ⟨-, hcl⟩ := hK'
    rcases hcl with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hLie, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact hAlt.2 hLie
    · omega
    · omega
  · exact S3.noIsJ2Alt_of_depth (d := 7) (by norm_num) S3.not_isAltQuot_of_inG2Depth_seven
      (hdepth.trans h7)

omit [Finite G] in
theorem le_iSup_conj_of_quasisimple {L B : Subgroup G} (hL : IsQuasisimple ↥L) (hBL : B ≤ L)
    (hB : ∃ b ∈ B, ∃ l ∈ L, b * l ≠ l * b) :
    L ≤ ⨆ g ∈ L, B.map (MulAut.conj g).toMonoidHom := by
  set R : Subgroup G := ⨆ g ∈ L, B.map (MulAut.conj g).toMonoidHom with hR
  have hRinv : ∀ h ∈ L, R.map (MulAut.conj h).toMonoidHom ≤ R := by
    intro h hh
    rw [hR, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [Subgroup.map_map]
    refine le_iSup_of_le (h * g) (le_iSup_of_le (L.mul_mem hh hg) (le_of_eq ?_))
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hBR : B ≤ R := by
    have h1 : B.map (MulAut.conj (1 : G)).toMonoidHom ≤ R :=
      le_iSup₂_of_le (1 : G) L.one_mem le_rfl
    intro b hb
    refine h1 ⟨b, hb, ?_⟩
    simp
  have hN : (R.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ R := hn
    have h1 := hRinv (g : G) g.2 (Subgroup.mem_map_of_mem _ hn')
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ R
    simpa [MulAut.conj_apply] using h1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hL hN with htop | hcen
  · intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ R.subgroupOf L := by rw [htop]; trivial
    exact this
  · exfalso
    obtain ⟨b, hb, l, hl, hbl⟩ := hB
    have hbN : (⟨b, hBL hb⟩ : ↥L) ∈ R.subgroupOf L := hBR hb
    have h1 := Subgroup.mem_center_iff.1 (hcen hbN) ⟨l, hl⟩
    exact hbl (congrArg Subtype.val h1.symm)

omit [Finite G] in
theorem oPrimeResidual_le_liftAt {x y : G} {Lb : Subgroup (CentralizerBar x)} {B : Subgroup G}
    (hBx : B ≤ centralizer ({x} : Set G)) (hBy : B ≤ centralizer ({y} : Set G))
    (hBL : S3.imgBar x B ≤ Lb) : oPrimeResidualOf 2 B ≤ liftAt x y Lb := by
  unfold liftAt
  refine GLS.Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 => ?_
  refine GLS.Balance.mem_oPrimeResidualOf_of_two_element ?_ h2
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨v, hBx hv⟩, ?_, rfl⟩, hBy hv⟩
  exact hBL (S3.mem_imgBar.2 ⟨⟨v, hBx hv⟩, hv, rfl⟩)

end CFSG.GH74.Generic.BProg.B3
