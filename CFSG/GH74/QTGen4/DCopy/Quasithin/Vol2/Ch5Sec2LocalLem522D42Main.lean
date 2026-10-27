module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522D42CartanB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42CartanB
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Seven

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_2_2_eq_D42_of_F4
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hF : FactL2LieParabolic)
    (hLie : Stmt5_2_L2Lie_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    Stmt5_2_2_eq_D42_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl Lh k hhat hlt htype hres
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hT₀N : T₀ ≤ Subgroup.normalizer (L₂ : Set G) := inf_le_right
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hBX : B ≤ X₀ := le_sup_right
  obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
  have hL₂c : L₂ ∈ cComp L₂ := by
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact cComp_mem_of_le hK₁ le_rfl (le_of_mem_cComp hK₁)
    · exact cComp_mem_of_le hL₂P le_rfl (le_of_mem_cComp hL₂P)
  have hL₂T₀ : L₂ ∈ lFamily T₀ := by
    refine cComp_mem_of_subnormal (IsSubnormal.step le_sup_left ?_ (IsSubnormal.refl _)) hL₂c
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT₀N)
  have l : EmbLoc G T₀ X₀ L₂ Lh :=
    ⟨h.simple, h.nonabelian, h.qtke, hOX, hT₀syl, hL₂X, hL₂T₀, hT₀N, hhat, hlt⟩
  have hXN : X₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 l.pCoreX l.sylowX
      l.hat_cComp
    rwa [l.conjClosure_hat] at this
  obtain ⟨hL8, hD4⟩ := D42.is3D4_bar l htype hres
  have hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂ := by
    have h1 := l.sylowK
    rwa [hT₀def, inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer : L₂ ≤ _)] at h1
  have hBN := hyp.B_le_normalizer_L2_F4 h510 h331 hR hLie
  obtain ⟨b, hbB, hb1, hb7, hbK⟩ :=
    D42.exists_seven_trivial hBN hL8 (D42.dvd_card_B_F4 h510 hF h38 hyp hL₂K hL8 hSL₂)
  have h3 := D42.three_le_pRank_of_seven l hXN hD4 hL8 (hBX hbB) hb1 hb7 (hBN hbB) hbK
  have h2 := pRank_le_two_of_pCoreOf_ne_bot h.qtke hOX (p := 7) (by norm_num) (by norm_num)
  omega

end CFSG.Quasithin.H13
