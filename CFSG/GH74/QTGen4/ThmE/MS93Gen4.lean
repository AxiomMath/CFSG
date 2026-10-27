module

public import CFSG.Quasithin.MS93.S34EDesc
public import CFSG.Quasithin.MS93.S45RF
public import CFSG.GH74.SectionalRank
public import CFSG.Quasithin.MS93.S46I461
public import CFSG.Quasithin.MS93.S46I462
public import CFSG.Quasithin.MS93.S46I463
public import CFSG.Quasithin.MS93.S46I464
public import CFSG.Quasithin.MS93.S46I465
public import CFSG.Quasithin.MS93.S46I466a
public import CFSG.Quasithin.MS93.S46I466b
public import CFSG.Quasithin.MS93.S46I467T
public import CFSG.Quasithin.MS93.S46R466
public import CFSG.Quasithin.EmptyFaithful.SzMSWAsm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GH74.QTGen4.ThmE.Gen4Vacuity
public import CFSG.Quasithin.MS93.RedHyp
public import CFSG.Quasithin.MS93.S46I468
public import Certificates.Certificate4129
public import Certificates.Certificate431004
public import CFSG.Quasithin.MS93.S46R468B
public import CFSG.Quasithin.MS93.S46R468B2
public import CFSG.Quasithin.MS93.S46I469
public import CFSG.Quasithin.MS93.S46RMain1
public import CFSG.Quasithin.MS93.S46RMain3
public import CFSG.Quasithin.MS93.MS93FrontierDeep
public import CFSG.Quasithin.EmptyFaithful.SzMSWC134
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEAssembly
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.EmptyFaithful.SzMSWFin
public import CFSG.Quasithin.MS93.ASC132
public import CFSG.Quasithin.MS93.ASC134C5
public import CFSG.Quasithin.MS93.ASC134NC5
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.GH74.QTGen4.ThmE

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.GH74 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93.S45 CFSG.Quasithin.SzMSW CFSG.Quasithin.MS93.S34D
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem endConcl_gen4 (hred : PUReduce) (hG : Gen4 G) (h : PUHyp M T L) : EndConcl T L := by
  obtain ⟨M₁, T₁, h₁, hT₁, hmin₁, -⟩ := exists_minimal_reduction hred h
  exact ⟨M₁, T₁, h₁, hT₁, hmin₁,
    Or.inr ⟨fun hU => sl3Full_of_sl3U_gen4 hG h₁ hU, fun hU => sp4Full_of_sp4U_gen4 hG h₁ hU⟩⟩

theorem false_of_s45_gen4 (h43 : S43) (h44 : S44) (hG : Gen4 G) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hfull : IsSL3Full M T L) :
    False := by
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 4
  exact false_of_ctx_gen4 hG c hp (by omega)

@[expose] def S46Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 → IsSL3Full M T L → MS93Case11 (Vq M L) T L

@[expose] def MS93ASWGen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G →
    ∀ (M T L : Subgroup G), PUHyp M T L → MS93ConclASW M T L

theorem ms93ConclASW_of_endConcl_gen4 (hG : Gen4 G) (h43 : S43) (h44 : S44) (h38 : S38)
    (h46 : S46Gen4) (h512 : S512) (h7 : S7Two) (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (he : EndConcl T L) : MS93ConclASW M T L := by
  obtain ⟨M₁, T₁, h₁, hT₁T, hmin₁, hor⟩ := he
  have hV₁ : Vq M₁ L = Vq M L := h.vq_eq_vq h₁
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m, hm⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L M₁ T₁ h h₁ hT₁T hmin₁ hV₁ hb hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb with hSL | hSp
      · exact hSL.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact MS93ConclASW.of_case5 hX h5
  have hgood := hor.resolve_left hb₁
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G M₁ T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G M₁ T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)).elim
  have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
    rcases h38 G M T L h hb with hSL | hSp
    · exact hSL.1.le
    · exact (sl3U_sp4U_false h h₁ hSL₁ hSp).elim
  have hFull := hgood.1 hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G hG M₁ T₁ L h₁ hmin₁ h4 hFull
    rw [hV₁] at h11
    exact MS93ConclASW.of_case11 hX (h11.mono hT₁T)
  · exact (false_of_s45_gen4 h43 h44 hG h₁ hmin₁ h4 hFull).elim

theorem ms93ASWGen4_of_items (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18) (h38 : S38)
    (h43 : S43) (h44 : S44) (h46 : S46Gen4) (h512 : S512) (h7 : S7Two) (hred : PUReduce) :
    MS93ASWGen4 := by
  intro G _ _ hG M T L h
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact ms93ConclASW_of_critDist_eq_two h32 h36 h37 h18 h hb
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    exact ms93ConclASW_of_endConcl_gen4 hG h43 h44 h38 h46 h512 h7 h (by omega)
      (endConcl_gen4 hred hG h)

open CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46R

theorem card_field_eq_two_gen4 {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hG : Gen4 G) (h : PUHyp M T L) (hφ : IsSL3FullVia M T L φ) : Fintype.card F = 2 := by
  obtain ⟨⟨n, hn⟩, hφs, hX, hZU, hMV, -, β, hβ, hβker, hβφ⟩ := hφ
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hcardU : Nat.card (Uq M T L) = Fintype.card F ^ 3 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβ⟩), Nat.card_eq_fintype_card]
    simp
  have h16 := card_Uq_le hG h
  rw [hcardU] at h16
  have hF2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  by_contra hne
  have hF3 : 3 ≤ Fintype.card F := by omega
  have : 3 ^ 3 ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_left hF3 3
  omega

theorem s468Cfg_gen4 (hG : Gen4 G) (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (h467 : I467) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} : S468Cfg M T L φ := by
  intro c α β hα hαβ g hg hgN hgZ hodd x hx v hv
  have hq2 := card_field_eq_two_gen4 hG c.pu c.via
  have hAt : S468At (puAmalgam c.pu.le) α β := by
    by_contra h
    obtain ⟨α', hc, hg1, hbad⟩ := exists_crit_of_not_s468At h43 h467 c hα hαβ h
    exact false_of_two h463 h464 h465 h466a c hc (by rw [hg1]; exact hbad) hq2
  exact hAt g ⟨hg, hgN, hgZ, hodd⟩ x hx v hv

theorem s46Gen4_of_items (h14 : MS14AS) (hSQ : SQTKQuot) (h43 : S43) (h463 : I463)
    (h464 : I464) (h465 : I465) (h466a : I466a) (h466b : I466b) (h467 : I467) : S46Gen4 := by
  intro G _ _ hG M T L h hmin hb4 hfull
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have h468 : S468Cfg M T L φ := s468Cfg_gen4 hG h43 h463 h464 h465 h466a h467
  have h469 := i469Cfg_of_s468Cfg h43 h463 h464 h465 h466a h466b h467 h468
  have hKC2 := kc4612TwoCfg_of_i469Cfg h463 h464 h465 h466b h467 h469
  have hidx := idx4612Cfg_of_kc2 hKC2 h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have hkc := kc4612Cfg_of_kc2 hKC2 h43 h463 h464 h465 h466a h466b h467 h469
  have h4612 := i4612Cfg_of hkc hidx h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have h46t := i46tCfg_of h14 hSQ h463 h464 h465 h466a h466b h467 h469 h4612
  exact case11_of_i46sCfg h465 h466a h hmin hb4 hφ
    (i46sCfg_of_i46tCfg h14 hSQ h463 h465 h466b h467 h46t)

theorem ms93ASWGen4_holds
    : MS93ASWGen4 :=
  have h441 := s441_holds
  have h43 := s43_holds
  have h442 := S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441
  have h39 := s39_of s32_holds
  have h42 := s42_of s32_holds
  have h461 := S46.i461_of s32_holds h39 h43 ms14AS_holds sqtkQuot_holds
  have h462 := S46.i462_of h39 h461 ms14AS_holds sqtkQuot_holds
  have h463 := S46.i463_of s32_holds h39 h462
  have h464 := S46.i464_of h42 h461 h462 h463 ms14AS_holds sqtkQuot_holds
  have h465 := S46.i465_of h43 h462 h463 h464
  have h466a := S46.i466a_of (S46R.s466aQ4_of_orbit ms14AS_holds sqtkQuot_holds h43 h462 h463
    h464 h465) h464 h465
  have h466b := S46.i466b_of h43 h461 h462 h463 h464 h465 h466a
  have h467 := S46.i467_of_transv h461 h463 h464 h465 h466a
  ms93ASWGen4_of_items s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds) h43 (s44_frontier h441 h442)
    (s46Gen4_of_items ms14AS_holds sqtkQuot_holds h43 h463 h464 h465 h466a h466b h467)
    s512_holds (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds) puReduce_holds

end CFSG.GH74.QTGen4.ThmE
