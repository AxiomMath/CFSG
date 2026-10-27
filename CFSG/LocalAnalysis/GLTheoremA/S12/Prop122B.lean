module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem layer_le_self (p : ℕ) (H : Subgroup G) : GLAPLayer p H ≤ H :=
  sSup_le fun _ hJ => hJ.1

theorem layer_up (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {E Y : Subgroup G} (hE : IsE3 p B E)
    (hDE : D ≤ E) (hKY : K ≤ Y) (hne : GLAPLayer p (K ⊓ cs E) ≠ ⊥) : GLAPLayer p (Y ⊓ cs E) ≠ ⊥ := by
  have hp := h.prime
  have hEel : IsElemAbelian p E := hE.2.1
  have hbal := hin.bal hp h.ctx.ctx.ctx.kProper D E (isPGroup_of_isElemAbelian h.elem)
    (isPGroup_of_isElemAbelian hEel) (fun d hd e he => isElemAbelian_commute hEel (hDE hd) he)
  rw [std_layer h hin, inf_eq_right.2 (Subgroup.centralizer_le (show (D : Set G) ⊆ E from hDE))] at hbal
  have hLE : GLAPLayer p (cs E) ≤ GLAPLayer p (Y ⊓ cs E) := by
    refine sSup_le fun P hP => ?_
    have hPL : P ≤ GLAPLayer p (cs E) := le_sSup hP
    have hPY : P ≤ Y ⊓ cs E := by
      rw [← hbal] at hPL
      exact hPL.trans ((layer_le_self p _).trans (inf_le_inf_right _ hKY))
    exact le_sSup (glaPComponent_of_le hp hP hPY inf_le_right)
  intro hbot
  rw [hbot, le_bot_iff, ← hbal] at hLE
  exact hne hLE

theorem inf_primeCore_le (hp : p.Prime) {K Y : Subgroup G} (hKY : K ≤ Y) :
    K ⊓ GLAPPrimeCoreOf p Y ≤ GLAPPrimeCoreOf p K := by
  have h := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp Y K
  rw [inf_eq_right.2 hKY] at h
  rwa [inf_comm]

theorem twoRank_pQuot_le (hp : p.Prime) (hp2 : p ≠ 2) (J : Subgroup G) :
    GLATwoLocalRank p (PQuot p J) ≤ GLATwoLocalRank p ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥J) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  exact glaTwoLocalRank_quotient_le hp hp2 (GLAPPrimeCore p ↥J) hN

theorem isS0_of_gstar {B J : Subgroup G} {y : G} (hS : IsSTriple p B y J) (hG : IsGStar p B J) : IsS0 p B y J := by
  refine ⟨hS, ?_⟩
  have h5 : tripleLevel p B J = 5 := by
    unfold tripleLevel
    rw [if_pos hG]
  have h1 : tripleLevel p B J ≤ dLevel G p := tripleLevel_le_dLevel hS
  have h2 : dLevel G p ≤ 5 := by
    refine csSup_le' ?_
    rintro j ⟨B', x', L', -, rfl⟩
    exact tripleLevel_le_five' p B' L'
  omega

theorem isEmpty_quaternion_of_card_gt {T : Subgroup G} (h : 8 < Nat.card T) : IsEmpty (T ≃* QuaternionGroup 2) :=
  ⟨fun e => by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at h
    omega⟩

theorem not_nGen_le (hp : p.Prime) {B J K T : Subgroup G} {y : G} (hKJ : K ≤ closureIn J B) (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G)) (hTO : ¬ T ≤ GLAPPrimeCoreOf p K)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    ¬ nGen B (closureIn J B) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) := by
  intro hle
  have hT : T ≤ nGen B (closureIn J B) := le_iSup₂_of_le T ⟨hTK.trans hKJ, hT2, hTB⟩ le_rfl
  exact hTO fun t ht => inf_primeCore_le hp hKy ⟨hTK ht, hle (hT ht)⟩

theorem m_le_five (h : Cfg12 G m 3 B x L D K) (hin : I102InnAt G)
    (hL : catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod 3 L b) : m ≤ 5 := by
  have h1 := hin (Subgroup.centralizer ({x} : Set G)) L B h.tri.comp hL h.tri.bmax.1 h.tri.norm hinner
  rw [card_B_inf_centMod_L h, h.card_B] at h1
  have h2 : 3 ^ m ≤ 3 ^ 5 := by simpa [pow_succ] using h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem not_A6 (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) (hdisj : SmallDisjointAt) : ¬ A6Type p K := by
  intro hA6
  rcases lemma121 h hin with ⟨hU, -⟩ | ⟨hns, -⟩
  · exact hdisj _ hU hA6
  · exact hns (Or.inr hA6)

theorem u42_T0 (hc : S12Ctx G m 3) {B : Subgroup G} {x : G} {L : Subgroup G} (hS : IsSStarMax 3 B x L)
    (hd2 : dLevel G 3 = 2) :
    ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
      B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨hxB, hx1, T₀, hT₀c, hT₀2, hT₀B, hT₀ne, -⟩ := IsSStarMax.essential hS
  refine ⟨T₀, hT₀c, hT₀2, hT₀B, hT₀ne, fun hle => hT₀ne ?_⟩
  exact hc.ctx.stage4.2.2 hd2.le B x T₀ (IsSStarMax.bmax hS) hxB hx1 hle hT₀2 hT₀B

theorem chev2_of_reflTransGen (hc : S10Ctx G p) (hl : Lemma102Inputs G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') (h' : IsChevSimple 2 (PSimple p t'.2.2)) :
    IsChevSimple 2 (PSimple p t.2.2) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact h'
  | @head a c hs _ ih =>
    obtain ⟨Ba, xa, La⟩ := a
    obtain ⟨Bc, xc, Lc⟩ := c
    exact S10.step_chev2 hc hl hs ih

theorem chev2_of_s0 (hc : S12Ctx G m p) (hl : Lemma102Inputs G p) {B J : Subgroup G} {y : G}
    (hS0 : IsS0 p B y J)
    (hn : ¬ nGen B (closureIn J B) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G))) :
    IsChevSimple 2 (PSimple p J) := by
  obtain ⟨-, -, c3, -, -, c6, -, -⟩ := hc.ctx.stage4o
  obtain ⟨B', x', L', hmax, hpump⟩ := c3 B y J hS0
  have hn' : ¬ nGen B' (closureIn L' B') ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x'} : Set G)) :=
    c6 (B, y, J) (B', x', L') hpump hn
  have hBN : B' ≤ Subgroup.normalizer (L' : Set G) := hmax.2.2
  rw [closureIn_eq_self hBN] at hn'
  have hT : ∃ T : Subgroup G, T ≤ L' ∧ IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x'} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hn' (iSup₂_le fun T hT => hcon T hT.1 hT.2.1 hT.2.2)
  obtain ⟨T, hTL, hT2, hTB, hTO⟩ := hT
  have hT1 : T ≠ ⊥ := fun hbot => hTO (by rw [hbot]; exact bot_le)
  have hcyc : CycModSylow p L' :=
    hc.ctx.stage5.2.2 B' x' L' hmax ⟨T, le_sup_of_le_left hTL, hT1, hT2, hTB⟩
  have hchev' : IsChevSimple 2 (PSimple p L') := hc.ctx.stage8.1 B' x' L' ⟨hmax, hcyc⟩
  exact chev2_of_reflTransGen hc.ctx hl hpump.2.2 hchev'

theorem chev2_of_A8 (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) (hp3 : p = 3)
    (hA8 : catalogIs (PSimple p K) isA8) : IsChevSimple 2 (PSimple p J) := by
  subst hp3
  have hJ := ky_eq_J h hin
  have hBJ := nbr_norm h hin
  have hKJ : K ≤ J := by
    rw [← hJ]
    exact le_closureIn_self K _
  have hKcy : K ≤ Subgroup.centralizer ({y} : Set G) :=
    h.cfg.K_le_cs.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.y_mem_D))
  obtain ⟨⟨T, hTK, hT2, hTB, hTc, hT8, hTO⟩, E, hE, hDE, hEne⟩ :=
    hin.a8 B x L D K h.cfg.tri.star h.cfg.pow_four_le h.cfg.pre hA8
  have hess : IsEssential 3 B y :=
    ⟨h.yB, h.y_ne_one, T, hTK.trans hKcy, hT2, hTB, hTc, fun _ => isEmpty_quaternion_of_card_gt hT8⟩
  have hS : IsSTriple 3 B y J := ⟨h.bmax, hess, h.J_comp⟩
  have hG : IsGStar 3 B J := by
    refine ⟨E, hE.1, hE.2.1, hE.2.2, ?_⟩
    rw [closureIn_eq_self hBJ]
    exact layer_up h.cfg hin.l121.common hE hDE hKJ hEne
  have hn := not_nGen_le h.cfg.prime (B := B) (J := J) (by rw [closureIn_eq_self hBJ]; exact hKJ) hTK hT2 hTB hTO hKcy
  exact chev2_of_s0 h.cfg.ctx hin.l102 (isS0_of_gstar hS hG) hn

theorem u42_false (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) (hp3 : p = 3) (hd2 : dLevel G p = 2)
    (hL : catalogIs (PSimple p L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod p L b) (hK : U42Type p K) (hS : IsSTriple p B y J)
    (hnot : ¬ IsS0 p B y J) : False := by
  subst hp3
  have hJ := ky_eq_J h hin
  have hBJ := nbr_norm h hin
  have hle := tripleLevel_le_dLevel hS
  rw [hd2] at hle
  have hne : tripleLevel 3 B J ≠ 2 := fun h2 => hnot ⟨hS, by rw [h2, hd2]⟩
  have hpos : 1 ≤ tripleLevel 3 B J := by
    classical
    unfold tripleLevel
    split_ifs
    · omega
    · have := one_le_fullCoverLevel 3 (PQuot 3 J)
      omega
  have h1 : tripleLevel 3 B J = 1 := by omega
  obtain ⟨-, hchev3⟩ := (tripleLevel_eq_one_iff Nat.prime_three B h.J_comp).1 h1
  have hKx : GLAPComponent 3 (J ⊓ Subgroup.centralizer ({x} : Set G)) K := by
    have := ky_pcomp_cent h.cfg hin.l121.common h.y_mem_D h.y_not_mem
    rwa [hJ] at this
  have hx3 : x ^ 3 = 1 := h.cfg.elem.2 x h.cfg.xD
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hBJ h.cfg.tri.mem
  have hnc : ¬ CentMod 3 J x := fun hc => h.not_cent_x hc.2
  have h6 := hin.i1429 (Subgroup.centralizer ({y} : Set G)) J K x
    (kGroup_centralizer h.cfg.ctx.toS6 h.y_ne_one) h.J_comp hchev3 hxJ hx3 hnc hKx hK
  have hm5 : m ≤ 5 := m_le_five h.cfg hin.i102 hL hinner
  have h7 : GLATwoLocalRank 3 (PQuot 3 J) ≤ m :=
    (twoRank_pQuot_le Nat.prime_three (by norm_num) J).trans ((twoRank_le_top Nat.prime_three J).trans h.cfg.ctx.rank.le)
  omega

theorem chev2_of_U42 (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) (hp3 : p = 3) (hd2 : dLevel G p = 2)
    (hL : catalogIs (PSimple p L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i))
    (hinner : ∀ b ∈ B, InducesInnerMod p L b) (hK : U42Type p K) : IsChevSimple 2 (PSimple p J) := by
  have hhd2 := hd2
  subst hp3
  have hJ := ky_eq_J h hin
  have hBJ := nbr_norm h hin
  have hKJ : K ≤ J := by
    rw [← hJ]
    exact le_closureIn_self K _
  have hKcy : K ≤ Subgroup.centralizer ({y} : Set G) :=
    h.cfg.K_le_cs.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.y_mem_D))
  obtain ⟨T₀, hT₀c, hT₀2, hT₀B, hT₀ne, hT₀O⟩ := u42_T0 h.cfg.ctx h.cfg.tri.star hd2
  obtain ⟨T, hTK, hT2, hTB, hTc, hT32, hTO⟩ := hin.u42 B x L D K h.cfg.tri.star h.cfg.pow_four_le hL hinner
    h.cfg.pre hK ⟨T₀, hT₀c, hT₀2, hT₀B, hT₀ne, hT₀O⟩
  have hess : IsEssential 3 B y :=
    ⟨h.yB, h.y_ne_one, T, hTK.trans hKcy, hT2, hTB, hTc,
      fun _ => isEmpty_quaternion_of_card_gt hT32⟩
  have hS : IsSTriple 3 B y J := ⟨h.bmax, hess, h.J_comp⟩
  by_cases hS0 : IsS0 3 B y J
  · have hn := not_nGen_le h.cfg.prime (B := B) (J := J) (by rw [closureIn_eq_self hBJ]; exact hKJ) hTK hT2 hTB hTO hKcy
    exact chev2_of_s0 h.cfg.ctx hin.l102 hS0 hn
  · exact (u42_false h hin rfl hhd2 hL hinner hK hS hS0).elim

end S12

end CFSG.LocalAnalysis.GLTheoremA
