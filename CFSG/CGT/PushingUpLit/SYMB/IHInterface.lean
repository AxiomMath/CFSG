module

public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteen
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenH
public import CFSG.CGT.PushingUpLit.BHS6.SixEight
public import CFSG.CGT.PushingUpLit.BHS7.FifteenMain
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightLinBlock
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightS3
public import CFSG.CGT.PushingUpLit.BHS7.Final

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7

@[expose] def IHFor {Γ : Type} [Group Γ] [Finite Γ] (G : Subgroup Γ) : Prop :=
  ∀ G' T' : Subgroup Γ, Nat.card G' < Nat.card G → CharTwo G' → IsSylowOf 2 T' G' →
    cStarIn G' T' ≠ G' → LocalCStarConcl G' T'

@[expose] def ThreeEightIH : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T V : Subgroup Γ), ThreeEightHyp G T V → IHFor G →
    ∃ E : Subgroup Γ, IsBTBlock G T E ∧
      G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ∧
      ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V

@[expose] def ThreeEightSymmIH : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T V : Subgroup Γ) (m : ℕ), 2 ≤ m →
    CharTwo G → IsSylowOf 2 T G → cStarIn G T ≠ G →
    G ≤ Subgroup.normalizer (V : Set Γ) → omegaOneCenterOf T ≤ V →
    V ≤ omegaOneCenterOf (pCoreOf 2 G) → IsNatSym G V (2 * m + 1) → IHFor G →
      ∃ E : Subgroup Γ, IsBTBlock G T E ∧
        G ≤ baum T ⊔ E ⊔ (G ⊓ Subgroup.centralizer (V : Set Γ)) ∧
        ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V

theorem three_eight_ih (hmult : SL2EvenMultiplierTrivial) (hn2 : PushUpPerfectTwo)
    (hsym : ThreeEightSymmIH) : ThreeEightIH := by
  intro Γ _ _ G T V h hih
  have hT : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf h.sylow
  rcases h.natural with ⟨n, hn, hnat⟩ | ⟨m, hm, hnat⟩
  · exact three_eight_natSL_block hmult hn2 h.charTwo hT h.ne h.normal h.le_V h.V_le hn hnat
  · rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have hm1' : m = 1 := by omega
      subst hm1'
      exact three_eight_natSL_block hmult hn2 h.charTwo hT h.ne h.normal h.le_V h.V_le le_rfl
        (isNatSL_one_of_isNatSym_three hnat)
    · exact hsym Γ G T V m hm2 h.charTwo h.sylow h.ne h.normal h.le_V h.V_le hnat hih

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem false_of_natTail_ih (h : MinCex G T) (h4 : Seven4 G T) (h38 : ThreeEightIH)
    {Ê : Subgroup Γ} (hd : NatTailData G T Ê) : False := by
  classical
  have hG := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.2.1.to_le hBT
  have hTC : T ≤ cStarIn G T := le_cStarIn_of_minCex h
  have hÊG : Ê ≤ G := le_of_isSubnormal_bhs hd.subnormal
  have hBG : baum T ≤ G := hBT.trans hT2.1
  have hHG : baum T ⊔ Ê ≤ G := sup_le hBG hÊG
  by_cases hH : baum T ⊔ Ê = G
  ·
    obtain ⟨V, h3⟩ := hd.caseTwo hH
    obtain ⟨E, hE, hGE, -⟩ := h38 Γ G T V h3 h.ih
    have hVQ : V ≤ pCoreOf 2 G := h3.V_le.trans (omegaOneCenter_le_pCoreOf G)
    have hEV : E ≤ Subgroup.normalizer (V : Set Γ) := hE.le.trans h3.normal
    have hne : ⁅E, V⁆ ≠ ⊥ := fun h0 => hE.nonCentral (le_bot_iff.mp
      ((Subgroup.commutator_mono le_rfl h3.le_V).trans h0.le))
    have hWV : (blockW E : Set Γ) ⊆ (V : Set Γ) := by
      rw [← commutator_eq_blockW hG hT hE hVQ hEV hne]
      exact commutator_le_of_le_normalizer hEV
    have hEN : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ Subgroup.normalizer (E : Set Γ) :=
      (inf_le_inf_left G (Subgroup.centralizer_le hWV)).trans (six_six hG hT hE)
    have hGN : G ≤ Subgroup.normalizer (E : Set Γ) :=
      hGE.trans (sup_le (sup_le (baum_le_normalizer_of_isBTBlock hE) Subgroup.le_normalizer) hEN)
    have hsub : IsSubnormal E G := isSubnormal_of_le_of_le_normalizer hE.le hGN
    refine false_of_subnormal_block h h4 hE (fun hEC => h.ne ?_) hsub
    refine le_antisymm (cStarIn_le G T) fun g hg => ?_
    have hVC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
      (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => h3.le_V hx)).trans
        (centralizer_le_cStarIn G T)
    exact (sup_le (sup_le (hBT.trans hTC) hEC) hVC) (hGE hg)
  ·
    have hHlt : baum T ⊔ Ê < G := lt_of_le_of_ne hHG hH
    have hHC : ¬ baum T ⊔ Ê ≤ cStarIn G T := fun hle =>
      hd.not_le ((le_sup_right : Ê ≤ baum T ⊔ Ê).trans hle)
    have hHl : baum T ⊔ Ê ∈ lSet G T := ⟨hHlt, le_sup_left, hHC⟩
    have hSÊ : IsSylowTwoOf (T ⊓ Ê) Ê := isSylowTwoOf_inf_of_isSubnormal hd.subnormal hT2
    have hSH : IsSylowTwoOf (T ⊓ (Ê ⊔ baum T)) (Ê ⊔ baum T) :=
      isSylowTwoOf_inf_sup_baum hT2.2.1 hd.baum_le hSÊ
    rw [sup_comm Ê (baum T)] at hSH
    obtain ⟨-, -, hconcl⟩ := seven_three h hT2 hHl hSH
    obtain ⟨𝒢, hbl, hinv, hcomm, hsup, -⟩ := hconcl
    have hBS : baum T ≤ T ⊓ (baum T ⊔ Ê) := le_inf hBT le_sup_left
    have hex : ∃ F ∈ 𝒢, ¬ F ≤ cStarIn G T := by
      by_contra hall
      push Not at hall
      apply hHC
      rw [← hsup]
      exact sup_le (two_three_d hT2 hb0 hHG hSH hBS) (iSup₂_le fun F hF => hall F hF)
    obtain ⟨F, hF, hFn⟩ := hex
    have hFb : IsBTBlock (baum T ⊔ Ê) (T ⊓ (baum T ⊔ Ê)) F := hbl F hF
    have hbaum : baum (T ⊓ (baum T ⊔ Ê)) = baum T :=
      (CFSG.Quasithin.baum_eq_of_le hBS inf_le_left).symm
    have hFG : IsBTBlock G T F := isBTBlock_of_sub hFb hHG hbaum hFn
    have hsubH : IsSubnormal F (baum T ⊔ Ê) := isSubnormal_of_mem_concl hbl hinv hcomm hF
    have hFÊ : F ≤ Ê := by
      refine le_of_forall_odd_le (opResidual_eq_of_isBTBlock hFb) fun x hx hodd => ?_
      have hx' : x ∈ Ê ⊔ baum T := by
        have := hFb.le hx
        rwa [sup_comm] at this
      exact mem_of_odd_orderOf_sup hB2 hd.baum_le hx' hodd
    have hFsub : IsSubnormal F Ê := A3.subnormal_of_le_of_le hsubH hFÊ le_sup_right
    exact false_of_subnormal_block h h4 hFG hFn (A3.subnormal_trans hFsub hd.subnormal)

structure Sec7RestIH : Prop where
  sl2EvenMultiplier : SL2EvenMultiplierTrivial
  pushUpPerfectTwo : PushUpPerfectTwo
  threeEightSymmIH : ThreeEightSymmIH

theorem Sec7RestIH.threeEightIH (hR : Sec7RestIH) : ThreeEightIH :=
  three_eight_ih hR.sl2EvenMultiplier hR.pushUpPerfectTwo hR.threeEightSymmIH

theorem seven_five_of_restIH (hR : Sec7RestIH) (h : MinCex G T)
    (h4 : Seven4 G T) : Seven5 G T := fun hmin => by
  obtain ⟨Ê, hd⟩ := five_of_certificate h hmin
  exact false_of_natTail_ih h h4 hR.threeEightIH hd

theorem seven_fifteen_of_restIH (hR : Sec7RestIH) (h : MinCex G T)
    (h4 : Seven4 G T) (h5 : Seven5 G T) (h13 : Seven13 G T) (h14 : Seven14 G T) : False := by
  obtain ⟨Ê, hd⟩ := fifteen_of_certificate h h5 h13 h14
  exact false_of_natTail_ih h h4 hR.threeEightIH hd

theorem not_minCex_of_pendingIH (hP : Sec7Pending) (hR : Sec7RestIH)
    (G T : Subgroup Γ) :
    ¬ MinCex G T := fun h => by
  have h4 := seven_four_of_minCex h
  have h5 := seven_five_of_restIH hR h h4
  have h13 := hP.seven_thirteen Γ G T h h4 h5 (seven_seven_of_seven_four h h4)
  exact seven_fifteen_of_restIH hR h h4 h5 h13
    (seven_fourteen_of_six_eight h h13 (six_eight h.charTwo h.sylow))

theorem bhsLocalCStar_of_pendingIH (hP : Sec7Pending)
    (hR : Sec7RestIH) : BHSLocalCStar :=
  bhsLocalCStar_of_concl fun _ _ _ G T hc hT hne =>
    concl_of_forall_not_minCex (fun G T => not_minCex_of_pendingIH hP hR G T) G T hc hT hne

theorem bhsLocalCStar_of_restIH (hR : Sec7RestIH) :
    BHSLocalCStar :=
  bhsLocalCStar_of_pendingIH sec7Pending_holds hR

end CFSG.CGT.PushingUpLit.SYMB
