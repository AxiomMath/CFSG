module

public import CFSG.Quasithin.H13.NQS134YC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134YB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1343
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S13473N

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits CFSG.Quasithin.H13.U3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem stmt13473NonSolv_of_F4 (hC137 : U3.C137StatementFiveZ_F4)
    (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1345 : Stmt13_4_5_F4) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big) :
    U3.Stmt13473NonSolv_F4 := by
  intro G _ _ T L V S H₁ H₂ Y₂ Y he h hK₂L hiii hH₀ hH₀M hY₂H hY₂N hY₂ hfpf hmoves hZV₀ hY₂T
    h3 hq hY₂M hY hinf htr hYH hYM hred hcent hJL1 hJ hnot hns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁def

  obtain ⟨⟨K, hK⟩, hall⟩ := h1345 G T L V S Y hYH hYM hns
  obtain ⟨⟨-, hKf⟩, hN, hcases, hKM, -, hKZV, -, ⟨W, hW⟩, hWall⟩ := hall K hK
  obtain ⟨hTW, hfsu, hWcl, ⟨hab, hmod⟩, ho2Z, hcentR⟩ := hWall W hW
  have hKY := le_of_mem_cComp hK

  have hnhat := not_hat_of_cent hred hcent hKY hcentR
  have hcases' : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) := by
    rcases hcases with h5 | h32 | h6 | hhat
    · exact Or.inl h5
    · exact Or.inr (Or.inl h32)
    · exact Or.inr (Or.inr h6)
    · exact absurd hhat hnhat

  obtain ⟨hnot5, hKi⟩ := f618_K hF hBig S htr hYH hK hN hcases'
  have hKtype : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) :=
    hcases'.resolve_left hnot5
  obtain ⟨hL13, hL1O, hL1q⟩ := s134_L1T_a6 S he
  have hL1Y : L₁ ⊔ T ≤ Y := hY ▸ le_sup_left
  have hY2Y : Y₂ ⊔ T ≤ Y := hY ▸ le_sup_right
  have hL1K : L₁ ≤ K := by
    have h1 := hKi hL1Y le_sup_right (s1347_relIndex_three S le_sup_right hL1q)
    refine le_trans ?_ h1
    refine (closure_le _).2 fun x hx => subset_closure ⟨mem_sup_left (subset_closure hx), hx.2⟩
  have hY2K : Y₂ ≤ K := by
    have h1 := hKi hY2Y le_sup_right h3
    rw [← hY₂]
    exact (oTwoRes_mono' le_sup_left).trans h1

  obtain ⟨y, hyY₂, hyC⟩ := hmoves
  have hcZ : U3.cZ T K = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxZ, hxK⟩ := hx
    rw [mem_bot]
    refine hfpf y hyY₂ hyC x (hZV₀ hxZ) ?_
    rw [mem_centralizer_iff.1 hxK y (hY2K hyY₂), mul_inv_cancel_right]

  have hTK : T ≤ normalizer (K : Set G) := hYH.1.trans hN
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  obtain ⟨hs, -⟩ := U3.simple_of_cases hcases'
  have hKJ : ⁅K, thompsonJ T⁆ = K := by
    have hle : ⁅K, thompsonJ T⁆ ≤ K := by
      rw [commutator_le]
      intro k hk j hj
      have h1 : j * k⁻¹ * j⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK (hJT hj)) _).mp (inv_mem hk)
      rw [commutatorElement_def, show k * j * k⁻¹ * j⁻¹ = k * (j * k⁻¹ * j⁻¹) by group]
      exact mul_mem hk h1
    have hKN : K ≤ normalizer ((⁅K, thompsonJ T⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_left' K (thompsonJ T)
    have : (⁅K, thompsonJ T⁆.subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).2 hKN
    have hnotle : ¬ ⁅K, thompsonJ T⁆.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      intro hle'
      have hL1O' : L₁ ≤ pCoreOf 2 K := by
        intro l hl
        have hl1 : l ∈ ⁅K, thompsonJ T⁆ := by
          rw [← hJL1] at hl
          exact commutator_mono hL1K le_rfl hl
        have hl2 := hle' (mem_subgroupOf.2 (show ((⟨l, hL1K hl⟩ : ↥K) : G) ∈ _ from hl1))
        rw [← U3.pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at hl2
        exact hl2
      have hL1T : L₁ ≤ L₁ ⊓ T := le_inf le_rfl
        (hL1O'.trans (pCoreOf_two_le_of_isSylowTwoOf (A4.isSylowTwoOf_inf_normal
          (A5.isSylowTwoOf_of_le S.h13.sylow hYH.1) hKY hN)) |>.trans inf_le_left)
      have h1 : (L₁Of L (fsuV1 T V) ⊓ T).relIndex (L₁Of L (fsuV1 T V)) = 1 :=
        relIndex_eq_one.2 hL1T
      omega
    have htop := eq_top_of_not_le_pCore' hperf hs hnotle
    refine le_antisymm hle fun k hk => ?_
    have hk' : (⟨k, hk⟩ : ↥K) ∈ ⁅K, thompsonJ T⁆.subgroupOf K := by rw [htop]; trivial
    exact mem_subgroupOf.1 hk'

  have hZ2 : 2 < Nat.card ↥(quasithinOmegaOneCenter T) := by
    have h1 := U3.s134_card_Z_F4 h1332 hC58 h317 h56 S ⟨Y, hYH, hYM⟩
    have hzV : S.zV ∈ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) :=
      mem_inf.2 ⟨U3.s134_zV_mem_Z S, (S.mem_ZV_iff.2 (Or.inr rfl)).2⟩
    have h2 : 1 < Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)) := by
      rw [one_lt_card_iff_ne_bot]
      intro hb
      rw [hb, mem_bot] at hzV
      exact S.zV_ne_one hzV
    omega

  have D : KWData S K W := ⟨hKf, hTK, hKM, hKZV, hKJ, hcases, hW, hTW, hfsu, hWcl, hmod, ho2Z⟩
  exact D.false_of_cZ_eq_bot_F4 hC137 h1332 h1228 h56 he hL1K hKtype hcZ hZ2

end CFSG.Quasithin.H13.NQS134
