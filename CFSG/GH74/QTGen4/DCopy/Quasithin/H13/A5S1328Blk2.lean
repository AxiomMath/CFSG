module

public import CFSG.Quasithin.H13.A5S1328Blk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1328Blk2S331

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isA5Block_or_isA5Block_F4 (h331 : Stmt3_3_1_F4) (h512 : Stmt5_1_2_F4)
    (h5172 : Stmt5_1_7_two_F4) (h126 : TheoremC126) {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hHK : H = K ⊔ T)
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    (IsBlock2 (K ⊔ T) K ∧ IsAltType K 5) ∨ (IsBlock2 (L ⊔ T) L ∧ IsAltType L 5) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  have hT0 : T ≠ ⊥ := by
    intro h
    exact S.z_ne_one (Subgroup.mem_bot.mp (h.le (S.V_le_T S.z_mem_V)))
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, -, -⟩ := hC.pair T S.isPGroup_T hT0

  have hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ (by rw [Setting.UH, hHK]; exact hJ)
  have hZz : ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = S.z :=
    fun x hx => S.mem_omegaOneCenter_of_F4 h512 S' hJK hZK hx

  have hzC₁ : S.z ∈ C₁ T := by
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := C₁ T)).1 h1ne
    rcases hZz c (h1Z c.2) with h | h
    · exact absurd (Subtype.ext h) hc1
    · rw [← h]; exact c.2

  have hC₂2 : IsPGroup 2 ↥(C₂ T) := S.isPGroup_T.to_le (h2B.trans (C1GN.baum_le T))

  have hHH : InH T H := hH.1
  have hmpH : MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) :=
    (S.hyp501.minParabolic_of_isHStar_F4 h331 hH).1
  have hH1 : (H ≤ Subgroup.normalizer (C₂ T : Set G)) ∨ (IsBlock2 (K ⊔ T) K ∧ IsAltType K 5) := by
    rcases c126_of_minParabolic (h126 G C₁ C₂ hC) (S.charTwo_of_inH hHH)
        (isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hHH) hmpH with
      h1 | h2 | ⟨B, hB⟩
    · exfalso
      apply hHZ
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hZz x hx with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_iff.mp (h1 hh) _ hzC₁)
    · exact Or.inl h2
    · right
      rw [hHK] at hB
      obtain ⟨hblk, htype⟩ := hB
      have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨e⟩ := (quasithinO2QuotientIso_iff K _).1 S'.a5
      have hBK : B = K := eq_of_isBlock2 le_sup_left (sup_le Subgroup.le_normalizer S'.T_le_NL)
        (fun _ hx => C1.exists_pow_mem_of_mem_sup S.isPGroup_T S'.T_le_NL hx)
        S'.h13.faithful.2.1 e.isSimpleGroup hblk
      subst hBK
      rcases htype with ⟨n, -, hlin⟩ | h3 | h5
      · exact (S'.not_isLin2Type hblk.1 hlin).elim
      · exact absurd (S'.eq_five_of_isAltType le_rfl h3) (by norm_num)
      · exact ⟨hblk, h5⟩

  have hL1 : (L ⊔ T ≤ Subgroup.normalizer (C₂ T : Set G)) ∨
      (IsBlock2 (L ⊔ T) L ∧ IsAltType L 5) := by
    rcases S.c126_LT (h126 G C₁ C₂ hC) with h1 | h2 | h3
    · exfalso
      have hzC : S.z ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_sup_left hl)) _ hzC₁).symm
      have hzL : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hzC⟩
      rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzL
      exact S.z_ne_one hzL
    · exact Or.inl h2
    · exact Or.inr h3

  rcases hH1 with hHN | hK
  · rcases hL1 with hLN | hLb
    · exfalso
      have hloc : IsTwoLocal (Subgroup.normalizer (C₂ T : Set G)) := ⟨C₂ T, h2ne, hC₂2, rfl⟩
      obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
      have hM'eq : M' = Subgroup.normalizer (L : Set G) := S.uniqueM.2 M' ⟨hM', hLN.trans hle⟩
      exact hH.2.1 (hM'eq ▸ hHN.trans hle)
    · exact Or.inr hLb
  · exact Or.inl hK

theorem pCoreOf_KT_eq_F4 (h331 : Stmt3_3_1_F4) (h512 : Stmt5_1_2_F4)
    (h5172 : Stmt5_1_7_two_F4) (h126 : TheoremC126) {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hHK : H = K ⊔ T)
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    pCoreOf 2 (K ⊔ T) = VH := by
  have hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G) := fun hJ =>
    S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ (by rw [Setting.UH, hHK]; exact hJ)
  have hZz : ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = S.z :=
    fun x hx => S.mem_omegaOneCenter_of_F4 h512 S' hJK hZK hx
  rcases S.isA5Block_or_isA5Block_F4 h331 h512 h5172 h126 S' hH hHZ hHK hZK with
    ⟨hblk, h5⟩ | ⟨hblk, h5⟩
  ·
    have hCTK := inf_centralizer_eq_bot_of S.isPGroup_T S'.T_le_NL hZK
    exact le_antisymm (S'.pCoreOf_LT_le_V hblk h5 hCTK) S'.V_le_pCoreOf_LT
  ·
    have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxZ, hxL⟩
      rw [Subgroup.mem_bot]
      rcases hZz x hxZ with h | rfl
      · exact h
      · have hzb : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hxL⟩
        rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzb
        exact hzb
    have hCTL := inf_centralizer_eq_bot_of S.isPGroup_T S.T_le_NL hZL
    have hO : pCoreOf 2 (L ⊔ T) = V :=
      le_antisymm (S.pCoreOf_LT_le_V hblk h5 hCTL) S.V_le_pCoreOf_LT
    obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
      S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer_F4 h5172 hH hHZ)
    have hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1 :=
      ⟨j, thompsonJ_le_self T hjJ, by
        rw [show (⟨j, S.frame.T_le (thompsonJ_le_self T hjJ)⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = ⟨j, hjN⟩ from rfl, hj]
        decide⟩
    have hcardT : Nat.card ↥T = 128 := by
      rw [S.card_T_eq hodd, hO, S.card_V]

    have hUV : S.UH H ≤ VH := by
      unfold Setting.UH
      rw [hHK]
      refine conjClosure_le fun h hh x hx => ?_
      have hxV : x ∈ VH := by
        rcases hZz x hx with rfl | rfl
        · exact Subgroup.one_mem _
        · rw [S.z_eq_of_F4 h512 S' hJK hZK]
          exact S'.z_mem_V
      have hhN : h ∈ Subgroup.normalizer (VH : Set G) :=
        (sup_le S'.frame.L_le S'.frame.T_le) hh
      exact (Subgroup.mem_normalizer_iff.mp hhN x).mp hxV
    have hJVH : ¬ thompsonJ T ≤ Subgroup.centralizer (VH : Set G) := fun hJ =>
      S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ
        (hJ.trans (Subgroup.centralizer_le hUV))
    obtain ⟨⟨j', hjJ', hjN', hj'⟩, -⟩ := S'.lemma_13_2_4_two_b hJVH
    have hodd' : ∃ (t : G) (ht : t ∈ T), (S'.frame.ρ ⟨t, S'.frame.T_le ht⟩).sign ≠ 1 :=
      ⟨j', thompsonJ_le_self T hjJ', by
        rw [show (⟨j', S'.frame.T_le (thompsonJ_le_self T hjJ')⟩ :
          ↥(Subgroup.normalizer (VH : Set G))) = ⟨j', hjN'⟩ from rfl, hj']
        decide⟩
    have hcard : Nat.card ↥(pCoreOf 2 (K ⊔ T)) = 16 := by
      have := S'.card_T_eq hodd'
      omega
    exact (Subgroup.eq_of_le_of_card_ge S'.V_le_pCoreOf_LT (by rw [hcard, S'.card_V])).symm

end Setting

end CFSG.Quasithin.H13.A5
