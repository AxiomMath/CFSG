module

public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem false_of_s3_ch615_F4 (h432 : Stmt4_3_2_F4) (hDSB : DSBLoc_F4) (c : Cx615B G T M L V H n)
    {S P₁ : Subgroup G} (hST : S ≤ T) (hTLS : T ⊓ L ≤ S)
    (hSP : S ≤ Subgroup.normalizer (P₁ : Set G))
    (hBP : borelL T L ≤ Subgroup.normalizer (P₁ : Set G)) (hP₁M : ¬ P₁ ≤ M)
    (hsyl : IsSylowTwoOf (S ⊓ P₁) P₁) (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)))
    (hc1 : CharTwo (L ⊔ S)) (hc2 : CharTwo (P₁ ⊔ S ⊔ borelL T L)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.hyp
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hSL : S ⊓ L = T ⊓ L := le_antisymm (inf_le_inf_right L hST) (le_inf hTLS inf_le_right)
  have hbP : borelOf P₁ S = S ⊓ P₁ := borelOf_eq_of_s3 hsyl hS3
  have hbL : borelOf L S = borelL T L := by
    unfold borelOf borelL
    rw [hSL]
  have hn2 := h.two_le
  have hlist : IsRankOneListed (oTwoQuot ↥L) := Or.inl ⟨n, by omega, c.isL2Quot_ch615⟩
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le hST
  have hyp : Hyp111 L P₁ S := by
    refine ⟨⟨inferInstance, hS2, hST.trans hTL, ?_, hlist, ?_, ?_⟩,
      ⟨inferInstance, hS2, hSP, hsyl, ?_, ?_, ?_⟩, ?_⟩
    · rw [hSL]
      exact c.toCx615.isSylowTwoOf_inf
    · rw [hbP]
      exact inf_le_left.trans (hST.trans hTL)
    · rw [hbP, sup_of_le_left ((inf_le_left : S ⊓ P₁ ≤ S).trans le_sup_right)]
      exact hc1
    · obtain ⟨e⟩ := hS3
      exact isRankOneListed_perm_three e
    · rw [hbL]
      exact hBP
    · rw [hbL]
      exact hc2
    ·
      by_contra hne
      have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ P₁ ⊔ S) : Set G)) :=
        ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
      obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
      have hG0 : L ⊔ P₁ ⊔ S ≤ K :=
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hle
      have hKM : K = M := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
        h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1 K hK
          (le_sup_left.trans (le_sup_left.trans hG0))
      exact hP₁M (hKM ▸ (le_sup_right.trans (le_sup_left.trans hG0)))
  have hqt : IsQuasithinSub (L ⊔ P₁ ⊔ S) := isQuasithinSub_of_qtke' h.qtke _
  have hnorm : (S.subgroupOf (S ⊔ borelOf L S)).Normal ∨
      (S.subgroupOf (S ⊔ borelOf P₁ S)).Normal := by
    right
    rw [hbP, sup_of_le_left inf_le_left, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hnsolv : ¬ Group.IsSolvable ↥L := fun hs => by
    have h1 := (isSolvable_iff_perfectCore_eq_bot L).mp hs
    rw [perfectCore_eq_self_of_perfect h.toHyp5_0_1.commutator_eq] at h1
    apply h.module.2.2
    rw [h1]
    exact Subgroup.commutator_bot_right V
  obtain ⟨L1', L2', hsw, -, hlist'⟩ := dsBLoc_orient_of_F4 hDSB G L P₁ S hyp hqt hnorm hnsolv hS3
  have hcL := c.card_oTwoQuot_ch615
  have hcP := card_oTwoQuot_of_s3 hS3
  have h60 : 60 ≤ 2 ^ n * (4 ^ n - 1) := two_pow_mul_four_pow_sub_one_ge n hn2
  have h504 : 3 ≤ n → 504 ≤ 2 ^ n * (4 ^ n - 1) := fun hn3 => by
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h64 : 4 ^ 3 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    calc 504 = 2 ^ 3 * (4 ^ 3 - 1) := by norm_num
      _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h8 (by omega)
  unfold F112ListBLoc F112B4Loc F112B6Loc F112B10Loc F112B11Loc at hlist'
  rcases hlist' with ⟨hq1, hsp, -⟩ | ⟨hq1, -, -, hq2, -, hA5⟩ | ⟨hq1, hQ, -⟩ |
      ⟨-, hQ, ⟨e2⟩, -⟩
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have hn3 : 3 ≤ n := by
        by_contra hlt
        have hn : n = 2 := by omega
        rw [hcL, hn] at hq
        norm_num at hq
      exact c.not_isSpecialPow_ch615 hn3 hsp
    · rw [hcP] at hq
      norm_num at hq
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · rw [hcL] at hq
      norm_num at hq
      omega
    · have hq' := hq2.card (by norm_num)
      rw [hcL] at hq'
      have hn : n = 2 := by
        by_contra hne
        have := h504 (by omega)
        norm_num at hq'
        omega
      exact c.false_of_isAltType_ch615 hn hA5
  ·
    have hq := hq1.card (by norm_num)
    rcases hsw with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact c.not_isQ8D8_ch615 hQ
    · rw [hcP] at hq
      norm_num at hq
  ·
    have h6 := card_oTwoQuot_of_s3 ⟨e2⟩
    rcases hsw with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact c.not_isQ8D8_ch615 hQ
    · rw [hcL] at h6
      omega

end Cx615B

end CFSG.Quasithin.H13
