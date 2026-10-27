module

public import CFSG.GH74.GLS.C3.Layer1.U1a
public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.GH74.GLS.C3.Layer1

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness

variable {G : Type} [Group G] [Finite G] {M L T Q : Subgroup G}

theorem exists_conj_inter_rank_two_normal
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    (hM : M ≠ ⊤) (hLM : L ≤ M) (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hT : IsSylowOf 2 T M) (hQT : Q ≤ T)
    (hQ2 : 2 ≤ CFSG.pRank 2 ↥Q) (hpre : gammaK 2 Q 1 ≤ M) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) :=
  U1a.exists_conj_inter_rank_two_normal_of_corZD S_CorZD_unconditional hG hnon hM hLM hLnorm hLs hLn
    hQ hT hQT hQ2 hpre

theorem exists_conj_inter_rank_two_normal_of_preuniq
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    (hM : M ≠ ⊤) (hLM : L ≤ M) (hLnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a)
    (hQ : IsSylowOf 2 Q (CMK M L)) (hQ2 : 2 ≤ CFSG.pRank 2 ↥Q)
    (hpre : ∀ y ∈ CMK M L, orderOf y = 2 → centralizer ({y} : Set G) ≤ M) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) :=
  U1a.exists_conj_inter_rank_two_normal_of_preuniq S_CorZD_unconditional hG hnon hM hLM hLnorm hLs
    hLn hQ hQ2 hpre

theorem exists_conj_inter_of_hyp9A
    (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    {x : G} {K : Subgroup G} (h : Hyp9A x K L M T Q)
    (hLs : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L))
    (hLn : ∃ a b : ↥L ⧸ pPrimeCore 2 ↥L, a * b ≠ b * a) :
    ∃ g : G, g ∉ M ∧ 2 ≤ CFSG.pRank 2 ↥(CFSG.conjugate Q g ⊓ M) :=
  exists_conj_inter_rank_two_normal_of_preuniq hG hnon h.maximal.ne_top h.L_normal.1
    h.L_normal.2 hLs hLn h.sylowQ h.rankQ
    (U1a.centralizer_le_of_gammaK h.sylowQ h.gamma)

end CFSG.GH74.GLS.C3.Layer1
