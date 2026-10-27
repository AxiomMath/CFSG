module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Bound

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped IsMulCommutative

theorem delta_false (h309 : KD309) {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {x z : G}
    {T : Subgroup G} (hpl : Plane63 5 G P x z)
    (hC2 : centralizer ((CFSG.pCore 2 G : Subgroup G) : Set G) ≤ CFSG.pCore 2 G)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (primeComplementCore (G := G) 5))
    (hR32 : Nat.card (Rsub T z x) ≤ 32) (hsq : ∃ r ∈ Rsub T z x, r ^ 2 ≠ 1)
    {L : Subgroup (G ⧸ primeComplementCore (G := G) 5)} (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup (G ⧸ primeComplementCore (G := G) 5), IsComponentOf K ⊤ → K = L)
    (h29 : Is29a ↥L) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Q : Subgroup G := CFSG.pCore 2 G with hQdef
  haveI hQn : Q.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ2⟩
  have hQD : Q ≤ primeComplementCore (G := G) 5 := by
    refine normal_coprime_le_primeComplementCore 5 Q hQn ?_
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes (by norm_num) (by norm_num)).2 (by norm_num))
  have hQT : Q ≤ T := by
    have hsup : IsPGroup 2 ↥(T ⊔ Q) := IsPGroup.to_sup_of_normal_right hT.isPGroup hQ2
    have := hT.eq_of_le (le_sup_left : T ≤ T ⊔ Q) (sup_le hT.le hQD) hsup
    rw [← this]
    exact le_sup_right
  have h1 := h309 G P x z hpl L hL hLu h29 (FV Q) (rep Q) (isPGroup_ker_rep Q hC2)
  have h2 := finrank_range_le_twenty Q hpl.plane hpl.z_central hpl.four_le hQT hR32 hsq
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
