module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveNT
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolve21
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits

public section

namespace CFSG.AGLEmbedding

open CFSG.Open KFactProofs.SmallIdent

theorem involve_of_sylowSq {K L : Type} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hK : SylowSq p K) (T : Sylow p K) (TL : Sylow p L)
    (hTL : ¬ IsCyclic (TL : Subgroup L)) (hdvd : Nat.card L ∣ Nat.card K) :
    Nat.card TL = Nat.card T := by
  have : Fact p.Prime := ⟨hp⟩
  have hTK : (Nat.card K).factorization p = 2 := by
    have h := T.card_eq_multiplicity
    rw [hK T] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  obtain ⟨a, ha⟩ := (TL.2 : IsPGroup p (TL : Subgroup L)).exists_card_eq
  have ha_dvd : p ^ a ∣ Nat.card K := by
    rw [← ha]
    exact (Subgroup.card_subgroup_dvd_card _).trans hdvd
  have hle : a ≤ 2 := by
    have := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ha_dvd
    omega
  have hd : Nat.card TL ∣ p ^ 2 := by
    rw [ha]
    exact pow_dvd_pow p hle
  rw [card_eq_sq_of_noncyclic hp (TL : Subgroup L) hTL hd, hK T]

theorem involve_of_sylowCube {K L : Type} [Group K] [Group L] {p : ℕ} (hK : SylowCube p K)
    (hL : SylowCube p L) (T : Sylow p K) (TL : Sylow p L) : Nat.card TL = Nat.card T := by
  rw [(hL TL).1, (hK T).1]

theorem involve_of_isSmallUnitary
    {K L : Type} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hsL : IsSimpleGroup L) (hK : IsSmallUnitary p K) (hL : IsSmallStrongP p L)
    (T : Sylow p K) (TL : Sylow p L) (hdvd : Nat.card L ∣ Nat.card K) :
    Nat.card TL = Nat.card T := by
  have hg := card_mul_gcd_of_isSmallUnitary hK
  have hKdvd : Nat.card K ∣ p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) := Dvd.intro _ hg
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKle : Nat.card K ≤ p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) := Nat.le_of_dvd (by
    have : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    positivity) hKdvd
  have hKcube := sylowCube_of_isSmallUnitary hp hp2 hK
  rcases hL with hL2 | hLU | hLA | ⟨h3, hL34 | hLM⟩ | ⟨h5, hLT | hLMcL | hLFi⟩ | ⟨h11, hLJ⟩
  · exfalso
    rw [card_of_isSmallLinTwo hp hp2 hL2] at hdvd
    exact linTwo_not_dvd_unitaryOrder hp3 hodd (hdvd.trans hKdvd)
  · exact involve_of_sylowCube hKcube (sylowCube_of_isSmallUnitary hp hp2 hLU) T TL
  · exfalso
    rw [card_of_isAltTwoP hp hLA] at hdvd
    have hp' : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    rcases hp' with rfl | h5 | h7
    · norm_num [Nat.factorial] at hdvd hg
      omega
    · have := Nat.le_of_dvd hKpos hdvd
      have h2 := lt_factorial_two_mul (p := p) (Or.inl h5)
      omega
    · have := Nat.le_of_dvd hKpos hdvd
      have h2 := lt_factorial_two_mul (p := p) (Or.inr h7)
      omega
  · exfalso
    subst h3
    norm_num at hg
    rw [card_of_isLinThreeFour hL34] at hdvd
    omega
  · exfalso
    subst h3
    norm_num at hg
    rw [card_of_isM11 hLM] at hdvd
    omega
  · exfalso
    subst h5
    norm_num at hg
    rw [card_of_isTitsGroup hLT] at hdvd
    omega
  · subst h5
    exact involve_of_sylowCube hKcube (sylowCube_of_isMcL hsL hLMcL) T TL
  · exfalso
    subst h5
    norm_num at hg
    rw [card_of_isFi22 hsL hLFi] at hdvd
    omega
  · subst h11
    exact involve_of_sylowCube hKcube (sylowCube_of_isJ4 hsL hLJ) T TL

theorem involve_of_isMcL
    {K L : Type} [Group K] [Finite K] [Group L] [Finite L] (hs : IsSimpleGroup K)
    (hsL : IsSimpleGroup L) (hK : IsSporadicGroup .McL K) (hL : IsSmallStrongP 5 L)
    (T : Sylow 5 K) (TL : Sylow 5 L) (A : Subgroup K) (f : A →* L)
    (hf : Function.Surjective f) (hdvd : Nat.card L ∣ Nat.card K) : Nat.card TL = Nat.card T := by
  have hKcard := card_of_isMcL hs hK
  have hKcube := sylowCube_of_isMcL hs hK
  rcases hL with hL2 | hLU | hLA | ⟨h3, -⟩ | ⟨-, hLT | hLMcL | hLFi⟩ | ⟨h11, -⟩
  · exfalso
    rw [card_of_isSmallLinTwo (by norm_num) (by norm_num) hL2, hKcard] at hdvd
    omega
  · exact involve_of_sylowCube hKcube (sylowCube_of_isSmallUnitary (by norm_num) (by norm_num) hLU)
      T TL
  · exfalso
    obtain ⟨g, hg⟩ := exists_orderOf_twenty_one_of_isAltTwoP_five hLA
    obtain ⟨x, hx⟩ := exists_orderOf_eq_of_surjective A f hf g
    exact not_orderOf_twenty_one_of_isMcL hs hK x (hx.trans hg)
  · omega
  · exfalso
    rw [card_of_isTitsGroup hLT, hKcard] at hdvd
    omega
  · exact involve_of_sylowCube hKcube (sylowCube_of_isMcL hsL hLMcL) T TL
  · exfalso
    rw [card_of_isFi22 hsL hLFi, hKcard] at hdvd
    omega
  · omega

theorem involve_of_isJ4
    {K L : Type} [Group K] [Finite K] [Group L] [Finite L] (hs : IsSimpleGroup K)
    (hsL : IsSimpleGroup L) (hK : IsSporadicGroup .J4 K) (hL : IsSmallStrongP 11 L)
    (T : Sylow 11 K) (TL : Sylow 11 L) (hdvd : Nat.card L ∣ Nat.card K) :
    Nat.card TL = Nat.card T := by
  have hKcard := card_of_isJ4 hs hK
  have hKcube := sylowCube_of_isJ4 hs hK
  rcases hL with hL2 | hLU | hLA | ⟨h3, -⟩ | ⟨h5, -⟩ | ⟨-, hLJ⟩
  · exfalso
    rw [card_of_isSmallLinTwo (by norm_num) (by norm_num) hL2, hKcard] at hdvd
    omega
  · exact involve_of_sylowCube hKcube (sylowCube_of_isSmallUnitary (by norm_num) (by norm_num) hLU)
      T TL
  · exfalso
    rw [card_of_isAltTwoP (by norm_num) hLA, hKcard] at hdvd
    norm_num [Nat.factorial] at hdvd
  · omega
  · omega
  · exact involve_of_sylowCube hKcube (sylowCube_of_isJ4 hsL hLJ) T TL

theorem kFactSmallInvolveCard_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallInvolveCard := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut L _ _ hsL hnabL hcL TL hTL hΓL hAutL A f hf
  have hK := isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut
  have hL := isSmallStrongP_of_autRank h hsL hnabL hcL hp hp2 TL hTL hΓL hAutL
  have hdvd : Nat.card L ∣ Nat.card K :=
    (Subgroup.card_dvd_of_surjective (f := f) hf).trans (Subgroup.card_subgroup_dvd_card A)
  rcases hK with hK2 | hKU | hKA | ⟨rfl, hKL34 | hKM⟩ | ⟨rfl, hKT | hKMcL | hKFi⟩ | ⟨rfl, hKJ⟩
  · exact involve_of_sylowSq hp (sylowSq_of_isSmallLinTwo hp hp2 hK2) T TL hTL hdvd
  · exact involve_of_isSmallUnitary hp hp2 hsL hKU hL T TL hdvd
  · exact involve_of_sylowSq hp (sylowSq_of_isAltTwoP hp hp2 hKA) T TL hTL hdvd
  · exact involve_of_sylowSq hp (sylowSq_of_isLinThreeFour hKL34) T TL hTL hdvd
  · exact involve_of_sylowSq hp (sylowSq_of_isM11 hKM) T TL hTL hdvd
  · exact involve_of_sylowSq hp (sylowSq_of_isTitsGroup hKT) T TL hTL hdvd
  · exact involve_of_isMcL hs hsL hKMcL hL T TL A f hf hdvd
  · exact involve_of_sylowSq hp (sylowSq_of_isFi22 hs hKFi) T TL hTL hdvd
  · exact involve_of_isJ4 hs hsL hKJ hL T TL hdvd

end CFSG.AGLEmbedding
