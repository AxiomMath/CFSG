module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.EndgameHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ExtremalNotInM0
public import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.exists_THyp (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {Q : Subgroup G}
    (hQ : QHyp L A D t Q) : ∃ T : Subgroup G, THyp S D Q t T := by
  have hQN : Q ≤ normalizer (D : Set G) :=
    hQ.le_centralizer.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hSN : S ≤ normalizer (D : Set G) := H.S_le_normalizer_D W W2 hD
  have htN : t ∈ normalizer (D : Set G) :=
    le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)
  have hSN' : S ≤ L ⊓ normalizer (A : Set G) := by
    have h : S ≤ L ⊓ normalizer (D : Set G) := le_inf W.S_le hSN
    rwa [H.inf_normalizer_D_eq W W2 hD] at h
  have hS_le_NQ : S ≤ normalizer (Q : Set G) :=
    Subgroup.le_normalizer_iff.2 fun s hs q hq => hQ.conj_mem s (hSN' hs) q hq
  have hQSp : IsPGroup 2 (Q ⊔ S : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQ.pgroup W.pgroup hS_le_NQ
  have htQ : t ∈ normalizer (Q : Set G) := by
    have ht2 : t * t = 1 := by simpa [sq] using H.sq_t
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    refine mem_normalizer_iff.2 fun q => ⟨hQ.conj_t_mem q, fun hq => ?_⟩
    have h := hQ.conj_t_mem (t * q * t⁻¹) hq
    have e : t * (t * q * t⁻¹) * t⁻¹ = q := by
      rw [htinv]
      calc t * (t * q * t) * t = (t * t) * q * (t * t) := by group
        _ = q := by rw [ht2, one_mul, mul_one]
    rwa [e] at h
  have hzS : zpowers t ≤ centralizer (S : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun s hs => (H.comm_of_mem_L (W.S_le hs)).symm
  have hzNS : zpowers t ≤ normalizer (S : Set G) :=
    hzS.trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hzNQS : zpowers t ≤ normalizer ((Q ⊔ S : Subgroup G) : Set G) :=
    (le_inf (Subgroup.zpowers_le.2 htQ) hzNS).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Q S)
  have hZtP : IsPGroup 2 (zpowers t : Subgroup G) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, H.order_two]; norm_num)
  have hKp : IsPGroup 2 ((Q ⊔ S) ⊔ zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQSp hZtP hzNQS
  let N : Subgroup G := normalizer (D : Set G)
  let K : Subgroup G := (Q ⊔ S) ⊔ zpowers t
  have hKN : K ≤ N :=
    sup_le (sup_le hQN hSN) (Subgroup.zpowers_le.2 htN)
  have hK'p : IsPGroup 2 (K.subgroupOf N) := hKp.comap_subtype
  obtain ⟨P, hPK⟩ := hK'p.exists_le_sylow
  have hKleT : K ≤ (P : Subgroup N).map N.subtype := by
    have h := map_mono (f := N.subtype) hPK
    rwa [Subgroup.map_subgroupOf_eq_of_le hKN] at h
  have hQK : Q ≤ K := (le_sup_left : Q ≤ Q ⊔ S).trans (le_sup_left : Q ⊔ S ≤ K)
  have hSK : S ≤ K := (le_sup_right : S ≤ Q ⊔ S).trans (le_sup_left : Q ⊔ S ≤ K)
  have hzK : zpowers t ≤ K := le_sup_right
  refine ⟨(P : Subgroup N).map N.subtype, P.isPGroup'.map N.subtype,
    Subgroup.map_subtype_le (P : Subgroup N), ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hKleT (hQK hq)
  · intro s hs
    exact hKleT (hSK hs)
  · exact hKleT (hzK (mem_zpowers t))
  · intro Y hYN hYp hTY
    have hY'p : IsPGroup 2 (Y.subgroupOf N) := hYp.comap_subtype
    have hPY' : (P : Subgroup N) ≤ Y.subgroupOf N := fun p hp =>
      hTY (Subgroup.mem_map_of_mem N.subtype hp)
    have heq : Y.subgroupOf N = P := P.is_maximal' hY'p hPY'
    intro y hy
    have hy' : (⟨y, hYN hy⟩ : N) ∈ Y.subgroupOf N := hy
    rw [heq] at hy'
    exact Subgroup.mem_map_of_mem N.subtype hy'

theorem ThCyc.exists_mem_normalizer_not_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q T : Subgroup G}
    (hT : THyp S D Q t T) : ∃ g ∈ normalizer (T : Set G), g ∉ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  have hsub : normalizer (T : Set G) ≤ normalizer (D : Set G) := by
    intro g hg
    by_contra hgD
    exact h ⟨g, hg, hgD⟩
  obtain ⟨P, hTP⟩ := hT.pgroup.exists_le_sylow
  by_cases hTPeq : T = P
  · have hTidx : ¬ 2 ∣ T.index := by
      rw [hTPeq]
      exact P.not_dvd_index
    exact H.false_of_sylow_le_normalizer_D W W2 hD F h4 hb hT.pgroup hTidx
      (sup_le hT.S_le (Subgroup.zpowers_le.2 hT.t_mem)) hT.le_normalizer
  · have hlt : T < (P : Subgroup G) := lt_of_le_of_ne hTP hTPeq
    have hlt' : T < (P : Subgroup G) ⊓ normalizer (T : Set G) :=
      CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt (q := 2) P.isPGroup' hlt
    obtain ⟨g, hg, hgT⟩ := SetLike.exists_of_lt hlt'
    have hgP : g ∈ (P : Subgroup G) := hg.1
    have hgN : g ∈ normalizer (T : Set G) := hg.2
    have hgD : g ∈ normalizer (D : Set G) := hsub hgN
    have hgZp : IsPGroup 2 (zpowers g : Subgroup G) :=
      P.isPGroup'.to_le (Subgroup.zpowers_le.2 hgP)
    have hYp : IsPGroup 2 (T ⊔ zpowers g : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hT.pgroup hgZp (Subgroup.zpowers_le.2 hgN)
    have hYN : T ⊔ zpowers g ≤ normalizer (D : Set G) :=
      sup_le hT.le_normalizer (Subgroup.zpowers_le.2 hgD)
    have hle := hT.maximal (T ⊔ zpowers g) hYN hYp le_sup_left
    exact hgT (hle (mem_sup_right (mem_zpowers g)))

end CFSG.EvenSporadicStandard.ThStd
